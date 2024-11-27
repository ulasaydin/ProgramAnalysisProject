import argparse
import dis
import importlib.util
import subprocess
from datetime import datetime
import ast
import os
import sys

sys.path.append(os.path.dirname(__file__))

from invariant_inserter import insert_invariants_in_ast
from daikon_to_nagini_parser import parse_all_daikon_invariants
from instrumenter import Instrumenter
from util import remove_nagini_annotations
from config import APP_AUTHOR, APP_NAME
from platformdirs import user_data_dir
from concolic_test_case_generator import ConcolicTestCaseGenerator
from util import write_to_file, extract_functions, function_ast_to_bytecode

def find_invariants(program_file_path: str, entry_point_function: str, output_dir: str):
    print(f"Finding invariants for {entry_point_function} in {program_file_path}:")
    print(f"Writing results to {output_dir}")

    program_file_path = os.path.abspath(program_file_path)

    with open(program_file_path) as program_file:
        program_root = ast.parse(program_file.read(), program_file_path)

    functions: dict[str, tuple[ast.FunctionDef, dis.Bytecode]] = {}

    for function_name, function_ast in extract_functions(program_root, program_file_path).items():
        function_without_annotations = remove_nagini_annotations(function_ast)
        functions[function_name] = (function_without_annotations, function_ast_to_bytecode(function_without_annotations))

    if entry_point_function not in functions:
        raise RuntimeError(f"Entry point method { entry_point_function} not found in program")

    for function_name, (function_ast, function_bytecode) in functions.items():
        write_to_file(os.path.join(output_dir, f"{function_name}_without_annotations.py"), ast.unparse(function_ast))
        write_to_file(os.path.join(output_dir, f"{function_name}_ast.txt"), ast.dump(function_ast, indent=4))
        write_to_file(os.path.join(output_dir, f"{function_name}_bytecode.txt"), function_bytecode.dis())
        write_to_file(os.path.join(output_dir, f"{function_name}_codeobj.txt"), "\n".join([f"{c}:{getattr(function_bytecode.codeobj, c)}" for c in dir(function_bytecode.codeobj)]))

    concolic_test_case_generator = ConcolicTestCaseGenerator(
        env = functions,
        entry_point=entry_point_function
    )
    concolic_test_cases = concolic_test_case_generator.generate_test_cases(max_branching_points=10)
    #concolic_test_case_generator.dot.render(os.path.join(output_dir, "concolic_tree"), format="pdf")
    """
    random_test_cases = RandomTestCaseGenerator(
        env={function_name: function_ast for function_name,
             (function_ast, _) in functions.items()},
        entry_point=entry_point_function
    ).generate_random_test_cases()
    """

    test_cases = concolic_test_cases

    write_to_file(os.path.join(output_dir, "concolic_test_cases.txt"), str("\n".join([str(tc) for tc in test_cases])))
    # print(f"Generated {len(random_test_cases)} random test cases for {entry_point_function}")
    # print(random_test_cases)

    # TODO: Translate more programs

    # Run instrumenter on program to get instrumented program
    instrumented_dir = os.path.join(output_dir, "instrumented")
    os.makedirs(instrumented_dir, exist_ok=True)
    instrumented_program = os.path.join(
        instrumented_dir, os.path.basename(program_file_path))
    print(f"Instrumenting {os.path.basename(program_file_path)}")
    Instrumenter().instrument_file(program_file_path, instrumented_program)

    # Output instrumented program to output directory
    spec = importlib.util.spec_from_file_location(
        "instrumented."+entry_point_function, instrumented_program)
    instrumented_fun = importlib.util.module_from_spec(spec)
    sys.modules["instrumented."+entry_point_function] = instrumented_fun

    # Run instrumented program on test cases
    # Output data traces to output directory
    dtrace_base_path = os.path.join(
        instrumented_dir, os.path.basename(program_file_path))
    dtraces = []
    fd = sys.stdout.fileno()
    print(f"Importing instrumented.{entry_point_function}")
    with os.fdopen(os.dup(fd), 'w') as old_stdout:
        for i, test_case in enumerate(test_cases):
            dtraces.append(dtrace_base_path+'_'+str(i)+".dtrace")
            with open(dtraces[-1], 'w', encoding='utf-8') as file:
                sys.stdout.close()  # + implicit flush()
                os.dup2(file.fileno(), fd)  # fd writes to 'to' file
                sys.stdout = os.fdopen(fd, 'w')  # Python writes to fd
            try:
                spec.loader.exec_module(instrumented_fun)
                method = getattr(instrumented_fun, entry_point_function)
                method(*test_case)
            finally:
                sys.stdout.close()  # + implicit flush()
                os.dup2(old_stdout.fileno(), fd)  # fd writes to 'to' file
                sys.stdout = os.fdopen(fd, 'w')  # Python writes to fd

    # Run Daikon on data traces to get invariants
    print(f"Running Daikon over {len(test_cases)} test cases.")
    daikon_result = subprocess.run(["java","-cp",os.path.join(os.path.dirname(__file__), "daikon.jar"),"daikon.Daikon","-o",dtrace_base_path, *dtraces], capture_output=True)

    if daikon_result.returncode != 0:
        write_to_file(os.path.join(output_dir, "daikon_error.txt"),
                      daikon_result.stderr.decode('utf-8'))
    daikon_output_path = os.path.join(output_dir, "daikon_output.txt")
    daikon_output_content = daikon_result.stdout.decode('utf-8')
    write_to_file(daikon_output_path, daikon_output_content)
    # TODO: (Jimena) Parse Daikon output and translate invariants to Nagini syntax
    print("Parsing Daikon output to Nagini...")
    nagini_invariants = parse_all_daikon_invariants(daikon_output_content)
    nagini_output_path = os.path.join(output_dir, "nagini_invariants.txt")
    with open(nagini_output_path, "w") as nagini_file:
        for invariant in nagini_invariants:
            nagini_file.write(f"{invariant}\n")
    print(f"invariants saved to {nagini_output_path}")

    # TODO: (Jimena) Insert invariant annotations in program ast

    output_program_path = os.path.join(output_dir, f"{os.path.basename( program_file_path).replace('.py', '_with_invariants.py')}")
    insert_invariants_in_ast(
        program_file_path, nagini_invariants, output_program_path)
    print(f"Invariants inserted into the AST in {output_program_path}");

    # TODO: Output program with invariants to output directory

    # TODO: (Ulas) Run Nagini on the annotated program to check invariants
    print("Running Nagini to verify the annotated program...")
    nagini_result = subprocess.run(["nagini", "--select", entry_point_function, output_program_path],capture_output=True,text=True)
    if nagini_result.returncode == 0:
       print("Nagini verification succeeded!")
       print("Output:")
       print(nagini_result.stdout)  
    else:
       print("Nagini verification failed.")
       print("Standard Output:")
       print(nagini_result.stdout)
       print("Error Output:")
       print(nagini_result.stderr) 
    
    print("---")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog="Loop Invariant Finder")
    parser.add_argument("program_file_path", help="Program file path")
    parser.add_argument("entry_point_function", help="Entry point function name")
    parser.add_argument("-o", "--output_dir", help="Output directory", required=False)
    args = parser.parse_args()

    program_file_path = args.program_file_path
    entry_point_function_name = args.entry_point_function

    if args.output_dir:
        output_dir = args.output_dir
    else:
        user_data_directory = user_data_dir(APP_NAME, APP_AUTHOR)
        output_dir_name = f"Invariants-{os.path.basename(program_file_path)}-{entry_point_function_name}-{datetime.now().strftime(f'%Y-%m-%d_%H-%M-%S')}"
        output_dir = os.path.join(user_data_directory, output_dir_name)
    find_invariants(program_file_path, entry_point_function_name, output_dir)
