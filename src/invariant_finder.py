import argparse
import dis
import importlib.util
from contextlib import contextmanager
import subprocess
from datetime import datetime
import ast
import os
import sys

sys.path.append(os.path.dirname(__file__))

from util import write_to_file, extract_functions, function_ast_to_bytecode
from concolic_test_case_generator import ConcolicTestCaseGenerator
from random_test_case_generator import RandomTestCaseGenerator
from platformdirs import user_data_dir
from config import APP_AUTHOR, APP_NAME
from util import remove_nagini_annotations
from instrumenter import Instrumenter


def find_invariants(program_file_path: str, entry_point_function: str, output_dir: str):
    print(f"Finding invariants for {entry_point_function} in {program_file_path}:")
    print(f"Writing results to {output_dir}")

    program_file_path = os.path.abspath(program_file_path)

    with open(program_file_path) as program_file:
        program_root = ast.parse(program_file.read(), program_file_path)

    functions: dict[str, (ast.FunctionDef, dis.Bytecode)] = {}

    for function_name, function_ast in extract_functions(program_root, program_file_path).items():
        function_without_annotations = remove_nagini_annotations(function_ast)
        functions[function_name] = (function_without_annotations, function_ast_to_bytecode(function_without_annotations))

    if entry_point_function not in functions:
        raise RuntimeError(f"Entry point method {entry_point_function} not found in program")

    for function_name, (function_ast, function_bytecode) in functions.items():
        write_to_file(os.path.join(output_dir, f"{function_name}_without_annotations.py"), ast.unparse(function_ast))
        write_to_file(os.path.join(output_dir, f"{function_name}_ast.txt"), ast.dump(function_ast, indent=4))
        write_to_file(os.path.join(output_dir, f"{function_name}_bytecode.txt"), function_bytecode.dis())
        write_to_file(os.path.join(output_dir, f"{function_name}_codeobj.txt"), "\n".join([f"{c}:{getattr(function_bytecode.codeobj, c)}" for c in dir(function_bytecode.codeobj)]))

    concolic_test_cases = ConcolicTestCaseGenerator(
        env = functions,
        entry_point=entry_point_function
    ).generate_test_cases()

    """
    random_test_cases = RandomTestCaseGenerator(
        env = { function_name : function_ast for function_name, (function_ast, _) in functions.items() },
        entry_point=entry_point_function
    ).generate_random_test_cases()
    """

    test_cases = concolic_test_cases
    # print(f"Generated {len(random_test_cases)} random test cases for {entry_point_function}")
    # print(random_test_cases)

    # TODO: Translate more programs (maybe)
    # TODO: (Kalle and Amir) Implement interpreter
    # TODO: (all of us) Implement concolic execution for test case generation

    # Run instrumenter on program to get instrumented program
    instrumented_dir = os.path.join(output_dir, "instrumented")
    os.makedirs(instrumented_dir, exist_ok=True)
    instrumented_program = os.path.join(instrumented_dir,os.path.basename(program_file_path))
    print(f"Instrumenting {os.path.basename(program_file_path)}")
    Instrumenter().instrument_file(program_file_path, instrumented_program)

    # Output instrumented program to output directory
    spec = importlib.util.spec_from_file_location("instrumented."+entry_point_function, instrumented_program)
    instrumented_fun = importlib.util.module_from_spec(spec)
    sys.modules["instrumented."+entry_point_function] = instrumented_fun

    # Run instrumented program on test cases
    # Output data traces to output directory
    dtrace_base_path = os.path.join(instrumented_dir, os.path.basename(program_file_path))
    dtraces = []
    fd = sys.stdout.fileno()
    print(f"Importing instrumented.{entry_point_function}")
    with os.fdopen(os.dup(fd), 'w') as old_stdout:
        for i, test_case in enumerate(test_cases):
            dtraces.append(dtrace_base_path+'_'+str(i)+".dtrace")
            with open(dtraces[-1], 'w', encoding='utf-8') as file:
                sys.stdout.close() # + implicit flush()
                os.dup2(file.fileno(), fd) # fd writes to 'to' file
                sys.stdout = os.fdopen(fd, 'w') # Python writes to fd
            try:
                spec.loader.exec_module(instrumented_fun)
                method = getattr(instrumented_fun, entry_point_function)
                method(*test_case)
            finally:
                sys.stdout.close() # + implicit flush()
                os.dup2(old_stdout.fileno(), fd) # fd writes to 'to' file
                sys.stdout = os.fdopen(fd, 'w') # Python writes to fd
        
    # Run Daikon on data traces to get invariants
    print(f"Running Daikon over {len(test_cases)} test cases.")
    daikon_result = subprocess.run(["java","-cp",os.path.join(os.path.dirname(__file__), "daikon.jar"),"daikon.Daikon","-o",dtrace_base_path, *dtraces], capture_output=True)
    if daikon_result.returncode != 0:
        write_to_file(os.path.join(output_dir, "daikon_error.txt"), daikon_result.stderr.decode('utf-8'))
    write_to_file(os.path.join(output_dir, "daikon_output.txt"), daikon_result.stdout.decode('utf-8'))
    # TODO: (Jimena) Parse Daikon output and translate invariants to Nagini syntax
    # TODO: (Jimena) Insert invariant annotations in program ast

    # Keep AST with invariants

    # TODO: Output program with invariants to output directory

    # TODO: (Ulas) Run Nagini on the annotated program to check invariants
    #       if it fails, remove the invariant and run again
    #       if it passes, we have found the proved invariants
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