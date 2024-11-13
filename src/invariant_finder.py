import argparse
import dis
from datetime import datetime
import ast
import os
import sys

sys.path.append(os.path.dirname(__file__))

from util import write_to_file, extract_functions, get_function_bytecode
from concolic_test_case_generator import ConcolicTestCaseGenerator
from platformdirs import user_data_dir
from config import APP_AUTHOR, APP_NAME
from util import remove_nagini_annotations


def find_invariants(program_file_path: str, entry_point_function: str, output_dir: str):
    print(f"Finding invariants for {entry_point_function} in {program_file_path}:")
    print(f"Writing results to {output_dir}")

    program_file_path = os.path.abspath(program_file_path)

    with open(program_file_path) as program_file:
        program_root = ast.parse(program_file.read(), program_file_path)

    functions: dict[str, (ast.FunctionDef, dis.Bytecode)] = {}

    for function_name, function_ast in extract_functions(program_root, program_file_path).items():
        function_without_annotations = remove_nagini_annotations(function_ast)
        functions[function_name] = (function_without_annotations, get_function_bytecode(function_without_annotations))

    if entry_point_function not in functions:
        raise RuntimeError(f"Entry point method {entry_point_function} not found in program")

    for function_name, (function_ast, function_bytecode) in functions.items():
        write_to_file(os.path.join(output_dir, f"{function_name}_without_annotations.py"), ast.unparse(function_ast))
        write_to_file(os.path.join(output_dir, f"{function_name}_ast.txt"), ast.dump(function_ast, indent=4))
        write_to_file(os.path.join(output_dir, f"{function_name}_bytecode.txt"), function_bytecode.dis())

    test_cases = ConcolicTestCaseGenerator(
        env = { function_name : function_bytecode for function_name, (_, function_bytecode) in functions.items() },
        entry_point=entry_point_function
    ).generate_test_cases()

    # TODO: Translate more programs (maybe)

    # TODO: Implement interpreter
    # TODO: Implement concolic execution for test case generation
    # TODO: Run instrumenter on program to get instrumented program
    # TODO: Output instrumented program to output directory
    # TODO: Run instrumented program on test cases
    # TODO: Output data traces to output directory
    # TODO: Run Daikon on data traces to get invariants
    # TODO: Parse Daikon output and translate invariants to Nagini syntax
    # TODO: Insert invariant annotations in program ast
    # TODO: Output program with invariants to output directory
    # TODO: Run Nagini on the annotated program to check invariants
    #       if it fails, remove the invariant and run again
    #       if it passes, we have found the proved invariants


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog="Loop Invariant Finder")
    parser.add_argument("program_file_path", help="Program file path")
    parser.add_argument("entry_point_function", help="Entry point function name")
    args = parser.parse_args()

    program_file_path = args.program_file_path
    entry_point_function_name = args.entry_point_function

    user_data_directory = user_data_dir(APP_NAME, APP_AUTHOR)

    output_dir_name = f"Invariants-{os.path.basename(program_file_path)}-{entry_point_function_name}-{datetime.now().strftime(f'%Y-%m-%d_%H-%M-%S')}"
    output_dir = os.path.join(user_data_directory, output_dir_name)

    find_invariants(program_file_path, entry_point_function_name, output_dir)