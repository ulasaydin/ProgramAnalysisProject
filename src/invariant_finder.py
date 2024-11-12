from datetime import datetime
import dis
import importlib
import importlib.util
import sys
import ast
import types
import os
from fuzzer import Fuzzer
from platformdirs import user_data_dir
from config import APP_AUTHOR, APP_NAME


def extract_functions(program_root: ast.Module, program_file_path: str) -> tuple[ast.FunctionDef, dict[str, ast.FunctionDef]]:
    functions : dict[str, ast.FunctionDef] = dict()

    for node in ast.iter_child_nodes(program_root):
        if isinstance(node, ast.FunctionDef):
            node.module = program_file_path
            functions[node.name] = node
        if isinstance(node, ast.ImportFrom):
            if node.module == 'nagini_contracts.contracts':
                continue
            if program_file_path not in sys.path:
                sys.path.append(os.path.abspath(os.path.dirname(program_file_path)))
            if (spec := importlib.util.find_spec(node.module)) is not None:
                with open(spec.origin) as module_file:
                    imported_module_root = ast.parse(module_file.read(), spec.origin)
                imported_names = map(lambda alias: alias.name, node.names)
                for imported_module_node in ast.iter_child_nodes(imported_module_root):
                    if isinstance(imported_module_node, ast.FunctionDef) and imported_module_node.name in imported_names:
                        imported_module_node.module = spec.origin
                        functions[imported_module_node.name] = imported_module_node
    
    for function_name, function_node in functions.items():
        print(f"Extracted function {function_name} from module {function_node.module}")

    return functions

def get_function_bytecode(function: ast.FunctionDef) -> dis.Bytecode:
    compiled_function = compile(ast.unparse(function), '<string>', 'exec')
    for co_const in compiled_function.co_consts:
        if isinstance(co_const, types.CodeType):
            bytecodes = co_const
    return dis.Bytecode(types.FunctionType(bytecodes, globals(), function.name).__code__)

def remove_nagini_annotations(function: ast.FunctionDef) -> ast.FunctionDef:
    class NaginiAnnotationRemover(ast.NodeTransformer):
        def visit_Expr(self, node: ast.Expr):
            if isinstance(node.value, ast.Call) and node.value.func.id in ["Requires", "Ensures", "Invariant", "Assert"]:
                return None
            return node
    
    new_function = NaginiAnnotationRemover().visit(function)
    new_function.decorator_list = []
    return new_function

def get_method_preconditions(function: ast.FunctionDef) -> list[ast.Expr]:
    class PreconditionExtractor(ast.NodeVisitor):
        def __init__(self):
            super().__init__()
            self.preconditions = []
        
        def visit_Expr(self, node: ast.Expr):
            if isinstance(node.value, ast.Call) and node.value.func.id == "Requires":
                self.preconditions.append(node)
            return node
    
    extractor = PreconditionExtractor()
    extractor.visit(function)
    return extractor.preconditions

def find_invariants(program_file_path: str, entry_point_method: str, output_dir: str):
    print(f"Finding invariants for {entry_point_method} in {program_file_path}:")
    print(f"Writing results to {output_dir}")

    program_file_path = os.path.abspath(program_file_path)

    with open(program_file_path) as program_file:
        program_root = ast.parse(program_file.read(), program_file_path)

    functions = extract_functions(program_root, program_file_path)

    if entry_point_method not in functions:
        raise RuntimeError(f"Entry point method {entry_point_method} not found in program")
    main_function = functions[entry_point_method]

    main_function_preconditions = get_method_preconditions(main_function)

    main_function_without_annotations = remove_nagini_annotations(main_function)

    main_function_bytecode = get_function_bytecode(main_function_without_annotations)

    test_cases = Fuzzer(main_function_without_annotations, main_function_bytecode, main_function_preconditions).generate_test_cases()

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
    program_file_path = sys.argv[1]
    main_method_name = sys.argv[2]

    user_data_directory = user_data_dir(APP_NAME, APP_AUTHOR)

    output_dir_name = f"Invariants-{os.path.basename(program_file_path)}-{main_method_name}-{datetime.now().strftime(f'%Y-%m-%d_%H-%M-%S')}"
    output_dir = os.path.join(user_data_directory, output_dir_name)
    os.makedirs(output_dir)

    find_invariants(program_file_path, main_method_name, output_dir)