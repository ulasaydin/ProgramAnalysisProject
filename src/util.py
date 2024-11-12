import ast
import dis
import importlib
import sys
import types
import os


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