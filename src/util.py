import ast
import dis
import importlib
import importlib.util
import sys
import types
import os
import random
from typing import Union, Any
import z3

sys.path.append(os.path.dirname(__file__))

from symbolic_integer_array import SymbolicIntegerArray


def extract_functions(program_root: ast.Module, program_file_path: str) -> dict[str, ast.FunctionDef]:
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
                imported_names = list(map(lambda alias: alias.name, node.names))
                for imported_module_node in ast.iter_child_nodes(imported_module_root):
                    if isinstance(imported_module_node, ast.FunctionDef):
                        if imported_module_node.name in imported_names or '*' in imported_names:
                            imported_module_node.module = spec.origin
                            functions[imported_module_node.name] = imported_module_node
    
    for function_name, function_node in functions.items():
        print(f"Extracted function {function_name} from module {function_node.module}")

    return functions

def function_ast_to_bytecode(function: ast.FunctionDef) -> dis.Bytecode:
    return function_source_to_bytecode(ast.unparse(function))

def function_source_to_bytecode(function: str) -> dis.Bytecode:
    compiled_function = compile(function, '<string>', 'exec', optimize=0)
    for co_const in compiled_function.co_consts:
        if isinstance(co_const, types.CodeType):
            return dis.Bytecode(types.FunctionType(co_const, globals(), compiled_function.co_name).__code__)

def remove_nagini_annotations(function: Union[ast.Module, ast.FunctionDef]) -> Union[ast.Module, ast.FunctionDef]:
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

def write_to_file(path: str, text: str):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as file:
        file.write(text)

def extract_arguments_and_annotations(function_ast: ast.FunctionDef) -> list[tuple[str, Any]]:
    return [(arg.arg, arg.annotation) for arg in function_ast.args.args]

def extract_parameter_types(function_ast: ast.FunctionDef) -> list[str]:
        parameter_types = []
        for arg in function_ast.args.args:
            if isinstance(arg.annotation, ast.Name):
                parameter_types.append(arg.annotation.id)
            elif isinstance(arg.annotation, ast.Subscript):
                if isinstance(arg.annotation.value, ast.Name) and arg.annotation.value.id == "list":
                    element_type = arg.annotation.slice.id if isinstance(arg.annotation.slice, ast.Name) else "Any"
                    parameter_types.append(f"list[{element_type}]")
            else:
                parameter_types.append("Any")
        return parameter_types

def extract_parameter_names(function_ast: ast.FunctionDef) -> list[str]:
    return [arg.arg for arg in function_ast.args.args]

def generate_random_value(param_type: str) -> Any:
    value = None
    if param_type == "int":
        value = random.randint(-100, 100)
    elif param_type == "float":
        value = random.uniform(-100.0, 100.0)
    elif param_type == "str":
        value = ''.join(random.choices("abcdefghijklmnopqrstuvwxyz", k=random.randint(1, 10)))
    elif param_type == "bool":
        value = random.choice([True, False])
    elif param_type.startswith("list"):
        inner_type = param_type[5:-1]
        value = [generate_random_value(inner_type) for _ in range(random.randint(1, 10))]
    return value

def function_initial_locals_from_inputs(bytecode: dis.Bytecode, inputs: list[Any]) -> dict[str, Any]:
    if len(inputs) < bytecode.codeobj.co_argcount:
        raise TypeError(f"Expected {bytecode.codeobj.co_argcount} positional arguments, got {len(inputs)}")
    assert len(inputs) >= bytecode.codeobj.co_argcount
    locals_ = dict(zip(
        bytecode.codeobj.co_varnames[:bytecode.codeobj.co_argcount],
        inputs[:bytecode.codeobj.co_argcount]
    ))
    # the following is to handle *args
    if len(inputs) > bytecode.codeobj.co_argcount:
        locals_[bytecode.codeobj.co_argcount] = inputs[bytecode.codeobj.co_argcount:]
    return locals_

def types_to_symbolic_inputs(arguments: list[tuple[str, Any]]) -> list[Any]:
    symbolic_arguments = []
    for name, annotation in arguments:
        if isinstance(annotation, ast.Name):
            if annotation.id == 'int':
                symbolic_arguments.append(z3.Int(name))
            elif annotation.id == 'bool':
                symbolic_arguments.append(z3.Bool(name))
        elif isinstance(annotation, ast.Subscript) and isinstance(annotation.value, ast.Name) and annotation.value.id == 'list':
            if isinstance(annotation.slice, ast.Name) and annotation.slice.id == 'int':
                symbolic_arguments.append(SymbolicIntegerArray(name))
        else:
            raise NotImplementedError(f"Unsupported type annotation {annotation}")
    return symbolic_arguments

def to_concrete_value(x: Union[z3.ExprRef, SymbolicIntegerArray], model: z3.ModelRef, default=None) -> Union[int, bool, list[int]]:
    """ Tries to evaluate x in model
        if not found or can not be evaluated default is returned if provided
        if default is not provided, random value is returned
    """
    pass