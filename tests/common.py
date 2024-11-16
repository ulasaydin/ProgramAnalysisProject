import ast
import dis
import inspect
import textwrap
import types

from src.util import function_source_to_bytecode


def get_function_bytecode(function: types.FunctionType) -> dis.Bytecode:
    return function_source_to_bytecode(textwrap.dedent(inspect.getsource(function)))

