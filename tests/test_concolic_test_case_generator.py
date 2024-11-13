from src.concolic_test_case_generator import ConcolicTestCaseGenerator
from src.util import get_function_bytecode, get_method_preconditions
import inspect, ast

def Requires(condition):
    pass

def minimum(a: int, b: int) -> int:
    Requires(a >= 0)
    if a < b:
        return a
    else:
        return b

def test_fuzzer():
    function_ast = ast.parse(inspect.getsource(minimum)).body[0]
    bytecode = get_function_bytecode(function_ast)

    ConcolicTestCaseGenerator({"minimum" : bytecode}, "minimum").generate_test_cases()