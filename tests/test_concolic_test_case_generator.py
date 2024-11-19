import pytest
import z3

from src.concolic_test_case_generator import ConcolicTestCaseGenerator
from tests.common import get_function_bytecode, get_function_ast


def check_preconditions(n: int) -> None:
    if n < 0:
        raise RuntimeError('Precondition failed: n >= 0')

def sum_one_to_n(n: int) -> int:
    check_preconditions(n)
    i = 0
    sum = 0
    while i < n:
        i += 1
        sum += i
    return sum

functions = {
    check_preconditions.__name__:  (get_function_ast(check_preconditions), get_function_bytecode(check_preconditions)),
    sum_one_to_n.__name__: (get_function_ast(sum_one_to_n), get_function_bytecode(sum_one_to_n))
}

def test_concolic_test_case_generator():
    ConcolicTestCaseGenerator(
        env = functions,
        entry_point = sum_one_to_n.__name__
    ).generate_test_cases([4])