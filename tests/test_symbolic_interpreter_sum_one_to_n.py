import pytest
import z3

from src.symbolic_interpreter import SymbolicInterpreter
from tests.common import get_function_bytecode


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

i = SymbolicInterpreter(
    {check_preconditions.__name__: get_function_bytecode(check_preconditions),
     sum_one_to_n.__name__: get_function_bytecode(sum_one_to_n)},
    sum_one_to_n.__name__
)

def test_sum_one_to_n():
    pass

def test_sum_one_to_n_negative():
    pass