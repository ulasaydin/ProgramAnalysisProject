import pytest

from src.interpreter import Python39Interpreter
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

env = {
    check_preconditions.__name__: get_function_bytecode(check_preconditions),
    sum_one_to_n.__name__: get_function_bytecode(sum_one_to_n)
}

i = Python39Interpreter(
    env,
    sum_one_to_n.__name__
)

def test_sum_one_to_n():
    assert i.run([5]) == 15

def test_sum_one_to_n_negative():
    with pytest.raises(RuntimeError):
        i.run([-5])