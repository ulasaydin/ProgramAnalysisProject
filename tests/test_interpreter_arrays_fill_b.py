import pytest

from src.interpreter import InterpreterError, Python39Interpreter
from tests.common import get_function_bytecode


def within(a: list[int], fromIndex: int, toIndex: int) -> bool:
    return 0 <= fromIndex and fromIndex <= toIndex and (toIndex <= len(a))


def check_preconditions(a: list[int], from_index: int, to_index: int, val: int) -> None:
    if not within(a, from_index, to_index):
        raise RuntimeError("Precondition failed: within(a, from_index, to_index)")


def fill_b(a: list[int], from_index: int, to_index: int, val: int) -> None:
    check_preconditions(a, from_index, to_index, val)
    ic = from_index
    while ic < to_index:
        a[ic] = val
        ic += 1


env = {
    within.__name__: get_function_bytecode(within),
    check_preconditions.__name__: get_function_bytecode(check_preconditions),
    fill_b.__name__: get_function_bytecode(fill_b),
}

i = Python39Interpreter(env, fill_b.__name__)


def test_arrays_fill_b():
    a = [1, 2, 3, 4, 5]
    i.run([a, 0, 5, 0])
    assert a == [0, 0, 0, 0, 0]


def test_arrays_fill_b_partial():
    a = [1, 2, 3, 4, 5]
    i.run([a, 1, 4, 0])
    assert a == [1, 0, 0, 0, 5]


def test_arrays_fill_b_precondition_failure():
    a = [1, 2, 3, 4, 5]
    with pytest.raises(InterpreterError):
        i.run([a, 1, 6, 0])
