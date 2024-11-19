import pytest

from src.interpreter import Python39Interpreter
from tests.common import get_function_bytecode


def check_preconditions(xs: list[int]) -> None:
    if len(xs) == 0:
        raise RuntimeError("Precondition failed: len(xs) > 0")


def min_list(xs: list[int]) -> int:
    check_preconditions(xs)
    minimum = xs[0]
    i = 0
    while i < len(xs):
        if xs[i] < minimum:
            minimum = xs[i]
        i += 1
    return minimum


i = Python39Interpreter(
    {
        check_preconditions.__name__: get_function_bytecode(check_preconditions),
        min_list.__name__: get_function_bytecode(min_list),
    },
    min_list.__name__,
)


def test_min_list():
    assert i.run([[1, 2, 3, 4, 5]]) == 1


def test_min_list_single_element():
    assert i.run([[42]]) == 42


def test_min_list_all_negative():
    assert i.run([[-1, -2, -3, -4, -5]]) == -5


def test_min_list_mixed_values():
    assert i.run([[-10, 0, 10, 5, -5]]) == -10


def test_min_list_duplicates():
    assert i.run([[1, 3, 3, 2, 1]]) == 1


def test_min_list_empty():
    with pytest.raises(RuntimeError):
        i.run([[]])
