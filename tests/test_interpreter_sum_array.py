import pytest

from src.interpreter import Python39Interpreter
from tests.common import get_function_bytecode


def check_preconditions(a: list[int]) -> None:
    if len(a) == 0:
        raise RuntimeError("Precondition failed: len(a) > 0")


def sum_pure(a: list[int], fromIndex: int, toIndex: int) -> int:
    if fromIndex == toIndex:
        return 0
    return a[toIndex - 1] + sum_pure(a, fromIndex, toIndex - 1)


def sum_list(a: list[int]) -> int:
    check_preconditions(a)
    i = 0
    s = 0
    while i < len(a):
        s += a[i]
        i += 1
    return s


i_pure = Python39Interpreter(
    {
        sum_pure.__name__: get_function_bytecode(sum_pure),
    },
    sum_pure.__name__,
)

i_list = Python39Interpreter(
    {
        check_preconditions.__name__: get_function_bytecode(check_preconditions),
        sum_list.__name__: get_function_bytecode(sum_list),
    },
    sum_list.__name__,
)


def test_sum_pure_a():
    assert i_pure.run([[1, 2, 3, 4, 5], 0, 5]) == 15


def test_sum_pure_b():
    assert i_pure.run([[1, 2, 3, 4, 5], 1, 4]) == 9


def test_sum_pure_c():
    assert i_pure.run([[1, 2, 3, 4, 5], 2, 3]) == 3


def test_sum_list_a():
    assert i_list.run([[1, 2, 3, 4, 5]]) == 15


def test_sum_list_b():
    assert i_list.run([[-5, 9, -2, 3]]) == 5


def test_sum_list_empty_list():
    with pytest.raises(RuntimeError):
        i_list.run([[]])
