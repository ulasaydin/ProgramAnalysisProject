import pytest

from src.interpreter import Python39Interpreter
from tests.common import get_function_bytecode


def sorted(a: list[int], fromIndex: int, toIndex: int) -> bool:
    if toIndex - fromIndex <= 1:
        return True
    first = a[fromIndex]
    second = a[fromIndex + 1]
    return first <= second and sorted(a, fromIndex + 1, toIndex)

def within(a: list[int], fromIndex: int, toIndex: int) -> bool:
    return 0 <= fromIndex and fromIndex <= toIndex and (toIndex <= len(a))

def check_preconditions(a: list[int], fromIndex: int, toIndex: int, key: int) -> None:
    if not within(a, fromIndex, toIndex):
        raise RuntimeError('Precondition failed: within(a, fromIndex, toIndex)')
    if not sorted(a, fromIndex, toIndex):
        raise RuntimeError('Precondition failed: sorted(a, fromIndex, toIndex)')

def binary_search(a: list[int], fromIndex: int, toIndex: int, key: int) -> int:
    check_preconditions(a, fromIndex, toIndex, key)
    low = fromIndex
    high = toIndex - 1
    while low <= high:
        mid = low + (high - low) // 2
        midVal = a[mid]
        if midVal < key:
            low = mid + 1
        elif midVal > key:
            high = mid - 1
        else:
            return mid
    return -(low + 1)

env = {
    sorted.__name__: get_function_bytecode(sorted),
    within.__name__: get_function_bytecode(within),
    check_preconditions.__name__: get_function_bytecode(check_preconditions),
    binary_search.__name__: get_function_bytecode(binary_search)
}

i = Python39Interpreter(
    env,
    binary_search.__name__
)

def test_binary_search_key_found():
    assert i.run([[1, 2, 3, 4, 5], 0, 5, 3]) == 2


def test_binary_search_key_not_found():
    assert i.run([[1, 2, 3, 4, 5], 0, 5, 8]) < 0

def test_binary_search_not_sorted():
    with pytest.raises(RuntimeError):
        i.run([[1, 2, 3, 5, 4], 0, 5, 3])

def test_binary_search_out_of_bounds():
    with pytest.raises(RuntimeError):
        i.run([[1, 2, 3, 4, 5], 0, 6, 3])