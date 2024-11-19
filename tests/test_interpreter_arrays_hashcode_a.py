import pytest

from src.interpreter import Python39Interpreter
from tests.common import get_function_bytecode


def hashCode_a(a: list[int]) -> int:
    result = 1
    ic = 0
    while ic < len(a):
        element = a[ic]
        result = 31 * result + element
        ic += 1
    return result


i = Python39Interpreter(
    {
        hashCode_a.__name__: get_function_bytecode(hashCode_a),
    },
    hashCode_a.__name__,
)


def test_hashcode():
    assert i.run([[1, 2, 3]]) == 30817


def test_hashcode_empty():
    assert i.run([[]]) == 1


def test_hashcode_one_value():
    assert i.run([[1]]) == 32


def test_hashcode_negative():
    assert i.run([[-1, -5]]) == 925
