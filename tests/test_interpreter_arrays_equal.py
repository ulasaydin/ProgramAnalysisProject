from src.interpreter import Python39Interpreter
from tests.common import get_function_bytecode


def equals(a: list[int], a2: list[int]) -> bool:
    if a == a2:
        return True
    l = len(a)
    if len(a2) != l:
        return False
    ic = 0
    while ic < l:
        if a[ic] != a2[ic]:
            return False
        ic += 1
    return True

env = {
    equals.__name__: get_function_bytecode(equals)
}

i = Python39Interpreter(
    env,
    equals.__name__
)

def test_interpreter_array_equals():
    assert i.run([[1, 2, 3], [1, 2, 3]])

def test_interpreter_array_not_equals():
    assert not i.run([[1, 2, 3], [1, 2, 4]])

def test_interpreter_array_not_equals_different_lengths():
    assert not i.run([[1, 2, 3], [1, 2, 3, 4]])