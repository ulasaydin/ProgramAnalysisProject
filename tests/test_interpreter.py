import dis
import types
import inspect
import textwrap

from src.interpreter import Python39Interpreter
from src.util import function_source_to_bytecode


def get_function_bytecode(function: types.FunctionType) -> dis.Bytecode:
    return function_source_to_bytecode(textwrap.dedent(inspect.getsource(function)))


def test_binary_search():
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

    i = Python39Interpreter(
        {
            sorted.__name__ : get_function_bytecode(sorted),
            within.__name__ : get_function_bytecode(within),
            check_preconditions.__name__ : get_function_bytecode(check_preconditions),
            binary_search.__name__ : get_function_bytecode(binary_search)
        },
        binary_search.__name__,
        [[1, 2, 3, 4, 5], 0, 5, 3]
    )

    assert i.run() == 2