from typing import List
from nagini_contracts.contracts import *
from theories.TArrays import sorted, within, TArraysIn, less, grt


def check_preconditions(a: List[int], fromIndex: int, toIndex: int, key: int) -> None:
    if not within(a, fromIndex, toIndex):
        raise RuntimeError("Precondition failed: within(a, fromIndex, toIndex)")
    if not sorted(a, fromIndex, toIndex):
        raise RuntimeError("Precondition failed: sorted(a, fromIndex, toIndex)")

def binary_search(a: List[int], fromIndex: int, toIndex: int, key: int) -> int:
    Requires(Acc(list_pred(a)))
    Requires(within(a, fromIndex, toIndex))
    Requires(sorted(a, fromIndex, toIndex))
    Ensures(Acc(list_pred(a)))
    Ensures(len(a) == Old(len(a)))
    Ensures(Result() < len(a))
    Ensures(Implies(Result() >= 0, a[Result()] == key))
    Ensures(Implies(Result() < 0, not TArraysIn(a, fromIndex, toIndex, key)))

    check_preconditions(a, fromIndex, toIndex, key)

    low = fromIndex
    high = toIndex - 1

    while low <= high:
        Invariant(Acc(list_pred(a)))
        Invariant(len(a) == Old(len(a)))
        Invariant(0 <= fromIndex and fromIndex <= toIndex and toIndex <= len(a))
        Invariant(high >= -1)
        Invariant(fromIndex <= low)
        Invariant(low <= high + 1)
        Invariant(high < toIndex)
        Invariant(sorted(a, fromIndex, toIndex))
        Invariant(less(a, fromIndex, low, key))
        Invariant(grt(a, high + 1, toIndex, key))

        mid = low + (high - low) // 2
        midVal = a[mid]
        if midVal < key:
            low = mid + 1
        elif midVal > key:
            high = mid - 1
        else:
            return mid
    return -(low + 1)