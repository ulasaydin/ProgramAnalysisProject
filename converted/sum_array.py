from nagini_contracts.contracts import *
from theories.TArrays import within

@Pure
def sum_pure(a: list[int], fromIndex: int, toIndex: int) -> int:
    Requires(Acc(list_pred(a)))
    Requires(len(a) > 0)
    Requires(0 <= fromIndex and fromIndex <= toIndex and toIndex < len(a))

    if fromIndex >= toIndex:
        return a[0]
    else:
        return a[toIndex] + sum_pure(a, fromIndex, toIndex - 1)

def sum_list(a: list[int]) -> int:
    Requires(Acc(list_pred(a)))
    Requires(len(a) > 0)
    Ensures(Acc(list_pred(a)))
    Ensures(len(a) == Old(len(a)))
    Ensures(Result() == sum_pure(a, 0, len(a) - 1))

    i = 0
    s = a[0]

    while i < len(a):
        Invariant(Acc(list_pred(a)))
        Invariant(len(a) == Old(len(a)))
        Invariant(0 <= i and i <= len(a))
        Invariant(Implies(i < len(a), s == sum_pure(a, 0, i)))
        s += a[i]
        i += 1
    
    return s