from nagini_contracts.contracts import *

@Pure
def within(a: list[int], fromIndex: int, toIndex: int) -> bool:
    Requires(Acc(list_pred(a)))
    Ensures(Result() == (0 <= fromIndex and fromIndex <= toIndex and toIndex <= len(a)))

    return 0 <= fromIndex and fromIndex <= toIndex and toIndex <= len(a)

@Pure
def eq(a: list[int], fromIndex: int, toIndex: int, key: int) -> bool:
    Requires(Acc(list_pred(a)) and within(a, fromIndex, toIndex))
    Ensures(Result() == Forall(int, lambda i: Implies(fromIndex <= i and i < toIndex, a[i] == key)))

    if fromIndex >= toIndex:
        return True
    else:
        first = a[fromIndex]
        return first == key and eq(a, fromIndex + 1, toIndex, key)

@Pure
def sorted(a: list[int], fromIndex: int, toIndex: int) -> bool:
    Requires(Acc(list_pred(a)))
    Requires(within(a, fromIndex, toIndex))
    Ensures(Result() == Forall(int, lambda i: 
                        Forall(int, lambda j: 
                        Implies(
                            fromIndex <= i and i < j and j < toIndex, 
                            a[i] <= a[j]))))

    if toIndex - fromIndex <= 1:
        return True
    first = a[fromIndex]
    second = a[fromIndex + 1]
    return first <= second and sorted(a, fromIndex + 1, toIndex)

@Pure
def TArraysIn(a: list[int], fromIndex: int, toIndex: int, key: int) -> bool:
    Requires(Acc(list_pred(a)))
    Requires(within(a, fromIndex, toIndex))
    Ensures(Result() == Exists(int, lambda i: fromIndex <= i and i < toIndex and a[i] == key))

    if fromIndex >= toIndex:
        return False
    first = a[fromIndex]
    return first == key or TArraysIn(a, fromIndex + 1, toIndex, key)

@Pure
def less(a: list[int], fromIndex: int, toIndex: int, key: int) -> bool:
    Requires(Acc(list_pred(a)))
    Requires(within(a, fromIndex, toIndex))
    Ensures(Result() == Forall(int, lambda i: Implies(fromIndex <= i and i < toIndex, a[i] < key)))

    if fromIndex >= toIndex:
        return True
    first = a[fromIndex]
    return first < key and less(a, fromIndex + 1, toIndex, key)

@Pure
def grt(a: list[int], fromIndex: int, toIndex: int, key: int) -> bool:
    Requires(Acc(list_pred(a)))
    Requires(within(a, fromIndex, toIndex))
    Ensures(Result() == Forall(int, lambda i: Implies(fromIndex <= i and i < toIndex, a[i] > key)))

    if fromIndex >= toIndex:
        return True
    first = a[fromIndex]
    return first > key and grt(a, fromIndex + 1, toIndex, key)