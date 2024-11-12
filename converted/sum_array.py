from nagini_contracts.contracts import *
from theories.TArrays import within

@Pure
def sum_pure(a: list[int], fromIndex: int, toIndex: int) -> int:
    Requires(Acc(list_pred(a)))
    Requires(len(a) > 0)
    Requires(within(a, fromIndex, toIndex))

    if fromIndex == toIndex:
        return 0
    return a[toIndex - 1] + sum_pure(a, fromIndex, toIndex - 1)

def check_preconditions(a: list[int]) -> None:
    if len(a) == 0:
        raise RuntimeError("Precondition failed: len(a) > 0")

def sum_list(a: list[int]) -> int:
    Requires(Acc(list_pred(a)))
    Requires(len(a) > 0)
    Ensures(Acc(list_pred(a)))
    Ensures(len(a) == Old(len(a)))
    Ensures(Result() == sum_pure(a, 0, len(a)))

    check_preconditions(a)

    i = 0
    s = 0

    Assert(0 == sum_pure(a, 0, i))
    Assert(a[0] == sum_pure(a, 0, 1))

    while i < len(a):
        Invariant(Acc(list_pred(a)))
        Invariant(len(a) == Old(len(a)))
        Invariant(0 <= i and i <= len(a))
        Invariant(s == sum_pure(a, 0, i))
        s += a[i]
        i += 1
        Assert(sum_pure(a, 0, i) == sum_pure(a, 0, i - 1) + a[i - 1])

    return s

if __name__ == "__main__":
    print(sum_pure([1, 2, 3], 0, 3))
    print(sum_list([1, 2, 3]))