from nagini_contracts.contracts import *

from theories.TArrays import *


def check_preconditions(a: list[int], from_index: int, to_index: int, val: int) -> None:
    if not within(a, from_index, to_index):
        raise RuntimeError("Precondition failed: within(a, from_index, to_index)")

def fill_b(a: list[int], from_index: int, to_index: int, val: int) -> None:
    Requires(Acc(list_pred(a)))
    Requires(within(a, from_index, to_index))

    Ensures(Acc(list_pred(a)))
    Ensures(len(a) == Old(len(a)))
    Ensures(Forall(int, lambda j: Implies(0 <= j and j < from_index, a[j] == Old(a[j]))))
    Ensures(eq(a, from_index, to_index, val))
    Ensures(Forall(int, lambda j: Implies(to_index <= j and j < len(a), a[j] == Old(a[j]))))

    check_preconditions(a, from_index, to_index, val)

    ic = from_index

    while ic < to_index:
        Invariant(Acc(list_pred(a)))
        Invariant(len(a) == Old(len(a)))
        Invariant(from_index <= ic and ic <= to_index)
        Invariant(Forall(int, lambda j: Implies(0 <= j and j < from_index, a[j] == Old(a[j]))))
        Invariant(eq(a, from_index, ic, val))
        Invariant(Forall(int, lambda j: Implies(to_index <= j and j < len(a), a[j] == Old(a[j]))))

        a[ic] = val
        ic += 1