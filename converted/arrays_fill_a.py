from typing import List
from nagini_contracts.contracts import *
from theories.TArrays import eq

def fill_a(a: List[int], val: int) -> None:
    Requires(Acc(list_pred(a)))
    Ensures(Acc(list_pred(a)))
    Ensures(eq(a, 0, len(a), val))

    ic = 0
    l = len(a)

    while ic < l:
        Invariant(Acc(list_pred(a)))
        Invariant(l == len(a))
        Invariant(0 <= ic and ic <= l)
        Invariant(eq(a, 0, ic, val))
        a[ic] = val
        ic += 1