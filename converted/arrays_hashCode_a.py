from typing import List
from nagini_contracts.contracts import *

def hashCode_a(a: List[int]) -> int:
    Requires(Acc(list_pred(a)))

    result = 1
    ic = 0

    while ic < len(a):
        Invariant(Acc(list_pred(a)))
        Invariant(len(a) == Old(len(a)))
        Invariant(0 <= ic and ic <= len(a))
        element = a[ic]
        result = 31 * result + element
        ic += 1

    return result