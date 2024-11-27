from typing import List
from nagini_contracts.contracts import *


def check_preconditions(xs: List[int]) -> None:
    if len(xs) == 0:
        raise RuntimeError("Precondition failed: len(xs) > 0")


def min_list(xs: List[int]) -> int:
    Requires(Acc(list_pred(xs)))
    Requires(len(xs) > 0)
    Ensures(Acc(list_pred(xs)))
    Ensures(Forall(int, lambda i: Implies(0 <= i and i < len(xs), Result() <= xs[i])))

    check_preconditions(xs)

    minimum = xs[0]
    
    i = 0

    while i < len(xs):
        Invariant(Acc(list_pred(xs)))
        Invariant(0 <= i and i <= len(xs))
        Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, minimum <= xs[j])))
        
        if xs[i] < minimum:
            minimum = xs[i]
        i += 1
    
    return minimum