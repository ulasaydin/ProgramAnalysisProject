from nagini_contracts.contracts import *

from converted.sum_one_to_n import check_preconditions


def check_preconditions(xs: list[int]) -> None:
    if len(xs) == 0:
        raise RuntimeError("Precondition failed: len(xs) > 0")


def min_list(xs: list[int]) -> int:
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