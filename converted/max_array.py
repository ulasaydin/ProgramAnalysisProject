from nagini_contracts.contracts import *

def max_list(xs: list[int]) -> int:
    Requires(Acc(list_pred(xs)))
    Requires(len(xs) > 0)
    Ensures(Acc(list_pred(xs)))
    Ensures(Forall(int, lambda i: Implies(0 <= i and i < len(xs), Result() >= xs[i])))

    maximum = xs[0]
    
    i = 0

    while i < len(xs):
        Invariant(Acc(list_pred(xs)))
        Invariant(0 <= i and i <= len(xs))
        Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, maximum >= xs[j])))
        
        if xs[i] > maximum:
            maximum = xs[i]
        i += 1
    
    return maximum