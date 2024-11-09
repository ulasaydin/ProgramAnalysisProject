from nagini_contracts.contracts import *
from theories.TArrays import within

@Pure
def eq(a: list[int], aFrom: int, aTo: int, b: list[int], bFrom: int, bTo: int) -> bool:
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(b)))
    Requires(within(a, aFrom, aTo))
    Requires(within(b, bFrom, bTo))
    Ensures(Result() == ( (aTo - aFrom == bTo - bFrom) and Forall(int, lambda i: Implies(aFrom <= i and i < aTo, a[i] == b[bFrom + (i - aFrom)]))))

    if aTo - aFrom != bTo - bFrom:
        return False
    else:
        if aFrom >= aTo:
            return True
        else:
            return (a[aFrom] == b[bFrom]) and eq(a, aFrom + 1, aTo, b, bFrom + 1, bTo)

def equals(a: list[int], a2: list[int]) -> bool:
    Requires(Acc(list_pred(a)) and Implies(a != a2, Acc(list_pred(a2))))
    Ensures(Acc(list_pred(a)) and Implies(Old(a) != Old(a2), Acc(list_pred(a2))))
    Ensures(Result() == (Old(a) == Old(a2) or eq(a, 0, len(a), a2, 0, len(a2))))

    if a == a2:
        return True
    
    l = len(a)
    if len(a2) != l:
        return False
    
    ic = 0

    while ic < l:
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a2)))
        Invariant(0 <= ic and ic <= l)
        Invariant(l == Old(len(a)))
        Invariant(eq(a, 0, ic, a2, 0, ic))

        if a[ic] != a2[ic]:
            return False
        
        ic += 1

    return True