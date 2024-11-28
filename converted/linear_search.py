from typing import List
from nagini_contracts.contracts import *

def search(x: int, arr: List[int]) -> int:
    Requires(Acc(list_pred(arr)))
    #Ensures(Acc(list_pred(arr)))
     # Ensures(len(arr) == Old(len(arr)))
     # Ensures(Result() < len(arr))
     # Ensures(Implies(Result() >= 0, arr[Result()] == x))
     # Ensures(Implies(Forall(int, lambda i: Implies(0 <= i and i < len(arr), arr[i] != x)), Result() == -1))
    i = 0
    l = len(arr)
    while i < l:
        Invariant(Acc(list_pred(arr)))
         # Invariant(len(arr) == Old(len(arr)))
         # Invariant(l == len(arr))
         # Invariant(0 <= i and i <= l)
         # Invariant(Forall(int, lambda j: Implies(0 <= j and j < i, arr[j] != x)))
        if arr[i] == x:
            return i
        i += 1
    return -1