from nagini_contracts.contracts import *

def sum_one_to_n(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() == n * (n + 1) // 2)

    i = 0
    sum = 0

    while i < n:
        Invariant(0 <= i and i <= n)
        Invariant(sum == i * (i + 1) // 2)
        i += 1
        sum += i
    
    Assert(i == n)
    return sum