from nagini_contracts.contracts import *

def check_preconditions(n: int) -> None:
    if n < 0:
        raise RuntimeError("Precondition n >= 0 failed")

def cube(n: int) -> int:
    Requires(n >= 0)
    #Ensures(Result() == n * n * n)
    check_preconditions(n)
    result = 0
    square = 0
    i = 0
    while i < n:
        #Invariant(0 <= i and i <= n)
        #Invariant(square == i * i)
        #Invariant(result == i * i * i)
        result += 3 * square + 3 * i + 1
        square += 2 * i + 1
        i += 1
    return result

if __name__ == "__main__":
    assert cube(1) == 1
    assert cube(2) == 8
    assert cube(3) == 27
    assert cube(4) == 64
    assert cube(5) == 125