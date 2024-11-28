from nagini_contracts.contracts import *


def check_preconditions(n: int) -> None:
    if n < 0:
        raise RuntimeError("Precondition n >= 0 failed")

def square(n: int) -> int:
    Requires(n >= 0)
    #Ensures(Result() == n * n)
    check_preconditions(n)
    result = 0
    i = 0
    while i < n:
        #Invariant(0 <= i and i <= n)
        #Invariant(result == i * i)
        result += 2 * i + 1
        i += 1
    return result

if __name__ == "__main__":
    assert square(1) == 1
    assert square(2) == 4
    assert square(3) == 9
    assert square(4) == 16
    assert square(5) == 25
    assert square(6) == 36