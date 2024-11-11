def client(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() == n * (n + 1) / 2)
    i = 0
    sum = 0
    # loop invariant ---> ENTER
    while i < n:
        Invariant(i <= n) # iter invariant ---> ENTER
        Invariant(sum == i * (i + 1) / 2)
        i += 1
        sum += i
        # iter invariant ---> EXIT
    # loop invariant ---> EXIT
    Assert(i == n)
