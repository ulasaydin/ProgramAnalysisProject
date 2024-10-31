def client(n: int) -> int:
    Requires(n >= 0)
    Ensures(Result() == n * (n + 1) / 2)
    i = 0
    sum = 0
    while i < n:
        Invariant(i <= n)
        Invariant(sum == i * (i + 1) / 2)
        i += 1
        sum += i
    Assert(i == n)
