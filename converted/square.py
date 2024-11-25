def square(n: int) -> int:
    result = 1
    i = 0
    while i < n:
        i += 1
        result += 2 * i + 1
    return result
