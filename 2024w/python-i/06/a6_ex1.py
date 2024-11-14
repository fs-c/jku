def numerical_sequence():
    n = 0
    while True:
        n += 1
        # https://en.wikipedia.org/wiki/Arithmetic_progression
        yield n * (n + 1) // 2
