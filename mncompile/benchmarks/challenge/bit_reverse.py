def kernel(x):
    return [
        sum(((value >> bit) & 1) << (63 - bit) for bit in range(64))
        for value in reversed(x)
    ]
