def kernel(a, b):
    return [[p / q for p in row] for row, q in zip(a, b)]
