def kernel(a, b):
    return [[p + q for p, q in zip(row, b)] for row in a]
