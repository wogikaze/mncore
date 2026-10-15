def kernel(a):
    return [[1.0 if v >= 0 else -0.0 for v in row] for row in a]
