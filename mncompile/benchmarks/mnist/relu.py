def kernel(a):
    return [[v if v >= 0 else -0.0 for v in row] for row in a]
