def kernel(a):
    return [[v + 0.001 * v * v for v in row] for row in a]
