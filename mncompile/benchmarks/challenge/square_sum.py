def kernel(x):
    return [sum(v * v for v in row) for row in x]
