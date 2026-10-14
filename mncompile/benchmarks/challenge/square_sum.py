def kernel(x):
    return [sum(value * value for value in row) for row in x]
