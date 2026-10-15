import math


def kernel(x):
    return [[math.exp(v) for v in row] for row in x]
