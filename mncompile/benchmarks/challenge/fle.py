def kernel(x):
    return [float("inf") if v >= 1.0 else 0.0 for v in x]
