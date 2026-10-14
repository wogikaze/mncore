def kernel(x):
    return [float("inf") if value >= 1.0 else 0.0 for value in x]
