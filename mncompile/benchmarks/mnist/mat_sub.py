def kernel(a, b):
    return [[p - q for p, q in zip(ra, rb)] for ra, rb in zip(a, b)]
