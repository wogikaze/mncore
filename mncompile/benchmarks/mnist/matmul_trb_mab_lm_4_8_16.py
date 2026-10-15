def kernel(a, b):
    # C = A @ B.T
    return [[sum(p * q for p, q in zip(ra, rb)) for rb in b] for ra in a]
