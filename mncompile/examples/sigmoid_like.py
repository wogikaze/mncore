def kernel(a):
    # clipped linear "hard sigmoid" with a small error budget
    return [[min(max(0.25 * v + 0.5, 0.0), 1.0) for v in row] for row in a]
