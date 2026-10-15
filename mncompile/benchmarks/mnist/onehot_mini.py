def kernel(t):
    return [[1.0 if t[i] == j else 0.0 for j in range(16)] for i in range(len(t))]
