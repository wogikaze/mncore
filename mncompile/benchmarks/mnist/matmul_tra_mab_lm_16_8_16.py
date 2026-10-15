def kernel(a, b):
    # C = A.T @ B
    return [[sum(a[k][i] * b[k][j] for k in range(len(a))) for j in range(len(b[0]))] for i in range(len(a[0]))]
