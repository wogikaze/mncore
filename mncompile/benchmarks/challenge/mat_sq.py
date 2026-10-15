def kernel(x):
    # Y[i] = (X[i] @ X[i]) transposed
    n = 16
    return [
        [[sum(m[k][t] * m[t][j] for t in range(n)) for k in range(n)] for j in range(n)]
        for m in x
    ]
