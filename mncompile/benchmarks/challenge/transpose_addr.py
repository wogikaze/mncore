def kernel(x):
    # Same logical matrix; only the physical layout differs.
    return [[x[i][j] for j in range(8)] for i in range(8)]
