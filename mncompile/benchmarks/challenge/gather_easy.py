def kernel(x, indices):
    return [[row[i] for i in idx] for row, idx in zip(x, indices)]
