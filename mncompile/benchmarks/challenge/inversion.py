def kernel(a):
    return [
        sum(row[j] > row[k] for j in range(len(row)) for k in range(j + 1, len(row)))
        for row in a
    ]
