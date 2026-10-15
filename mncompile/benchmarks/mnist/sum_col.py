def kernel(a):
    return [sum(row[j] for row in a) for j in range(len(a[0]))]
