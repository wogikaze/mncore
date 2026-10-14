def kernel(x):
    return [
        sum(
            row[left] > row[right]
            for left in range(len(row))
            for right in range(left + 1, len(row))
        )
        for row in x
    ]
