def kernel(x, indices):
    return [
        [row[index] for index in row_indices] for row, row_indices in zip(x, indices)
    ]
