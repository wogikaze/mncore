def kernel(x):
    return [
        [
            [
                sum(matrix[k][i] * matrix[j][k] for k in range(len(matrix)))
                for j in range(len(matrix))
            ]
            for i in range(len(matrix))
        ]
        for matrix in x
    ]
