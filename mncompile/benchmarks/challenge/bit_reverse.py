def kernel(x):
    # The words form one bit string (word 0 first, MSB first); reverse the whole string.
    n = len(x)
    return [
        sum(((x[n - 1 - i] >> b) & 1) << (63 - b) for b in range(64))
        for i in range(n)
    ]
