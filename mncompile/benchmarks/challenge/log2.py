def kernel(x):
    return [v.bit_length() - 1 for v in x]
