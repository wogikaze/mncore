def kernel(x):
    return [value.bit_length() - 1 for value in x]
