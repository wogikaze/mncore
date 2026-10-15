def kernel(src):
    # The vector is broadcast to all eight L2Bs.
    return [list(src) for _ in range(8)]
