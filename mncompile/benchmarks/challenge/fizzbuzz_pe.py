def kernel(a):
    return [
        0xFFFFBBBB if v % 15 == 0 else 0x0000FFFF if v % 3 == 0 else 0x0000BBBB if v % 5 == 0 else v
        for v in a
    ]
