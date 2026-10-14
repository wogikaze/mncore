def kernel(x):
    return [
        0xFFFFBBBB
        if value % 15 == 0
        else 0x0000FFFF
        if value % 3 == 0
        else 0x0000BBBB
        if value % 5 == 0
        else value
        for value in x
    ]
