#!/usr/bin/env python3
"""64-bit class masks for llsl-by-i + hrelu/frelu flag extraction."""
FIZ = {3, 6, 9, 12}; FH = {15}; BUZ = {0, 5, 10}; Z = {0, 6, 10, 12}
def mask_from_halves(conds):
    """conds[h] = set of i (0..15) for which half h's flag (MSB==0) must be 1 -> M bit (63-16h-i) = 0."""
    M = 0
    for h in range(4):
        for i in range(16):
            if i not in conds[h]:
                M |= 1 << (63 - 16 * h - i)
    return M
FzFH = FIZ | FH; FzB = FIZ | BUZ
M_W1 = mask_from_halves([FzFH, FzFH, FzB, set()])
M_W2 = mask_from_halves([BUZ, BUZ, FH, set()])
def mask_from_words(conds):
    """single-precision frelu: word w flag from bit (63-32w-i)."""
    M = 0
    for w in range(2):
        for i in range(16):
            if i not in conds[w]:
                M |= 1 << (63 - 32 * w - i)
    return M
M_Z = mask_from_words([Z, Z])
if __name__ == "__main__":
    for nm in ("M_W1", "M_W2", "M_Z"):
        print(nm, hex(globals()[nm]))
