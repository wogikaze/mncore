import struct, math
import numpy as np
from data import A, B
def bits(x): return struct.unpack('>I', struct.pack('>f', x))[0]
def fl(u): return struct.unpack('>f', struct.pack('>I', u & 0xffffffff))[0]
EVEN = [13, 11, 10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 2, 1, 1, 0]
ODD = [31, 30, 28, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13]
def rsqrt(x):
    u = bits(x); e = (u >> 23) & 0xff; m4 = (u >> 19) & 0xf
    oe = 190 - (e + 1) // 2
    m5 = (EVEN if e % 2 == 0 else ODD)[m4]
    return fl((oe << 23) | (m5 << 18))
f32 = lambda v: float(np.float32(v))
fma = lambda x, y, z: f32(x * y + z)   # double is exact enough for f32*f32
mul = lambda x, y: f32(x * y)
def report(name, recip):
    worst = 0; we = 0
    for n in range(4):
        for r in range(64):
            b = B[n][r]; a = recip(b)
            we = max(we, abs(1 - b * a))
            for x in A[n][r]:
                worst = max(worst, abs(mul(x, a) - x / b))
    print(f"{name:40s} max|1-ba|={we:.3e} max abs err={worst:.3e} {'OK' if worst <= 1e-4 else 'NG'}")
    return worst
def newton(a, b, c=2.0):
    y = fma(-a, b, c); return mul(y, a)
if __name__ == '__main__':
    report("rsqrt^2 + 2 newton", lambda b: newton(newton(mul(rsqrt(b), rsqrt(b)), b), b))
    report("rsqrt^2 + 1 newton", lambda b: newton(mul(rsqrt(b), rsqrt(b)), b))
    for magic in (0x7EF311C3, 0x7EF311C7, 0x7EEEEEEE, 0x7F000000):
        report(f"magic {magic:#x} + 2 newton", lambda b: newton(newton(fl(magic - bits(b)), b), b))
