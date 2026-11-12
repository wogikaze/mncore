"""numpy model of c8-style programs (half Horner + f32 tail)."""
import numpy as np
def f32(v): return np.asarray(v, dtype=np.float64).astype(np.float32)
def h(v):
    """round f32 -> MN-Core half (s1e6m9), round-to-nearest-even, returned as f32."""
    v = np.asarray(v, dtype=np.float32)
    b = v.view(np.uint32).astype(np.uint64)
    lsb = (b >> 14) & 1
    b2 = (b + 0x1FFF + lsb) & ~np.uint64(0x3FFF)
    return b2.astype(np.uint32).view(np.float32)
def fma(a, b, c): return f32(np.float64(a) * np.float64(b) + np.float64(c))
def c8(x, A4, A3, A1, A0, L=None, scale=1.0):
    x = f32(x); A4, A3, A1, A0 = map(np.float32, (A4, A3, A1, A0))
    if L is None: L = np.float32(16 * np.float64(A4))
    xh = h(x)
    s = fma(h(A4), xh, A3)
    s = fma(h(s), xh, L)
    s = fma(h(s), xh, A1)
    s = fma(h(s), xh, A0)
    return fma(s, x, A0)
def c8b(x, A4, A3, A1, A0, C0):
    """c8 with a separate final constant C0 (imm on line 6)."""
    x = f32(x); A4, A3, A1, A0, C0 = map(np.float32, (A4, A3, A1, A0, C0))
    L = np.float32(16 * np.float64(A4)); xh = h(x)
    s = fma(h(A4), xh, A3); s = fma(h(s), xh, L); s = fma(h(s), xh, A1); s = fma(h(s), xh, A0)
    return fma(s, x, C0)
