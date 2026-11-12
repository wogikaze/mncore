"""Structural model of the FizzBuzz byte stream, and the per-byte renderer budget.

NEW RESULT (verified below): the whole stream is a concatenation of 15-token
blocks whose start number is always n0 == 10 (mod 15).  This includes the 9-token
prefix, which is exactly the tail (j = 6..14) of the *virtual* block n0 = -5.

  segment   n0            stream start S   period P   field width d
  prefix    -5            -25               55         1
  d=2       10 + 15 q     30                63         2
  d=3       100 + 15 q    408               71         3
  d=4       1000 + 15 q   4668              79         4

Field start inside a block:  C_d(j) = (d+1) j + (4-d) A(j) + (8-d) [j > 5],
with A(j) = #{0,2,8,10,11,14} < j.  The six short fields are Buzz at j=0,10 and
Fizz at j=2,8,11,14 (length 5); j=5 is FizzBuzz (length 9); the other eight are
the number (length d+1).  Because n0 == 10 (mod 15) in every segment, the token
class is a function of j alone, identical in all four segments.

`verify_blocks()` below checks every byte of the 32766-byte reference text
against this model.
"""
import numpy as np

SPECIAL = (0, 2, 8, 10, 11, 14)

def A(j):
    return sum(1 for s in SPECIAL if s < j)

def C(d, j):
    return (d + 1) * j + (4 - d) * A(j) + (8 - d) * (j > 5)

def token(n):
    if n % 15 == 0: return b"FizzBuzz"
    if n % 3 == 0: return b"Fizz"
    if n % 5 == 0: return b"Buzz"
    return str(n).encode()

def reference_text():
    return b"".join(token(n) + b"\n" for n in range(1, 6335))[:-1]

def verify_blocks():
    txt = reference_text()
    ok = True
    # prefix = virtual block n0=-5, j=6..14
    for j in range(6, 15):
        n = -5 + j
        off = -25 + C(1, j)
        ok &= txt[off:off + len(token(n)) + 1] == token(n) + b"\n"
    # d=2 (6 blocks), d=3 (60 blocks), d=4 (355 full blocks + 10 tokens)
    for (P, n0base, d, nb) in ((63, 10, 2, 6), (71, 100, 3, 60)):
        for q in range(nb):
            for j in range(15):
                n = n0base + 15 * q + j
                off = (30 if d == 2 else 408) + P * q + C(d, j)
                ok &= txt[off:off + len(token(n)) + 1] == token(n) + b"\n"
    q = 0
    while 1000 + 15 * q <= 6334:
        for j in range(15):
            n = 1000 + 15 * q + j
            if n > 6334:
                break
            off = 4668 + 79 * q + C(4, j)
            want = token(n) + (b"\n" if n < 6334 else b"")
            ok &= txt[off:off + len(want)] == want
        q += 1
    return ok, len(txt)

def per_byte_ops():
    """Op budget of the per-byte (8-stream) renderer, in instruction words.

    A(line) = ALU expression, M = MAU expression; one A and one M can share a
    line.  'gap' lines are nops that cannot carry an ALU expression.
    """
    rows = [
        # stage, ALU, MAU, constants(imm/other), notes
        ("coords  B = 8b (measured 9-op floor)", 12, 0, 4, "baseline L1-L16"),
        ("8 byte positions p = 2c+h", 3, 0, 1, "MEASURED (prim_8lanes)"),
        ("duplicate B + X = B+p", 2, 0, 0, "MEASURED (val_x)"),
        ("X -> f32, u, q, r, v, j, o, n", 4, 12, 10, "MEASURED bit-exact (val_inv)"),
        ("digit: 4 decimals + pack + select", 18, 6, 8, "MEASURED (val_digit), o<=3 exact"),
        ("class / letter selection + newline", 10, 4, 3, "NOT BUILT (estimate)"),
        ("early segments (d=1/2/3) A(j) fix", 16, 6, 6, "NOT BUILT (estimate)"),
        ("pack 8 words -> long word", 6, 0, 1, "MEASURED (prim_8lanes, 6 ALU)"),
    ]
    tot_a = sum(r[1] for r in rows); tot_m = sum(r[2] for r in rows)
    tot_k = sum(r[3] for r in rows)
    return rows, tot_a, tot_m, tot_k

if __name__ == "__main__":
    ok, n = verify_blocks()
    print(f"unified 15-token block model: {'VERIFIED' if ok else 'FAILED'} over {n} bytes")
    rows, a, m, k = per_byte_ops()
    for (stage, ra, rm, rk, note) in rows:
        print(f"  {stage:42s} ALU {ra:2d}  MAU {rm:2d}  const {rk:2d}   {note}")
    print(f"  {'TOTAL (per-byte renderer)':42s} ALU {a:2d}  MAU {m:2d}  const {k:2d}")
    print("  + transfer/DRAM tail (baseline L85-L93): 6 non-hostable lines, 3 hostable")
    print(f"  => imm constants    : ALU {a+k}, MAU {m} -> {a+k+6} words")
    print(f"  => hosted constants : ALU {a}, MAU {m+k} -> {max(a, m+k)+6} words")
    print("     (6 = 4 mandatory tail nops + 2 MV that cannot carry an ALU expression)")
    print("     NOTE: measured ALU counts are HIGHER than the first estimate: the digit")
    print("     stage needs 5 fftoi + a 6-op pack + the shift chain (18 ALU), and the")
    print("     early-segment A(j) correction is not yet built.  The 62-word projection")
    print("     that assumed a 44-ALU renderer did not survive measurement.")
