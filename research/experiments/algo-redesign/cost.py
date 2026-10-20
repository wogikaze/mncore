#!/usr/bin/env python3
"""Word-budget model for two independent FizzBuzz renderers.

Counts *ALU expressions* (the line bottleneck: one ALU group per instruction
word) and MAU expressions (co-issued with ALU, so only a bottleneck if they
exceed the ALU count).  Constants produced by `imm` are ALU expressions.
Transfer/nop words are listed separately.
"""

# ---- common, measured -------------------------------------------------------
TRANSFER_1BLOCK = {           # l1bmd + 2 nops + l2bmd x2 + nop + mvd + mvp
    'l1bmd': 1, 'l2bmd': 2, 'mvd': 1, 'mvp': 1, 'nop': 3,
}
TRANSFER_2BLOCK = {'l1bmd':1,'l2bmd':2,'mvd':1,'mvp':1,'nop':4}
def transfer_words(t): return sum(t.values())

# ---- design A: token-cell (4 cells in 4 cycles, shift/OR, canvas pack) -----
A = [
 ('coordinate o = 16*l2bid|8*(h&1)|(peid&7)|128*(h>>1)|512*(m>>1)', 11, 0, 0),
 ('B=8o, segment d (3 cmp), X=B-S0', 4, 0, 0),
 ('k=floor(X/P) (int->f, fma, fftoi)', 2, 2, 0),
 ('r=X-P*k (f, fma, fftoi)', 2, 2, 0),
 ('j0/off inverse (d=4 closed form; corrections for d<4)', 8, 1, 0),
 ('C(j0+i) & 4 shift amounts (4 cycles)', 6, 0, 0),
 ('n=n0+15k+j (4 lanes)', 3, 0, 0),
 ('digits of 4 tokens: 3 quotients + 3 floors + 3 diffs', 4, 6, 0),
 ('ASCII pack polynomial (3 fma) + bit extract (land)', 1, 3, 0),
 ('special-cell constants (Fizz/Buzz/FB) + blend', 6, 0, 0),
 ('FB 9th byte correction', 3, 0, 0),
 ('shift cells by per-cycle amount (lsl/lsr)', 2, 0, 0),
 ('OR 4 shifted cells via memory round-trip', 5, 0, 0),
 ('canvas pack (8 bytes)', 6, 0, 0),
 ('constants (lane offsets, masks, reciprocals, ASCII)', 8, 0, 8),
]
# ---- design B: per-byte lane (8 lanes = 4 cycles x 2 words) -----------------
B = [
 ('coordinate o', 11, 0, 0),
 ('lane offset vector B+[0..7] (imm x4 + add)', 5, 0, 4),
 ('segment d per lane (3 cmp + 2 add)', 5, 0, 0),
 ('scalar/param select P,S0,n0,s', 6, 0, 0),
 ('k=floor(X/P)', 3, 2, 0),
 ('r=X-P*k', 2, 2, 0),
 ('j inverse (corrections)', 9, 2, 0),
 ('off = u - C(j)', 4, 0, 0),
 ('n = n0+15k+j', 4, 0, 0),
 ('digit: n->f, 3 quotients, 3 floors, 3 diffs, pack, extract', 10, 9, 0),
 ('special char (type mod15 + Fizz/Buzz/FB extract)', 12, 1, 0),
 ('digit/special select', 4, 0, 0),
 ('write chars to fixed canvas 0..7', 1, 0, 0),
 ('canvas pack 8 bytes', 6, 0, 0),
 ('constants', 10, 0, 10),
]

def report(name, rows, transfer):
    alu=sum(r[1] for r in rows); mau=sum(r[2] for r in rows); imm=sum(r[3] for r in rows)
    tr=transfer_words(transfer); mv=2
    pe=max(alu,mau)
    print(f'\n{name}: ALU={alu} MAU={mau} (imm inside ALU={imm})')
    for r in rows: print(f'  {r[1]:3d} {r[2]:3d}  {r[0]}')
    print(f'  PE words ~= max(ALU,MAU) = {pe}; + transfer {tr} (incl. nops) + {mv} MV')
    print(f'  TOTAL ~= {pe + tr + mv}')
    return pe+tr+mv

if __name__=='__main__':
    a=report('A token-cell renderer (1 block/PE)',A,TRANSFER_1BLOCK)
    b=report('B per-byte renderer (1 block/PE)',B,TRANSFER_1BLOCK)
    print('\nTarget: total <= 52.  Budget for renderer given the 2-block tail:')
    print('  52 - 17 (tail incl. pack+transfer) = 35 PE words for renderer+coords')
