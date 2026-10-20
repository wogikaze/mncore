# T-chain exact semantics and closed-form attempts

Work dir: `research/experiments/digit-closedform/`
Baseline: `problems/challenge/20.fizzbuzz/answer.vsm`, 93 words, `words=93 mismatches=0`.
All claims below are checked by `verify_chain.py` on all 4096 blocks
(`chain_data.csv`, produced by `collect_chain.py`).

## 1. What the "11-ALU chain" actually is

The chain is source lines 42–48.  Classified with `mncompile.machine.unit_of`:

| line | instruction | unit |
|---|---|---|
| 42 | `lsub $lr18 $ls132 $omr1` | ALU |
| 43 | `fvadd $t $lr104 $t/$imr1; lsub $aluf $ls4 $omr1` | MAU + ALU |
| 44 | `fvadd $mauf $lr104 $t/$imr1; lsub $aluf $ls130 $omr1` | MAU + ALU |
| 45 | `fvadd $mauf $lr104 $t/$imr1; lsub $aluf $ls134 $omr1` | MAU + ALU |
| 46 | `fvadd $mauf $lr104 $t/$imr1; lsub $aluf $ls134 $omr1` | MAU + ALU |
| 47 | `fvadd $mauf $lr104 $t/$imr1; lsub $aluf $ls4 $omr1` | MAU + ALU |
| 48 | `fvadd $mauf $lr104 $t/$imr1; imm f"0.01" $lr74` | MAU + ALU (imm) |

So the chain is **6 ALU expressions (the lsubs) + 6 MAU expressions (the
fvadds)**, not 11 ALU.  The "11" in the notes counts 6 lsub + 5 of the six
fvadds.  Since the binding resource is the ALU issue group, deleting the whole
chain saves **6 ALU**, not 11; the six MAU slots are not binding.  This is the
single most important correction for the 50-ALU budget.

It occupies six PE words (42–47) plus the MAU slot of line 48; line 48 also
carries the ALU `imm 0.01`, which is needed elsewhere.

## 2. Exact input/output relation

Notation, all verified over the 4096 blocks:

```
s0   = 8*b                       (byte position of the block in the output)
w    = s4                       (digits(n)+1 for the number containing s0)
     = 2 if s0 < 32, 3 if 32 <= s0 < 408, 4 if 408 <= s0 < 4672, 5 otherwise
C_w  = 8, 13, 66, 599            (for w=2,3,4,5)
M    = 8*w + 39                  (length of one 15-number period)
n1   = s0 + C_w
r18  = n1 mod M                  (this is the value in GRF0 long word 18)
s4   = w, s128 = w+3, s130 = w+5, s132 = w+8, s134 = w+10
```

The six comparisons (lsub, 64-bit, flag nibble is 0xf/0 per cycle) are

```
D0 = r18 - s132        = r18 - (w+8)
D1 = D0  - s4          = r18 - (2w+8)
D2 = D1  - s130        = r18 - (3w+13)
D3 = D2  - s134        = r18 - (4w+23)
D4 = D3  - s134        = r18 - (5w+33)
D5 = D4  - s4          = r18 - (6w+33)
m_i = [D_i >= 0]       (1 for i < k, 0 otherwise)
```

Therefore

```
k = #{ i in 1..6 : r18 >= T_i }
T_i = w+8, 2w+8, 3w+13, 4w+23, 5w+33, 6w+33
k in 0..6
```

The six `fvadd $t $lr104 $t/$imr1` add the float 2.0 to T under mask `$imr1`
(the OMR1 entry just produced by the corresponding lsub).  Before the chain
`T = 0x4b000000` (float 2^23) in every word; afterwards

```
T = float with bit pattern 0x4b000000 + 2*k
```

for all four cycles (the debug `$lt` values are identical in cycles 0..3).
T is used only as an address (`T`-indirect LM0) until L77, where it is
overwritten with r18 for the final pack.  Its low 7 bits are 2*k.

The threshold gaps in r18 are `w, w+5, w+10, w+10, w`, which is why the
sequence is *almost* arithmetic with step w+5 but not exactly.

## 3. The tempting closed form and why it fails

Because `T_i = i*w + c_i` with `c = 8,8,13,23,33,33`, and because
`r18 = n1 mod (8w+39)`, the map `r18 -> k` is a monotone step function for
each w.  The natural residue-index idea is:

* `r = r18 >> 3` is the field index in the period (`r = n mod 15`);
* `k` is a function of `r` *alone*: `0,0,1,2,2,3,3,3,4,4,4,5,6,6,6` for r=0..14;
* so T could be looked up with `llsr` + `lpassa $lmtBase`.

Numerically this fails because **r18 is reduced modulo M**: for large
residues r18 wraps, so `r18 >> 3` is not r.  Example: w=4, n=100 has r=10,
r18=48, `r18>>3 = 6`, whose residue-table entry is k=3 instead of k=4.
Over all blocks the residue table indexed by `r18>>3` gives the wrong k for
**3010 / 4096** blocks (mostly w=5).  The table candidate built this way
(`cand_table_keep51.vsm`) is 91 words but has **2718 mismatched output long
words**; the broken words are a subset of the 3010 blocks with a wrong
predicted k (some wrong k still happen to render the same bytes).  See
`analyze_candidate.py` for the exact list and the per-block
`(r18, j, w, true k, predicted k)` table.

The next natural fix, a w-dependent table indexed by `j = r18>>3`, also fails:
even with the correct k at `8*j`, 1240/4096 blocks change k inside the same
8-byte block (162 for w=4, 1067 for w=5).  Using `r18>>2` reduces the
within-block splits to 484 but needs 4*20 = 80 table entries; `r18>>1` still
has 166 splits and needs 4*40 = 160 entries.  A direct table over r18 needs
about 79 entries (one value per byte position).  Each MAU `fvadd` writes only
four LM0 words, and the only free MAU slots are the six chain lines plus the
non-imm ALU-only lines 16 and 37, so at most ~32 table words can be built
without adding ALU expressions.  A w-dependent 40-entry table (4 w x 10 j)
is therefore not reachable inside the current ALU budget.

## 4. Searches for an arithmetic closed form (all negative)

Over all 4096 (r18,w) samples, no exact formula of the following classes was
found (brute force, clamped to 0..6):

* `floor((r18 + a)/b)` for `a in [-40,40]`, `b in [2,30]`;
* `floor((r18 + a)/(w+b))` for `a in [-20,20]`, `b in [1,15]`;
* `floor((r18+a)/p) - floor((r18+b)/q)` for `p,q in {w, w+5, w+10, 2w,
  2w+5, 2w+10, 5, 10, 15, w+15}` and small offsets;
* min/max of two affine floors over a wide range.

The thresholds are not equally spaced, so no single floor/round can be exact.
The gap pattern `w, w+5, w+10, w+10, w` would need a piecewise construction
(select among three thresholds by a comparison), which needs a 0/1 data value
from a comparison; the ALU produces flags in OMR, not data, so a branchless
select costs at least 2 ALU per select and does not beat the six serial
subtractions.

## 5. What was measured

| candidate | words | mismatches | ALU expressions | note |
|---|---|---|---|---|
| baseline | 93 | 0 | 66 | unchanged |
| `cand_table.vsm` | 90 | 3673 | 61 (nominal) | L51 removed; **official assemble3 rejects it** (exit -6) |
| `cand_table_keep51.vsm` | 91 | 2718 | 62 (nominal) | legal under assemble3; table index still wrong |

The nominal ALU counts of the table candidates are *not* a usable win: the
table indexing is wrong, and fixing it needs either a per-w table (too many
words) or an extra correction step (more ALU than the six lsubs).

## 6. Reproduction

```sh
cd research/experiments/digit-closedform

# collect per-block chain inputs/outputs for all 4096 blocks (~1.4 s)
python3 collect_chain.py

# prove the exact relation over all blocks
python3 verify_chain.py

# rebuild the broken 91-word table candidate and measure it
python3 build_table_candidate.py
cd ../../..
python3 tools/fbcheck.py research/experiments/digit-closedform/cand_table_keep51.vsm
python3 tools/fbverify.py research/experiments/digit-closedform/cand_table_keep51.vsm

# enumerate which output words break and why
cd research/experiments/digit-closedform
python3 analyze_candidate.py cand_table_keep51.vsm
```

`verify_chain.py` prints `failures: none`, `r18 values where k depends on w: 32`,
and `residue-table indexed by r18>>3: 3010/4096 blocks wrong`.

## 7. Files

| file | purpose |
|---|---|
| `collect_chain.py` | inserts `d get` probes at L41/L48 for all 4096 blocks; writes `chain_data.csv` |
| `chain_data.csv` | block index, coordinates, r18, s4/s128/s130/s132/s134, T after L48 |
| `verify_chain.py` | asserts r18=n1 mod M, the s-tuple relations, k=threshold count, T=2^23+2k on all blocks |
| `trace_regs.py` | generic per-block register/memory tracer (native sim) |
| `patch_chain.py` | old helper that replaces L42–48 with an arbitrary body |
| `build_table_candidate.py` | builds `cand_table.vsm` / `cand_table_keep51.vsm` (broken, lower word count) |
| `analyze_candidate.py` | lists broken DRAM words and the (r18,j,w,true k,predicted k) diagnosis |
| `official_trace.py` | trace helper using the official emulator (copy of `docs/fizzbuzz-notes/trace.py` with fixed paths) |
