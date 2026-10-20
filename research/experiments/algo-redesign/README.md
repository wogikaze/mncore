# Independent FizzBuzz algorithm — design, models, and word budget

Agent: algo-redesign. Directory: `research/experiments/algo-redesign/`.
Baseline (not used for derivation): `problems/challenge/20.fizzbuzz/answer.vsm` = 93 words
(j=91,m=2). The 93-word source was read only **after** the structures below were derived;
the transfer mapping here was re-derived and agrees with the measured layout.

## 1. Problem structure (re-derived)

For n=1..6334, token T(n) is `str(n)`, `Fizz`, `Buzz` or `FizzBuzz`, followed by `\n`
(not after 6334).  Total 32766 bytes = 4096 long words.

Segments (digit width d), with measured stream offsets:

| d | n range | first token byte S0 | tokens per 15-block P | block size |
|---|---|---|---|---|
| 1 | 1..9 (prefix) | 0 | -- (9 tokens only) | -- |
| 2 | 10..99 | 30 | 63 | 63 B |
| 3 | 100..999 | 408 | 71 | 71 B |
| 4 | 1000..6334 | 4668 | 79 | 79 B |

Within a 15-token block starting at n0 (n0 in {10,100,1000}, n0 mod 15 = 10), cell j=0..14
has type and length

```
j:      0    1    2    3    4    5    6    7    8    9   10   11   12   13   14
type: Buzz  num Fizz  num  num   FB  num  num Fizz  num Buzz Fizz  num  num Fizz
len:     5   d+1   5   d+1  d+1   9   d+1  d+1   5   d+1   5    5   d+1  d+1   5
```

The cumulative offset is `C_d(j) = (d+1)*j + (4-d)*A(j) + (8-d)*[j>5]`, where
A(j) = #{0,2,8,10,11,14} < j.  C_4(j) = 5j + 4[j>5].

A word at byte B = 8*b covers up to **4 consecutive tokens** (worst case d=2: 3-byte
numbers).  d=4 words span at most 3 tokens, but words that start inside the 9-byte
FizzBuzz cell (j=5) can span 4.

Verified by `model.py`: build each 8-byte word as
`OR_i (cell_i >> 8*(C(j0+i)-r))` from four consecutive left-aligned cell values
(a 9-byte FizzBuzz cell is kept in 128 bits).  **4096/4096 words match the official
testcase expectations** (the 4 prefix words are special-cased in the model; the last
2 bytes are don't-care and are zero).

## 2. Two independent renderer designs

### A. Token-cell renderer (4 tokens in 4 VLIW cycles)
Per PE: compute block b -> B -> segment -> (k, r) -> starting cell j0 and offset off;
compute the 4 consecutive cell texts in the 4 cycles (digit quotients/floors are the same
opcode sequence for all 4 cycles); shift each cell by `8*(C(j0+i)-r)` and OR the four
shifted cells; pack/transfer.  Position/`C` data for the 4 cells is per-cycle, so one
instruction supplies all four.
Estimated ALU: **71** (see `cost.py`), of which coords 11, constants 8, index/inverse 15,
digit+special 14, assembly 13, pack 6.

### B. Per-byte renderer (8 or 16 independent byte positions in parallel)
Per PE: compute B, then for each byte position i compute X=B+i and evaluate the per-byte
formula directly: `k=floor((X-S0)/P)`, `u=X-S0-Pk`, `u'=u-4[u>=34]` (d=4),
`j=u'//5`, `off=u'-5j`, `n=n0+15k+j`, then char = digit / Fizz / Buzz / FizzBuzz.
Verified for the d=4 segment by `model2.py`: **3512/3512 d=4 words match**.
The 8 positions are 4 cycles x 2 32-bit lanes; fixed canvas positions mean no per-PE T.
Estimated ALU: **92** (see `cost.py`), of which digit+special selection is 22-26 and
lane-offset constants ~4-10.  The inverse for d=2/3 needs 1-2 correction steps
(error distribution measured: d=2 correction 0/1/2 occurs 27/27/9 times over 63 phases;
d=3 0/1 occurs 61/10 times; d=4 needs no correction).

## 3. Measured / verified facts used

* Transfer tail (measured by packer, re-verified here): 1 `l1bmd` + 2 `l2bmd` + `mvd/n512`
  + `mvp/n4096`, with 3 hazard-checker nops = 8 words; +2 MV = 10 words total for the
  1-block output.  The 2-block variant is 15 j + 2 m = 17 words (one extra nop).
* PE -> DRAM block index (verified against the measured formula):
  `b = 512*(m>>1) + 128*(h>>1) + 16*l2bid + 8*(h&1) + (peid&7)`,
  where h=l1bid, m=mabid, l2bid=2*group+l2b, peid=4*mab+subpeid.
  Equivalent: `b = (l2bid<<4)|((l1bid<<3)&8)|(peid&7)|((l1bid&6)<<6)|((mabid&30)<<8)`.
  Coordinate ALU ~11-12 + ~6-8 constants (the 93-word solution uses 12 ALU + shared imm).
* `imm i"x"` with flat addresses `$s[a,b,c,d]` writes a **single 32-bit word** per cycle at
  word address a/b/c/d (the other word of the long word stays 0); to fill both lanes of a
  long word with the same constant, write flat `[a,a+1,...]` with a 2-cycle mask.
  (Measured with `probe2.py`: `imm i"4" $s[0,...]/1000` -> long word 0 = `0x00000004_00000000`.)
* ALU is the line bottleneck: one ALU expression per instruction word; MAU/matrix/L1B/L2B/
  MV co-issue.  So renderer lines ~= max(ALU, MAU), plus non-pairable MV/nop lines.

## 4. Word budget (from `cost.py`)

```
A token-cell 1-block : ALU 71, MAU 14 -> PE 71 + transfer 8 + MV 2 = ~81 words
B per-byte   1-block : ALU 92, MAU 16 -> PE 92 + transfer 8 + MV 2 = ~102 words
existing 93-word     : ALU 66, MAU 41 -> 91 j + 2 m = 93 (66 ALU is the floor there)
target 52            : requires <= 50 ALU; with the 1-block tail (10 words) the whole
                       renderer including coords and pack must fit in ~42 ALU.
```

The 2-block tail (17 words) leaves only **35 PE words** for the renderer+coords if 52 is
the target, because the pack is inside the tail's 15 j.

## 5. Why the 2-block tail does not automatically halve the renderer

The baseline uses all four VLIW cycles as the four digit candidates of **one** block
(`$ls20v` then `ipassa $s[20,22,21,23] $mt[...]`; the docs/notes confirm "est..est+3 are
computed in parallel in the 4-cycle lanes").  Splitting cycles 0/1 vs 2/3 for two blocks
gives only **two candidates per block**, so the digit-render and canvas-write stages must
run twice (16 -> ~32 and 8 -> ~16 ALU), while only the scalar chain (coords, block/phase,
T/positions) is shared.  Rough count: constants 24 + shared scalar ~20 + doubled digit 32
+ doubled canvas 16 + pack 6 = ~98 ALU, i.e. no better than the current 66.  The 2-block
tail is free on the transfer side but is *not* a 2x renderer win by construction; it
becomes a win only if a renderer is found whose per-block candidate count is <= 2.
(The pack itself does amortize: 6 ALU for 16 bytes instead of 12.)

## 6. What was tried and failed / abandoned (diagnostics)

| idea | result |
|---|---|
| closed-form inverse cell index `j = ceil((e(j0)-rem)/s)` | exact for d=4; d=3 10/71 phases wrong, d=2 36/63 wrong -> needs correction steps (costed). |
| 79-entry phase table in LM0 via `l1bmd` distribute | needs P+8 words per segment; 4 words/instruction load -> ~20+ words/segment; not viable. |
| packed 4-bit inverse table + shift | 5 long words/segment and per-lane word selection (r>>4 varies inside a word) -> ~10 ALU + build cost; worse than arithmetic. |
| FMA magic `(F>>32)&15 == n%15` with base=0x452A0000, K=0x4488A854 | **not reproduced**: float32 `n*K+base` low-4 bits do not equal n%15 for any n (5933/6334 wrong); double variants and bit-position variants also fail. Treated as unusable. |
| per-byte lane offsets `B+[0..7]` | needs a per-PE constant vector 0..7 in GRF; `imm` can only repeat one 32-bit literal, so 4-8 imm lines or arithmetic. (Costed in design B.) |
| 4 tokens per PE (4 cycles) | transfer supports only 2 blocks/PE usefully; 4 blocks land at b+4096/b+6144 outside the dumped region. |
| direct L2BM->DRAM / DAR scatter / drop mvd | independently re-confirmed by packer: 4096/4096 wrong (not re-run here). |

## 7. Files

```
model.py     token-cell model; verifies 4096/4096 words (d>0 segments; prefix special-cased)
model2.py    per-byte d=4 model; verifies 3512/3512 d=4 words
cost.py      ALU/MAU word-budget model for designs A and B
probe2.py    native-simulator probe helper (dumps GRF/L1BM/L2BM/PDM/DRAM)
dram.py      run a VSM snippet and compare its 4096 DRAM words with the testcase
t_coord*.vsm coordinate/transfer experiments (mapping verified, see below)
```

`t_coord2.vsm` writes `8*b` per PE through the transfer tail and, with a `nop` inserted
before `mvp`, produces the block mapping; it was used to confirm the address algebra.
(The 93-word solution's coordinate stage also depends on dmwrite/dmread setup, which is
why the bare copy of its lines is not a standalone test.)

## 8. Conclusion

Both independent designs are correct at the Python model level (all 4096 words for A,
all 3512 d=4 words for B) but need **~71 and ~92 ALU** respectively versus the <= 50
budget.  The dominant cost is not the transfer and not arithmetic throughput; it is the
per-word variable-length stream inversion plus Fizz/Buzz/FizzBuzz classification, which
the 93-word canvas design already performs in ~42 non-constant ALU.  Reaching 52 needs a
renderer whose per-block candidate count is <= 2 (so the 4 cycles can serve two blocks)
and whose constants/index chain are generated outside the ALU group.  I did not find such
a renderer; the independent designs land around 70-80 words, i.e. better than 93 is
plausible but 52 is not demonstrated.

## 9. Refined 2-block analysis (correction to §5)

The 4 VLIW cycles are 4 **independent candidate slots**.  A 2-block renderer helps only
if one block needs at most 2 candidates, so that cycles 0/1 serve block A and 2/3 block B.
The prior notes (`docs/fizzbuzz-notes/10-53line-design.md`, addendum) say:
"est..est+3 are computed in parallel in the 4-cycle lanes; reducing candidates does not
reduce instructions in the 1-block design (lanes idle), but 4->2 is possible for most
words" and "words with t>=584 (d=4) span at most 2 fields; only t<51 (n<100) needs 3".
So for the d=4 domain (3512/4096 words) a **2-candidate renderer is possible**, and with
2 blocks per PE the candidate stages do not double; they are amortized over two blocks.

Budget with the 2-block tail (tail = 17 words *including* the 6-ALU 16-byte pack):

```
coords (shared, b_A and b_A+2048 in different cycles)      12 ALU
constants (imm)                                            24 ALU   <- removable
position/candidate chain (shared, 4 cycles = 2 blocks)     16 ALU
canvas writes (shared)                                      8 ALU
pack (in tail)                                              6 ALU
tail transfer + nops + 2 MV                                11 words
------------------------------------------------------------------
total with imm constants:   12+24+16+8 + 11+6 = 77 words
total if constants are MAU-generated (24 -> 0 ALU):        12+16+8 + 17 = 53 words
```

This is the concrete route to ~53: **2-candidate 2-block renderer + all imm constants
produced by MAU/FMA chains (co-issued, zero ALU lines)**.  It matches the prior diagnosis
that the 24 `imm` constants and the 11-ALU position chain are the two removable stages.
Below 52 needs ~1-2 more words (e.g. fold one scalar op into a MAU chain or shave the
coordinate setup).  My independent token-cell/per-byte renderers (§2) cannot use this
because they are not candidate-parallel; they need one instruction per byte/cell stage
regardless of the number of cycles.

Caveat: the 584 words of block A with d<4 may need 3 candidates (prior note: t<51).  With
2 blocks and 2 candidates each, those words would be wrong unless a masked correction pass
is added (a 3rd candidate for block A only).  The cost is a small number of extra
instructions; it is not free, and it is the main correctness risk of the 2-block plan.

## 10. Next implementation plan (if the 2-candidate hypothesis is accepted)

1. Keep the measured 2-block tail (`probes/p12_final_2block.vsm`): canvas chars at
   absolute LM0 words 0..7 (block A) and 64..71 (block B), pack with
   `$mt[0,4,64,68] ... $mt[3,7,67,71]`, `l1bmd $ls0v`, `l2bmd $lb0/$lb64`, `mvd/n512`, `mvp`.
2. Compute `b` once (12 ALU, §3) and `b+2048`; put `8b` in cycles 0/1 and `8(b+2048)` in
   2/3 with one masked add.
3. Position chain: per-cycle `T` already exists; drive it with block A in cycles 0/1 and
   block B in 2/3.  The chain is the same opcode sequence, so the 2-block cost equals the
   1-block cost (this is where the win is).
4. Render digits with **2 candidates per block** (only possible because d=4 words span at
   most 2 fields); the 2 blocks then fill all 4 cycles.  For the 584 block-A words with
   d<4, add a masked 3rd-candidate correction pass and measure the extra words.
5. Replace every `imm` constant by an MAU/FMA chain (start from a single `imm` of 1.0 and
   build 2,3,4,...,0.1,0.01,0.001,..., char base 0x4b000000+code).  This is where the 24
   ALU lines go to ~0; it requires allocating the chain results across GRF0/GRF1 so that
   no instruction reads two addresses of the same file (the failure mode the prior notes
   hit: "GRF0 port conflict").
6. Gate every step with `tools/fbasm.py` (hazard checker) and `tools/fbverify.py`; `fbcheck`
   alone accepts nop deletions that the official assembler rejects.

## 11. Measured MAU-constant caveat

Tested `MAU constant generation` on the native simulator (`probe2.py`):
one `imm f"1.0"` + 6 co-issued MAU ops produced 2.0/3.0/4.0/8.0/9.0 exactly
(`GREG1` dumps 0x4000.., 0x4040.., 0x4080.., 0x4100.., 0x4110..).  So it works and each op
must respect the "no two different addresses of the same register file" rule
(`fvmul $ls0 $ls4` is rejected; copy one operand to GRF0 via `fvpassa` first).

Important budget consequence: an MAU op still occupies one instruction word.  It is free
only if the design has at least that many ALU expressions to pair it with.  Replacing 24
`imm` ALU lines by 24 single-lane MAU ops does **not** reduce the word count (it changes
the bottleneck from ALU to MAU).  The win requires packing 2-4 constants per MAU op
(fv 2 lanes / hv 4 lanes) or folding them into existing MAU chains.  With ALU ~40 and
MAU ~44 the line count is MAU-bound at ~44 + tail 17 = ~61, not 53.  A 53-word design must
therefore keep **both** ALU and MAU <= ~45 and pack constants into lanes.
