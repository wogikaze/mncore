# Output-construction and transfer stage of the 93-word FizzBuzz solution

Agent: packer. Directory: `research/experiments/packer/`.
Baseline: `baseline-93.vsm` = `problems/challenge/20.fizzbuzz/answer.vsm`
(`fbcheck`: `OK words=93 lines=93 mismatches=0`; `fbverify`: `ACCEPTED!! score=93 j=91 m=2 bytes=3054`).

Everything below marked **[measured]** was reproduced with the official
`assemble3 --instruction-mode flat` + `gpfn3_package_main --offchip-memory-init zero`
(or with the judge for word counts/mismatches). Things marked **[inferred]** come from the
SDM/instruction docs or from arithmetic on measured layouts; the official emulator is
*functional*, not cycle-accurate, so **no cycle throughput was measurable**.

Reproduce:

```sh
cd research/experiments/packer
python3 ../../../tools/fbcheck.py  baseline-93.vsm          # fast: words + dump mismatches
# fbverify resolves its argument against the repo root, so pass the repo-root-relative path:
python3 ../../../tools/fbverify.py research/experiments/packer/baseline-93.vsm   # official judge
python3 run_official.py probes/p08_tag_1block.vsm          # assemble+emu, prints d get dumps
python3 analyze_layout.py out/p08_tag_1block.log 1block    # 4096/4096
python3 analyze_layout.py out/p07_tag_2block.log 2block    # 2048/2048 + 2048/2048
```

---

## 1. What the current output stage actually does (measured)

The 4096 long words of output are produced as **one long word per PE**, all 4096 PEs,
then permuted into linear order by the 4-stage chain

```
$s0 (GRF1, 8 B) --l1bmd--> L1BM[4m+p] --l2bmd x2--> L2BM --mvd--> PDM --mvp--> DRAM
```

Measured facts (all with official dumps; see `out/p03_dump_stages.log`, `out/p06_canvas.log`,
`out/p10_l1bm_dup.vsm`):

| stage | measured content |
|---|---|
| PE word | long word 0 of GRF1 (`$ls0`) = 8 bytes of the string; block tag in MSB half for probes |
| `l1bmd $ls0 $lb0` | L1BM address `64*cycle + 4*mabid + subpeid` = the PE's word. Only cycle 0 matters; cycles 1..3 write the *same* word at +64/+128/+192 because `$ls0` has no increment. 256 long words written per L1B, **64 used**. |
| `l2bmd $lb0 $lc0` + `l2bmd $lb32 $lc256` | `L2BM[64i + 8h + k] = L1BM_h[8i + k]`, i = gather cycle, h = L1B, k = 0..7. Two calls read L1BM 0..31 and 32..63, i.e. one word per PE. |
| `mvd/n512 $lc0 $p0@0` | `PDM[512i + 16(8j + t) + u] = L2BM_t[64i + 16j + u]`, t = 2*group + l2b. The 16-word round-robin across the 8 L2BMs. |
| `mvp/n4096 $p0@0 $d0@0` | linear PDM -> DRAM, 4096 long words = 32768 B. |

Composing them gives the PE -> DRAM block map; it agrees with the formula recorded in
`docs/fizzbuzz-notes/03-machine-model.md` and is here verified word-for-word on all 4096 PEs
(note `g = l2bid>>1` is **2 bits** at bits 5-6):

```
b = 512*(m>>1) + 128*(h>>1) + 32*g + 16*c + 8*(h&1) + 4*(m&1) + p
    g = l2bid>>1 (0..3), c = l2bid&1, h = l1bid, m = mabid, p = subpeid
```

**Evidence**: `probes/p08_tag_1block.vsm` tags every PE with the unique 12-bit value
`(l2bid<<9)|(l1bid<<6)|peid` and runs only `l1bmd / l2bmd x2 / mvd / mvp`. The official emulator
dump matches the formula for **4096/4096** words (`out/p08_tag_1block.log`, analyzed by
`analyze_layout.py`).

Word accounting of the whole output stage (lines 79-93 of `baseline-93.vsm`):

| item | words |
|---|---|
| pack (6 ALU, lines 79-84) | 6 j |
| nop 85 (pack -> l1bmd gap) | 1 j |
| `l1bmd` | 1 j |
| nop 87, 88 (L1BM write -> L2BM read gap) | 2 j |
| `l2bmd` x2 | 2 j |
| nop 91 (L2BM write -> mvd read gap) | 1 j |
| `mvd`, `mvp` | 2 m |
| **total** | **13 j + 2 m = 15 words** |

The 4 nops are *required by the official hazard checker*, not by the functional simulator:
deleting any of them makes the native simulator still say `OK words=92 mismatches=0`
(`logs/summary_fbcheck.txt`) but the official judge's `assemble3` aborts with
`DataRaceError` (`logs/nop_drop_hazard.txt`). This is a trap: **fbcheck alone is not a
sufficient gate for timing changes.**

---

## 2. Every DRAM-writing path (words / bytes / constraints / evidence)

`n` is in long words. "bytes to G0 DRAM" means bytes written to *group 0* DRAM.

| # | path (form) | words | bytes to G0 DRAM | constraints | evidence |
|---|---|---|---|---|---|
| 1 | `mvp/n4096 $p0@0 $d0@0` PDM->DRAM | 1 m | 32768 (4096 words) | n multiple of 64; PDM 4 MiB/group; linear | **used by baseline**; `out/p03` DRAM dump = expected string; fbverify ACCEPTED |
| 2 | `mvd/n512 $lc0 $p0@0` L2BM->PDM combine | 1 m | 0 (fills PDM: 32768 B) | n mult. of 64; reads all 8 L2BMs; 16-word round-robin | **used by baseline**; `out/p09` PDM dump `PDM[0..15]=L2BM_0[0..15]` |
| 3 | `mvp/n4096 $lc0@0.0 $d0@0` L2BM->DRAM single | 1 m | at most 4096 (512 words = one L2B's share) | source is one (group,l2b) L2BM; linear; n mult. of 64 | **built**: `cand/c_direct_l2bm_dram.vsm` -> fbcheck `mismatches=4096`; judge `RESULT MISMATCH pos=32765` |
| 4 | `mvp/n4096 $lc0@.0 $d0` L2BM->DRAM parallel | 1 m | 4096, and only from that L2B's 512 words | writes all 4 groups at once; linear | **built**: `cand/c_direct_l2bm_dram_par.vsm` -> `mismatches=4096` |
| 5 | `mvp/n512 $lc0@0.0 $d0@0` (512-word variant of 3) | 1 m | 4096 | same | **built**: `cand/c_l2bm512_to_d0.vsm` -> `mismatches=4096` |
| 6 | `mvd/n4096 $p0@0 $d0` PDM->DRAM distribute | 1 m | 4096, but consumes 16384 PDM words (4x) | 16 of every 64 words go to G0; needs 4x data to fill G0 | **built**: `cand/c_mvd_only_then_dist.vsm` -> `mismatches=4096` |
| 7 | `mvr2<op>/n64 $lc0 $d0` L2BM->DRAM group reduction | 1 m | 64/unit | arithmetic reduction over both L2Bs of the group (addmaxmin,and/or); cannot copy; depends on L2BM init | not built (doc: 3.5.8.14); not usable: it reduces, and grading forbids relying on non-zero init |
| 8 | `mvr4<op>/n64 $lc0 $d0` inter-group combine+reduce | 1 m | 32/unit (16 per l2b) | reduction over all 4 groups | not built (doc 3.5.8.17) |
| 9 | `mvr<op>/n64 $lc0 $d0` inter-group reduction | 1 m | 16/unit | reduction over all 8 L2Bs | not built (doc 3.5.8.21) |
| 10 | any of 1,3,4,6 with `$di<M>@g` + `nd N` | same + DAR setup | same, but **16-word granularity scatter** | DAR: 1024 entries/group, value = address in 16-long-word units; `M` = start entry, `N` = reuse count | **built**: `probes/p09_dar_scatter.vsm` -> 4 chunks landed at DRAM 0/16/32/48 according to DAR[0..3] (`out/p09.log`) |
| 11 | L1BM -> DRAM, direct | — | — | **does not exist**: `$lb` is not a legal MV source | **built**: `cand/c_l1bm_to_dram.vsm` -> assembler error `bad MV statement 'mvp/n64 $lb0 $d0@0'` |
| 12 | PE -> DRAM direct | — | — | does not exist; PE only reaches L1BM | same as 11 (no operand form) |
| 13 | `d set` | — | — | forbidden by the rules | not built |

Measured throughput (words, not cycles): the baseline moves the whole 32768 B with
**5 instruction words** (1 `l1bmd` + 2 `l2bmd` + 1 `mvd` + 1 `mvp`); with the 3 enforced nops
the transfer tail costs 8 words. The `l1bmd` itself writes 131072 B into L1BM
(4 identical 64-word blocks per L1B, 3 wasted).

Cycle throughput **[inferred]** from the SDM: `mvp` PDM->DRAM 16 words/cycle in-group,
`mvd` L2BM->PDM 1 word/cycle per L2BM, `l1bmd` 64 words per cycle into L1BM, `l2bmd` gather
64 words/cycle. Not measurable here (functional emulator).

---

## 3. Why the 5 MV-path instructions cannot be reduced

Each substitution was built and run:

| change | result | evidence |
|---|---|---|
| drop `mvd`, write DRAM straight from L2BM (path 3/4) | 4096/4096 dump words wrong | `cand/c_direct_l2bm_dram*`, `cand/c_l2bm512_to_d0` |
| drop `mvp`, use PDM->DRAM distribute (path 6) | 4096/4096 wrong (only 16 of every 64 words go to G0) | `cand/c_mvd_only_then_dist` |
| drop second `l2bmd` (only one gather) | 2048/4096 wrong (i=4..7 slots never filled) | `cand/c_skip_gather2` |
| drop first `l2bmd` | 2048/4096 wrong | `cand/c_skip_gather1` |
| drop `l1bmd` | 4096/4096 wrong | `cand/c_skip_l1bmd` |
| drop any of the 4 tail nops | functional OK, **official assembler aborts** | `logs/nop_drop_hazard.txt` |

Why it is structural, not accidental (derived from the measured layout, then verified):

* `l1bmd` is the only PE -> block-memory path; `l2bmd` is the only L1BM -> L2BM path.
* One gather call can move at most 32 words per L1B (`8 words/cycle x 4 cycles`), and 8 L1Bs
  => 256 words per L2BM. The `mvd` can only take 512 words per L2BM (`n512`), and 8 L2BMs
  => exactly 4096 words. So **two gathers are exactly what fills the 8 L2BMs to the 512-word
  level the `mvd` consumes**; one gather leaves half the DRAM region unwritten (measured:
  2048 mismatches).
* The `mvd` is not a "copy" but a **bit permutation**: it maps L2BM address bits
  `[0:4) -> PDM [0:4)`, `[4:6) (=h>>1) -> PDM [7:9)`, `[6:8) (=c) -> PDM [9:12)`, and inserts the
  L2B index `t` at PDM bits `[4:7)`. That is exactly the split the target needs
  (`h&1` at bit 3, `h>>1` at bits 7-8, `g,c` at bits 4-6, `m>>1` at bits 9-11). The gather, by
  contrast, always places the L1B index `h` into **three consecutive bits** (3-5) of the L2BM
  address. No choice of `l1bmd`/`l2bmd` base addresses can split `h` into bit 3 and bits 7-8,
  because the same address is used for all 8 L1Bs. So the `mvd` is the *only* instruction that
  can produce the line order, and a DRAM write must be a second MV.
* `mvp/n4096` (1 m) already writes the whole 32 KB with no per-byte cost, so 2 m is the floor
  (the only way to 1 m would be a single L2BM holding all 4096 words in final order, which the
  gather structure cannot express — see above — and would cost 16 gathers anyway).

---

## 4. The pack: 6 ALU for 8 bytes, and why it is not transfer-replaceable

Measured: the PE's block is 8 string bytes. The canvas in LM0 stores **one character per
32-bit word** (`out/p06_canvas.log`: LM0 words at T = 8 are `0x69,0x7a,0x7a,0x42,0x75,...` =
`izzBuzz\n`; the T register dump is `0x8`). The pack therefore reads 8 canvas words at
`T+0..7` (4 per cycle; `$mt[0,4,0,4]`, ... flat addresses) and builds two 32-bit packed words
with 3 shifts + 3 ORs, writing them to GRF1 words 0/1 with `/1100`
(cycle 0 = bytes 0-3 in the MSB word, cycle 1 = bytes 4-7 in the LSB word). 6 ALU => 8 B, i.e.
0.75 words/byte.

Transfer-side rearrangement cannot replace it:

* every transfer in the chain moves **whole long words** (8 B). The only reorderings available
  are (a) which 64-word L1BM block a PE's word lands in (`l1bmd` base, 64-aligned, same for all
  PEs; `mabdiff` permutes MAB numbers), (b) which 8-word window a gather takes
  (`l2bmd` base, 8-aligned), (c) the `mvd` 16-word round-robin, (d) DAR's 16-word scatter.
  All of them permute whole 8-byte blocks / 16-word chunks; **none of them can reorder bytes
  inside a block**. Since the string is cut at arbitrary byte positions, each 8-byte block must
  be assembled before it enters L1BM.
* `l1bmd` can source LM0 directly (`$lmt...`), which would remove the pack entirely, but the
  canvas would then have to hold the 8 bytes as one long word at `T`; today it holds 8 separate
  words, and one `l1bmd` reads only 1 long word per cycle, so this requires the canvas to be
  re-laid-out (2 or 4 bytes per word). That is a rendering-side change (the canvas/digit path),
  not a transfer change.
* Writes of 4 separate bytes into 4 different L1BM 64-word blocks (one per l1bmd cycle) do not
  help: the gathers/mvd place 16-word chunks, so the 4 bytes would end up in 4 different
  16-word chunks of the output.

Measured DAR cost (why DAR cannot rescue the layout either): `l2bmdars` loads the whole
512-entry DARBUF in **1** word; `l2bmdarw` writes **4** DAR entries per word (1 per cycle).
Scattering the 4096 output words needs 256 DAR entries => **1 + 64 = 65 j words** just to
program the addresses **[measured: 1+1 words program 4 entries and scatter 4 chunks,
`out/p09.log`; 64 steps for 256 entries is arithmetic on that]**, and DAR is per group, so each
L2BM's 512-word copy would need its own table: ~8 x 66 = 528 words **[inferred]**. DAR is a
destination-side 16-word scatter; the `mvd` is a source-side 16-word merge — the merge is the
cheap one.

---

## 5. Retracted claim: 2 blocks per PE saves **zero** renderer words

I originally proposed moving to 2048 PEs x 2 blocks, expecting the unused VLIW cycles to
amortize the renderer. That is wrong, and the numbers below are why.

* The renderer's parallelism is **already saturated in the block dimension**: there are 4096 PEs
  and 4096 output blocks, and the PE->block map is a bijection (measured, 4096/4096). One ALU
  line applies to all 4096 PEs and computes 4096 distinct block values in cycle 0 (cycles 1-3
  duplicate them). A 2-block renderer (2048 PEs, cycles 0/1 for block A and 2/3 for block B)
  also computes exactly 4096 block values per line. Same number of lines.
* So for the 77 renderer j words of the baseline: **0 disappear**. A 2-block renderer needs the
  same 77 lines, plus the tail costs +1 word (see below), i.e. it is a net loss.
* There is also no instruction whose cost is "per active PE set". All five transfer instructions
  are flat per-line costs: `l1bmd` = 1 line whatever it writes (64 or 128 longs per L1B), one
  `l2bmd` = 1 line per 32 words per L1B (hence exactly 2 lines for 4096 words), `mvd` = 1,
  `mvp` = 1. Restricting to `mabid < 8` changes none of them.
* A 4-block version cannot help either: with 4 words/PE the extra two blocks land at DRAM words
  `b+4096`/`b+6144`, outside the 4096 words the testcase dumps (`$d0..$d4095`).

What *is* true, and is kept as evidence only (it has no word benefit):

* the transfer really does support 2 blocks per PE at +1 word. `probes/p07_tag_2block.vsm`
  (hazard-clean, official emulator): long-word 0 -> `b` for 2048/2048, long-word 1 -> `b+2048`
  for 2048/2048.
* a word-access `$s0v` write with all 4 cycles enabled writes GRF1 words 0..3 = long words 0,1
  (`probes/p11_write4words.vsm`, `out/p11`).
* a complete 2-block pack+tail is built and verified (`probes/p12_final_2block.vsm`, hazard
  checker rc=0; `out/p12f.log`): 16 synthetic bytes/PE via the 6-ALU pack with flat per-cycle
  canvas addresses (`$mt[0,4,64,68]`, ...), `l1bmd $ls0v`, gathers at `$lb0`/`$lb64`, `mvd/n512`,
  `mvp/n4096`; `DRAM[b]` and `DRAM[b+2048]` matched 2048/2048 each, all 4096 words distinct.
* its tail cost is 15 j + 2 m = 17 words vs the baseline tail's 14 j + 2 m = 16, i.e. **+1 word**
  (one extra nop: `$ls0v` makes `l1bmd` read long words 0..3, so the hazard checker needs 2 nops
  after the pack instead of 1; measured: 1 nop -> DataRaceError on GRF1 address 2, 2 nops -> rc=0).

Where the idle cycles *do* pay: they are a **values-per-block** resource, not a block resource.
Measured: one line can write 4 arbitrary (char, position) pairs into the canvas
(`probes/p13_flat_canvas_writes.vsm`: `ipassa $r[0,1,2,3] $mt[4,12,20,37]` writes 'A','B','C','D'
to LM0 words 4, 12, 20, 37). Counting the baseline's canvas phase (lines 57-76): **16 lines address
47 position writes**; 7 of those lines address only 1-2 positions (`$mt[0,1,0,1]`,
`$mt[2,3,2,3]`, `$mt4`, `$mt12`, `$mt[17,22,22,22]`, `$mt[27,32,32,32]`, `$mt37`).
Bounds on repacking them at 4 writes/line: the source of a `passa` is one GRF, so only
same-GRF writes can share a line. The GRF0 (letter) group is 13 lines / 39 writes -> ceil(39/4)
= 10 lines; the GRF1 (digit) group is 2 lines / 4 writes -> 1 line. So the ceiling is
**about 4 words** (3 from the letter group, 1 from the digit group), and only if the per-cycle
zero-flush mask `/$imr15` is all-1 on the merged cycles. Not built. This is the
"delete/merge ALU expressions" direction, not a change in the block-to-PE mapping.

## 6. What did not work, and why (all built and run)

| idea | measured result | file |
|---|---|---|
| drop tail nops (all 4, any single, pairs) | native sim OK, official assembler `DataRaceError` | `cand/c_drop_nop*`, `logs/nop_drop_hazard.txt` |
| direct L2BM->DRAM (single & parallel, n512/n4096) | 4096/4096 words wrong | `cand/c_direct_l2bm_dram*`, `cand/c_l2bm512_to_d0` |
| PDM->DRAM distribute as final write | 4096/4096 wrong | `cand/c_mvd_only_then_dist` |
| one gather instead of two | 2048/4096 wrong | `cand/c_skip_gather1/2` |
| no l1bmd | 4096/4096 wrong | `cand/c_skip_l1bmd` |
| L1BM->DRAM instruction | does not exist (assembler error) | `cand/c_l1bm_to_dram.vsm` |
| DAR scatter instead of mvd | works at 16-word granularity but needs 65+ words of table setup and still only sees one L2BM (512 words) | `probes/p09_dar_scatter.vsm` |

## 7. Recommendation

1. Do not spend more effort on the transfer chain: 1 `l1bmd` + 2 `l2bmd` + `mvd` + `mvp` is the
   floor (measured substitutions above), and the 3 nops are enforced by the official hazard
   checker.
2. Do not spend more effort on transfer-side byte rearrangement or DAR: neither can reorder
   bytes inside an 8-byte block, and DAR setup costs more words than the `mvd` it would replace.
3. The idle VLIW cycles are a *values-per-block* resource, not a block resource (section 5):
   there are 4096 PEs for 4096 blocks, so every renderer line already covers all blocks and a
   2-block layout saves 0 words (it costs +1). The one place I could measure visible slack is
   the canvas phase: 16 lines addressing 47 position writes, of which 7 lines address only 1-2
   positions; one line can write 4 arbitrary (char, position) pairs (measured, p13). Because a
   `passa` source is one GRF, the ceiling is ~4 words (GRF0 letters 13 lines/39 writes -> 10;
   GRF1 digits 2/4 -> 1), and only if the per-cycle `/$imr15` flush mask is all-1 on the merged
   cycles. That is the same work as deleting/merging ALU expressions.
4. Keep using `fbverify` (official) for anything that changes timing; `fbcheck` accepts nop
   deletions that the judge rejects.

## 8. File index

```
baseline-93.vsm              copy of the accepted 93-word solution
cand/                        every substitution candidate (assembled + run)
probes/p01..p13*.vsm         official-tool probes (word/half semantics, stage dumps, tags, DAR,
                             2-block pack+transfer tail p12_final_2block.vsm (no word benefit),
                             4-arbitrary-canvas-writes-in-one-line p13_flat_canvas_writes.vsm)
out/*.log, out/*.asm         official emulator/assembler output used as evidence
logs/*.txt, logs/*.err       fbcheck summary, hazard-checker rejections
run_official.py              assemble3 + gpfn3_package_main runner printing d get dumps
analyze_layout.py            checks the PE->DRAM block formula against a DRAM dump
```
