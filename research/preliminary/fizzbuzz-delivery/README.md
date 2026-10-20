# A strict lower bound for the final FizzBuzz output delivery (MN-Core 2)

> **THIS IS NOT A LEAN PROOF.** This directory is *preliminary analysis*, kept
> out of `proofs/` on purpose. It argues a bound inside an abstract model with
> Python, exhaustive enumeration and an OR-Tools CP-SAT search. A CP-SAT UNSAT
> answer is not a Lean term and is not a theorem about MN-Core 2 semantics.
> The assembler and emulator measurements quoted here are real observations,
> but the *claim* "at least 8 words are needed" is a property of the model
> defined in this directory. See `proofs/README.md` for the repository rule and
> `docs/formal-semantics-worklist.md` for the Lean track that must eventually
> establish any such bound in the kernel.

**Status of this document:** preliminary analysis, not a Lean proof (see the banner above).  It proves a lower bound on **assembled instruction words** (`j + m`
lines).  It does not modify `problems/`, `tools/`, `docs/` or the accepted answer.

## 0. Results

Let a *word* be one assembled `j` or `m` line (the official score is `j + m`).

* **Theorem A (delivery, full ISA).**  Once the 4096 output long words are
  resident in PE-side storage (GRF/LM/T) and all other memories are zero, at
  least **8 assembled words** are needed to place them in Group 0 DRAM words
  0..4095.  The bound is **tight**: lines 86–93 of the accepted 93-word
  solution are exactly 8 words and deliver the real FizzBuzz block (the full
  program is `ACCEPTED!! score=93 j=91 m=2`).
* **Corollary B (whole program).**  Every program that produces the output has
  **`j + m >= 9`**: one extra word must produce the nonzero output data before
  the PE→L1BM transfer.  A 9-word program does deliver a nonzero constant block
  (`vsm/nine_word.vsm`), so 9 is attained for the relaxed predicate.  For the
  actual FizzBuzz block the accepted solution uses 10 words from its producer
  (line 84) through the last MV (line 93); 9 vs 10 is discussed in §4.
* **Target 1 (DRAM write bandwidth) is vacuous.**  One instruction word can
  write at most **131072 bytes** to Group 0 DRAM (`mvp/n16384`, 16384 long
  words; the assembler rejects `n=32768`).  Hence
  `ceil(32766 / 131072) = 1`.  The binding hop is L1BM→L2BM (2048 long words =
  16384 bytes per word), which is what Theorem A counts.

What is **not** covered: the number of words needed to *compute* the FizzBuzz
values.  The current best solution is 93 words; this document proves only
`j + m >= 9`, so it says nothing about the 52-word target beyond that.  See §7
for the exact scope.

## 1. Problem and counting convention

The challenge writes the FizzBuzz string for 1..6334 to Group 0 DRAM from
address 0.  The testcase contains exactly **4096** `d getd $d<i>n0 1` lines
(addresses 0..4095) and **32766** compared bytes; the last long word has 6
meaningful bytes and its low 2 bytes are don't-care.  Every one of the 4096
expected long words is nonzero (0 zero words; at least 6 nonzero bytes each),
so all 4096 words matter.

`j` = one PE instruction word; `m` = one MV instruction word; `nop` is a `j`
word.  The score is `j + m`, and hazard `nop`s are counted.  The assembler is
`judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat`; the official
gate is `python3 tools/fbverify.py`.

Initial state (judge run, `--offchip-memory-init zero`, no `--dirty`): DRAM,
PDM and the SRAMs are zero; GRF0, GRF1, T and the mask registers are zero; the
only nonzero PE inputs are the fixed-value operands (`$l2bid`, `$l1bid`,
`$mabid`, `$peid`, `$subpeid`, `$msb1`).  All 4096 PEs execute one program.
`d set` is forbidden in a submission and is rejected by the judge.

## 2. The instruction forms that matter

Capacities are long words (64-bit) moved per assembled word.  Sources: SDM
3.5.3, 3.5.8, 3.6.7.8, 3.6.8.21, 3.6.8.3; the `n` limit and hazard gaps are
measured with `assemble3` (`probe_isa.py`, log `logs/probe_isa.txt`).

| direction | instruction | capacity per word |
|---|---|---|
| PE → L1BM | `l1bmd <src> $lb` (only form in this direction) | 64 w/cyc × 4 cyc × 64 L1B = **16384** |
| L1BM → L2BM | `l2bmd $lb $lc` (max of all L1BM→L2BM forms) | 64 w/cyc × 4 cyc × 8 L2BM = **2048** |
| L1BM → L2BM | `l2bm@`, `l2bmr`, `l2bmr2` | 512, ≤2048, ≤2048 |
| L2BM → PDM | `mvd/n512 $lc0 $p0@0` | 512 w/L2B × 8 = **4096** |
| PDM → DRAM | `mvp/n4096 $p0@0 $d0@0` | **4096** (max 16384) |
| L2BM → DRAM | `mvp/n $lc@0.1 $d@0` (one L2B only) | ≤ words in that L2B (512 after 2 `l2bmd`) |
| any → DRAM | all MV forms, see `mv_forms.md` | ≤ **16384** w = 131072 B to Group 0 |

Assembler-verified hazards (`probe_isa.py`):

| producer → consumer (same address) | required gap | probe |
|---|---|---|
| `l1bmd` (PE→L1BM) → `l2bmd` (L1BM→L2BM) | 2 intervening words (SDM 3.6.3.7: 10 cycles / 3 steps) | 1 nop fails, 2 nops OK |
| `l2bmd` (L1BM→L2BM) → MV reading L2BM | 1 intervening word (SDM 3.6.3.1) | 0 nops fails, 1 nop OK |
| `mvd` (PDM write) → `mvp` (PDM read) | 0 intervening words | adjacent OK |
| ALU producer → `l1bmd` reading the same GRF1 address | 1 intervening word (SDM 3.6.3.9) | 0 nops fails, 1 nop OK |
| ALU write and `l1bmd` read in the **same** word | legal, but the read gets the **old** value | verified with a known register |

The body of SDM 3.6.3.1 is missing from the docs export; the second row is
therefore taken from the official hazard checker, which is the authority.

## 3. Theorem A: the 8-word delivery bound

**Setting.**  The 4096 nonzero output long words are already in PE-side
storage; all other memories are zero.  Count every assembled word until they
are in Group 0 DRAM words 0..4095.  The producer of the data is *not* counted
(it is added in Corollary B).

**Lemma 1 (volume into L2BM).**  The 4096 output words occupy 4096 distinct
long-word addresses.  Every L1BM→L2BM instruction writes at most 2048 words
(the maximum, `l2bmd`), and a word written to L2BM covers at most one output
address.  Therefore at least **2** L1BM→L2BM words are needed.  This bound is
independent of reductions: a reduction still needs its input words at the
output address, and one L2BM word writes at most 2048 addresses.

**Lemma 2 (PE→L1BM entry).**  L1BM is written only by `l1bmd` (PE→L1BM); no MV
touches L1BM, and PDM/DRAM start zero.  Nonzero output data must therefore
enter through at least **1** `l1bmd` word.

**Lemma 3 (forced gaps).**  The L1BM→L2BM read of the written address must be
3 steps after the `l1bmd` write, so at least **2** intervening words.  The MV
read of the L2BM data must be 2 steps after the last L1BM→L2BM write, so at
least **1** intervening word.  These 3 words are distinct from the data words
above because the dependencies fix their order.  (The `mvd`→`mvp` pair needs no
gap.)

**Lemma 4 (DRAM write).**  DRAM is written only by MV.
* *Direct `mvp` from L2BM:* one word reads one L2B; after the two L2BM words that
  L2B holds 512 of the 4096 output words, so one direct word reaches only 512
  addresses.  Reaching all 4096 with direct `mvp` needs ≥8 MV words (worse).
* *Via PDM:* PDM is not writable by PEs and starts zero, so it must be filled
  by an MV; one gather (`mvd/n512`, 4096 words) plus one PDM→DRAM write
  (`mvp/n4096`, 4096 words) = **2** MV words.
* *Single reduction word (`mvr`, `mvr2`, `mvr4`):* a k-input reduction needs k
  input words per output address when all k inputs are written (k=2 for
  `mvr2`, 4 for `mvr4`, 8 for `mvr`), while a copy needs 1.  Using an unwritten
  zero as the identity of the reduction does not help: it leaves only the
  other L2B's 512 written addresses, and putting all 4096 desired words in one
  L2B needs 16 L2BM words by itself.  With the two-L2BM-word budget there is no
  single reduction word that reaches 4096 output addresses.  So no single MV
  word beats the gather + write pair.

Hence at least **2** MV words.

**Arithmetic.**  `1 (l1bmd) + 2 (l2bmd) + 3 (gaps) + 2 (MV) = 8`.

**Tightness.**  Lines 86–93 of `problems/challenge/20.fizzbuzz/answer.vsm`:

```
l1bmd $ls0 $lb0        (j)
nop                    (j)
nop                    (j)
l2bmd $lb0 $lc0        (j)
l2bmd $lb32 $lc256     (j)
nop                    (j)
mvd/n512 $lc0 $p0@0    (m)
mvp/n4096 $p0@0 $d0@0  (m)
```

6 `j` + 2 `m` = **8** words.  The fragment `vsm/delivery_tail.vsm` assembles to
exactly j=6, m=2, and the full 93-word program is ACCEPTED, so this 8-word
delivery produces the actual FizzBuzz block.

## 4. Corollary B: `j + m >= 9` for the whole program

Theorem A starts with the data already in PE storage.  In a real solution the
4096 output words are nonzero and every memory starts zero, so at least one PE
instruction word must produce them.  That producer cannot be folded into the
`l1bmd` word:

* a same-word ALU write and `l1bmd` read of the same GRF address assembles, but
  the read gets the **old** value (measured); and
* `$aluf` is the *previous* step's ALU output, so a forwarded producer is also
  an earlier word.

Therefore the producer is an extra word: `j + m >= 8 + 1 = 9`.

**Attainment for the relaxed predicate.**  `vsm/nine_word.vsm` (7 j + 2 m = 9)
uses `imm` to make a full 64-bit constant, forwards it to `l1bmd` with `$aluf`
(no gap), then runs the 8-word delivery.  Official emulator:
`D0 = D2047 = D4095 = 0x1234567812345678`.  So 9 is attained for "deliver a
nonzero 4096-word block".

**For the real FizzBuzz block**, the accepted solution uses 10 words from the
producer (line 84) through the last MV: producer (84), forced gap (85), then
the 8-word delivery.  A 9-word FizzBuzz solution would need a producer whose
full 64-bit result is available on a forwarding operand (`$aluf` or `$mauf`)
in the MSB long word; the pack chain of the current solution does not satisfy
that (the 92-word `$aluf` variant writes only the high 32 bits of every word,
see §8).  This is the one open
question in the 9-vs-10 gap; the argued (not Lean-verified) bound is 9.

## 5. Target 1: the DRAM write bandwidth bound is 1

`mv_forms.md` enumerates every MV form with a DRAM destination.  The largest
transfer count is 16384 long words (the assembler's field overflows at 32768),
so the maximum per instruction word is

* **131072 bytes to Group 0** (`mvp/n16384 $p@0 $d@0` or
  `mvp/n16384 $lc@0.1 $d@0` or `mvr2<op>/n16384`), and
* 524288 bytes total if the form writes all four groups in parallel.

`ceil(32766 / 131072) = 1`, and `ceil(32768 / 131072) = 1` as well.  One
`mvp/n4096` writes the complete 4096-long-word block, so the DRAM hop needs
exactly one MV word and is not the bottleneck.  The binding hop is
L1BM→L2BM (2048 long words = 16384 bytes per word), which produces the 8-word
delivery bound.

## 6. Solver model, exact commands, and outputs

**Model.**  `delivery_model.py` abstracts the delivery as a finite-state
system.  State: whether the PE→L1BM write has happened and when, how many
L1BM→L2BM words have run, when the last one ran, whether PDM has been gathered,
and whether DRAM has been written.  Actions: `NOP`, `L1WRITE`, `L2WRITE`,
`GATHER`, `DRAM_PDM`, `DRAM_L2`; capacities and gaps are the table in §2.  The
goal is DRAM written.  The model is a deliberately conservative **upper
envelope** of the real instruction set: every real L1BM→L2BM form has capacity
≤2048, every real gap is at least the modeled gap, and the direct-copy
alternative (`DRAM_L2`, needing 16 L2 writes) is included.  Reduction-based
DRAM writes are not separate actions; Lemma 4's counting argument shows they
cannot beat 8.

Three independent searches over the same rules:

```
$ python3 research/preliminary/fizzbuzz-delivery/delivery_model.py --check
BFS shortest delivery length: 8
  t= 0  l1bmd(PE->L1BM)
  t= 1  nop
  t= 2  nop
  t= 3  l2bmd(L1BM->L2BM)
  t= 4  l2bmd(L1BM->L2BM)
  t= 5  nop
  t= 6  mvd/n512(L2BM->PDM)
  t= 7  mvp/n4096(PDM->DRAM)
BFS reachable states per layer: [1, 2, 3, 4, 6, 10, 17, 29, 46]

brute force, K=7 (all 6^7 action sequences): NO PLAN
CP-SAT K=7: INFEASIBLE  wall=0.002s branches=0 conflicts=0
CP-SAT K=8: OPTIMAL  wall=0.029s branches=0 conflicts=0
  ... (the 8-word plan above)
ALL CHECKS PASSED: delivery minimum 8 (K=7 UNSAT, K=8 SAT)
```

* **BFS**: exhaustive reachability over the finite abstract state space; first
  goal at layer 8.
* **Brute force**: enumerates all `6^7 = 279936` action sequences; none reaches
  the goal.  (Independent of the BFS/CP-SAT code path.)
* **CP-SAT**: OR-Tools 9.15.6755 (`python3 -c "import ortools; print(ortools.__version__)"`).
  `K=7` returns **INFEASIBLE** (not a timeout; wall 0.002 s) and `K=8` returns
  **OPTIMAL**.  z3 is not installed in this environment; CP-SAT was used as
  the brief allows.

**Capacity evidence from the official tools.**

| command | result | file |
|---|---|---|
| `python3 research/preliminary/fizzbuzz-delivery/run_official.py research/preliminary/fizzbuzz-delivery/vsm/mvp16384.vsm --init unique --dump 0:1 --dump 8191:8192 --dump 16383:16384` | one `m` word writes words 0, 8191, 16383: 16384 long words = 131072 B | `logs/mvp16384.txt` |
| delete one `l2bmd` from the accepted solution | `words=92 mismatches=2048` → one `l2bmd` moves 2048 words | `logs/one_l2bmd.txt` |
| 93-word accepted solution | `ACCEPTED!! score=93 j=91 m=2` | `logs/fbverify_answer.txt` |
| delivery tail `vsm/delivery_tail.vsm` | assembles to j=6, m=2 (8 words) | `logs/verify/delivery_tail.asm` |

## 7. Where this bound does **not** apply

* It is a bound on the **final delivery stage**, not on the computation of the
  FizzBuzz values.  Corollary B gives only `j + m >= 9`; the accepted solution
  spends 93 words.  It does not prove any lower bound near 52.
* The 8-word theorem assumes the 4096 words are already resident in PE-side
  storage in a layout where the 4096 nonzero values are available to `l1bmd`.
  A solution that produces the block in several passes must repeat transfer
  words; the theorem is a lower bound, not an upper bound, for such solutions.
* It assumes the judge's deterministic zero initialization of DRAM/PDM/SRAM
  (no `--dirty`) and no `d set`.  If host-initialized or random nonzero
  memories were allowed, data could be read instead of computed; the challenge
  forbids relying on that.
* The model is an upper envelope, not a full ISA enumerator.  The reduction
  forms `mvr`, `mvr2`, `mvr4` are ruled out at the minimum by the counting
  argument in Lemma 4, not by a CP-SAT action.  All copy forms with smaller
  capacities only increase the count.
* The exact SDM 3.6.3.1 text is missing from the docs export; the 1-step gap is
  taken from `assemble3`'s hazard checker (the official authority).
* The 9-word construction is not a FizzBuzz solution; it only exercises the
  delivery with a constant.  The actual FizzBuzz output needs more compute
  words, and the 9-vs-10 gap for its producer is explained in §4.
* Byte counting: the output is 4096 long words (32768 bytes), with 32766
  compared bytes.  The last word is nonzero (6 meaningful bytes) and must be
  written; its low 2 bytes are don't-care.  This does not change the bound.
* This bound is orthogonal to the ALU-expression count used by the search
  agents (one ALU expression per word; the 93-word baseline has 66 ALU
  expressions in 91 PE words).  The 8-word delivery contains **zero** ALU
  expressions (1 `l1bmd` + 3 `nop` + 2 `l2bmd` + `mvd` + `mvp`), so the ALU
  count cannot improve it.  Any route to 52 words must delete ALU expressions,
  not transfer words; the delivery tail is already minimal.

## 8. Negative results recorded during this work

* **92-word `$aluf` attempt** (`vsm/aluf_92.vsm`): delete the nop between the
  last pack ALU and `l1bmd`, and use `l1bmd $aluf $lb0`.  It assembles
  (j=90, m=2, 92 words) but gives **4096/4096 mismatches**;
  `D0 = 0x310a320a00000000` instead of `0x310a320a46697a7a`.  Cause: the
  1-long-word `l1bmd` takes the MSB 1 long word of the 2-long-word `$aluf`
  (SDM 3.6.8.3), and the current pack assembles the 64-bit word across
  cycles/GRF words, so only the high 32 bits reach L1BM word 0.  This is a
  negative result for the shortcut, not a disproof of all 9-word producers.
* **One `l2bmd` removed** (`vsm/one_l2bmd.vsm`): 92 words, exactly
  **2048 mismatches**.  This measures the 2048-long-word capacity of one
  `l2bmd` and confirms the 2-word requirement.
* **`mvp/n32768`** is rejected by the assembler (bitfield overflow); the
  maximum transfer is 16384 long words.
* **`mvd/n $p0@0 $d0@0`** (the manual's PDM→DRAM distribution form with a
  group suffix on the destination) is rejected by this assembler; the accepted
  syntax is `mvd/n $p0@0 $d0` (no suffix).  The accepted solution's final word
  uses `mvp/n4096 $p0@0 $d0@0`, which the emulator runs as a 4096-word copy.

## 9. Reproduce

```
bash research/preliminary/fizzbuzz-delivery/verify.sh
```

runs, in order: the BFS/brute-force/CP-SAT model, the assembler probes, the
`mvp/n16384` official run, the 9-word construction, the one-`l2bmd` capacity
experiment, the 92-word `$aluf` negative result, the delivery-tail word count,
and `tools/fbverify.py` on the accepted answer.  It ends with
`ALL VERIFICATION STEPS PASSED` (`logs/verify_all.txt`).

Individual commands are listed in §6 and in `verify.sh`.

## 10. Files

| path | contents |
|---|---|
| `README.md` | this document: statement, proof, scope |
| `delivery_model.py` | abstract model; BFS, brute force, CP-SAT |
| `probe_isa.py` | assembler probes for the `n` limit and hazard gaps |
| `run_official.py` | assemble + `gpfn3_package_main`, dump selected DRAM words |
| `mv_forms.md` | every DRAM-writing MV form and its max bytes/word |
| `vsm/delivery_tail.vsm` | the 8-word delivery tail (j=6, m=2) |
| `vsm/nine_word.vsm` | 9-word constant delivery (attains Corollary B's bound) |
| `vsm/one_l2bmd.vsm` | accepted solution minus one `l2bmd` (2048 mismatches) |
| `vsm/aluf_92.vsm` | 92-word `$aluf` negative result (4096 mismatches) |
| `vsm/mvp16384.vsm` | one-word 16384-long-word DRAM write |
| `logs/` | outputs of every command (see `logs/verify_all.txt`) |
