# Architecture / ISA notes (append-only)

Shared notes on the MN-Core 2 hardware structure. Add a new section per agent; do not rewrite
other sections.

---

## isa-analyst — what one instruction word can do, and where the 93 words go

Scope: instruction-level capability of one word (PE word and MV word), bytes per word, and a
word-budget account of `problems/challenge/20.fizzbuzz/answer.vsm` (93 words, j=91 m=2,
`fbverify` ACCEPTED). All raw evidence is in `research/experiments/isa-analyst/` (scripts,
`progs/`, `logs/`).

Tooling: `assemble3 --instruction-mode flat` is the authority for what is legal and for the
word count (`judge.py` counts `j` lines + `m` lines); `gpfn3_package_main
--offchip-memory-init {zero,unique}` plus `d get`/`d getd` is the authority for what a word
actually writes. `runner.py` in the experiment directory wraps both.

### 1. A PE instruction statement is exactly one word, regardless of 4 cycles or expression count

- `PE命令文` (one source line) = 1 `step` = 1 machine word = 1 `j` line (SDM 3.6, 3.6.4).
- Each operand carries 4 cycle addresses (flat `[...]`, or ADRI `v`); those 4 cycles are
  *inside* the one word.
- Measured (`logs/e2_pe_lines.log`, `logs/e2_coissue2.log`):
  - `lpassa $lm0v $ln0v` → `j=1`
  - `lpassa $lm[0,2,4,6] $ln[0,2,4,6]` (4 explicit cycle addresses) → `j=1`
  - 8 co-issued expressions on one line → `j=1`
  - `nop/2` + `nop/3` + 1 PE line → `j=6` (a `nop/n` costs n words)
  - the 93-word answer: 91 PE source lines → exactly 91 `j` lines.
- An MV statement can never share a PE line: `lpassa ...;mvp/n64 ...` →
  `Non PE operation after separator.` (`logs/e2_nop_mv_share.log`). Every MV statement is
  one extra `m` word.

### 2. Issue groups and co-issue capability

SDM table 3.6: one step may issue at most **one expression per group**, and the groups are

| group | expressions |
|---|---|
| `nop` | `nop` (cannot co-issue with anything except `wait`) |
| `noforward` | `noforward` (co-issues with anything) |
| `l2bm` | any L2BM instruction except `l2bmdarw` |
| `l2bmdarw` | `l2bmdarw` (special, can co-issue with `l2bm` in limited cases) |
| `l1bm` | non-turnaround L1BM instructions |
| `l1bm-turnaround` | turnaround L1BM instructions |
| `mau-calc` | `?mfma ?mmul ?vfma ?vmul ?vadd ?vpassa` |
| `mau-mwrite` | `?mwrite` |
| `mau-mread` | `?mread` |
| `alu` | any ALU expression **including `imm`** |
| `wait` | `wait` |

Additional constraints that bit in practice (all measured):
- `alu` + `alu` → `Instruction field conflict detected between 'alu' and 'alu'`
  (`imm` + any ALU op is therefore also illegal: `'alu' and 'immediate'`).
- `imm` + a line that **accesses LM0** → `'immediate' and 'lm0'` conflict (the immediate
  shares instruction bits with the LM0 address field).
- At most **2 of the 3 MAU groups** per step, and the two must use the same precision:
  `calc+mwrite` OK; adding `mread` → `conflict between 'mau+mwrite' and 'mread'`; `fvmul` +
  `dmwrite` → `mau_dmode` conflict.
- Several expressions reading the same PE operand must read the *same region in all cycles*
  (`in_grf1` / `in_grf1` conflicts otherwise).
- No two expressions may write the same PE operand (`out_lm1` / `out_lm1`).

Measured positive combinations (each 1 word):
`ALU+MAUcalc`, `MAUcalc+mwrite`, `ALU+MAUcalc+mwrite`, `\+L1BM`, `\+L2BM`,
`\+noforward`, `\+wait i01`, `\+l2bmdarw` (8 expressions), and the SDM's own 11-expression
example assembles as 2 words with 9 expressions on its second line.

An expression may have **several output operands**: `lpassa $llm0v $ln0v $lls0v $omr1`
(1 word, 3 destinations) and `dmread $lx0 $lr16v $ls16v` (1 word, 2 destinations). This is how
one word writes more than one memory: `lpassa $ls0v $ln8v;l1bmd $ls0v $lb256;l2bmd $lb0 $lc0`
wrote LM1, L1BM and L2BM in one step (`logs/e2_three_mem.dmp`).

### 3. MV: every form costs 1 word; size limit is the same for all forms

Parameter `n` is in long words on the L2BM side (or PDM side for PDM↔DRAM). The encoded field
is `n/16` with 11 bits, and `n` must be a multiple of 64:

- all MV forms: `n = 64·k`, `k = 1..511` → **max n = 32704** (511 long words blocks).
  `n=32752` → `nw must be aligned to the multiple of 64`; `n=32768` →
  `2048 >= 2^11` field overflow (`logs/e1_mv_size_sweep.log`, `logs/mvp_size_sweep.log`).
- Word cost is 1 `m` line for **every** size (n=64 and n=16384 both `m=1`).
- There is **no `mvn128` mnemonic**: `mvn128/n64 ...` → `No valid operation in this line.`
  `/n128` is just a size suffix valid on any form (`mvp/n128 ...` → `m=1`).

#### Which MV forms can write DRAM, and how many bytes per word (measured)

Boundary method: fill PDM with zeros (`mvp/n32704 $lc0@.0 $p0`), run the form at n=32704 over
a DRAM initialised to `unique` (= `0x80000 - addr`), then dump the last written and the first
untouched long word. `logs/e1_dram_extent.log`; parallel-vs-single scope in
`logs/e1_parallel_vs_single.log`.

| form (SDM) | example at max n | max n | longs written / DRAM | bytes / DRAM word | bytes over 4 groups |
|---|---|---|---|---|---|
| `mvp` PDM→DRAM single (3.5.8.2) | `mvp/n32704 $p0@0 $d0@0` | 32704 | 32704 | **261,632** | 261,632 (group 0 only) |
| `mvp` L2BM→DRAM single (3.5.8.7) | `mvp/n32704 $lc0@0.0 $d0@0` | 32704 | 32704 | 261,632 | 261,632 |
| `mvp` L2BM→DRAM parallel (3.5.8.12) | `mvp/n32704 $lc0@.0 $d0` | 32704 | 32704 | 261,632 | **1,046,528** |
| `mvd` PDM→DRAM distribute (3.5.8.24) | `mvd/n32704 $p0@0 $d0` | 32704 | 8176 (n/4) | 65,408 | 261,632 |
| `mvr2<op>` L2BM→DRAM (3.5.8.14) | `mvr2dfadd/n32704 $lc0 $d0` | 32704 | 32704 | 261,632 | 1,046,528 |
| `mvr4<op>` L2BM→DRAM (3.5.8.17) | `mvr4dfadd/n32704 $lc0 $d0` | 32704 | 16352 (n/2) | 130,816 | 523,264 |
| `mvr<op>` L2BM→DRAM (3.5.8.21) | `mvrdfadd/n32704 $lc0 $d0` | 32704 | 8176 (n/4) | 65,408 | 261,632 |
| `mvb`, `mvb2`, `mvb4` | DRAM is source, L2BM is destination | 32704 | **0** | 0 | 0 |
| `mvnop` | — | — | 0 | 0 | 0 |

So a single MV word can write at most **1,046,528 bytes** (parallel `mvp` L2BM→DRAM or
`mvr2`), or 261,632 bytes into one group's DRAM. **L2BM→DRAM `mvp` is legal and works** — the
brief's "直接 mvp 不可" is a *layout* statement, not an ISA one (see §7).

Also verified: `mvd/n512` in the answer gathers 4096 L2BM longs from all 8 L2BMs into group-0
PDM (64 L2BM longs per L2B per unit → 512 PDM longs per unit,
`size/64 = 8` units → 32,768 B in and out), and `mvp/n4096` copies 4096 longs (32,768 B) from
group-0 PDM to group-0 DRAM only (it is the *single-group* form).

### 4. Bytes per PE word (write capacity of one step)

| sink | per word | bytes/word (whole chip) |
|---|---|---|
| `l1bmd <src> $lb<a>` PE→L1BM gather | 64 longs/cycle × 4 cycles = 256 longs **per L1B** (`logs/e2_l1bmd_extent.dmp`: addresses 0..255 written, 256+ zero) | 256 × 64 L1Bs = 16,384 longs = **131,072 B** |
| `l2bmd $lb $lc` L1BM→L2BM gather | 64 longs/cycle × 4 cycles = 256 longs per L2BM | 256 × 8 L2BMs = 2,048 longs = 16,384 B |
| one ALU/MAU 2-long-word expression | 2 longs/cycle × 4 cycles = 8 longs per PE | 8 × 4096 PEs = 32,768 longs = **262,144 B** |

The answer only uses the cycle-0 column of `l1bmd` (its two `l2bmd` read L1BM 0..64), i.e.
**64 longs per L1B = 4096 longs = 32,768 B per PE word**, which is exactly the size of the
required output (32,766 B).

### 5. Bandwidth lower bound (item 3 of the assignment)

- Requirement: 32,766 bytes in group-0 DRAM.
- Max bytes/word over every instruction that writes DRAM: **1,046,528** (`mvp` parallel
  L2BM→DRAM, `mvr2` at n=32704); 261,632 for one group.
- Therefore `ceil(32766 / 1046528) = ceil(32766 / 261632) = **1 word**`.
- Production side: one PE word can push 131,072 B into L1BM (or 32,768 B in the answer's
  cycle-0-only usage) ≥ 32,766 B → **1 PE word**.
- DRAM starts zero in grading and MV cannot create data, so at least one PE word must compute
  the bytes and at least one MV word must move them: combined floor **2 words**.

**The bandwidth bound is 1 word, and even the compute+transfer floor is 2 words — far below
52.** Bandwidth is *not* what makes 52 hard. The binding resource is the ALU issue group:
at most one ALU expression per word (§2), and the current solution has 66 of them (§6).

Scope of this bound: instructions checked are the 20 legal MV operand/form combinations
enumerated in `sweep_mv.py` at n ∈ {16,32,48,64,128,1024,16384,32640,32704,32752,32768}, plus
the 7 DRAM-writing families emulated at n=32704. Not checked: `mvp` PDM→PDM (3.5.8.8), DRAM
indirect `$di`/`nd` forms at max n (same size field, address walk differs), tagged/wait MV
interactions, and reduction opcodes other than `dfadd` (size does not depend on the opcode).

### 6. The 93-word answer: per-stage word account

`python3 census.py answer.vsm` (`logs/answer_census.log`) and `python3 stage_table.py`
(`logs/stage_table.md`). Expression census: **ALU 66, MAU-calc 41, mwrite 1, mread 1,
L1BM 1, L2BM 2, nop 8, noforward 1, MV 2**; 121 PE expressions in 91 PE words + 2 MV words.

| stage (lines) | words | ALU expr | MAU expr | imm expr | imm-only words | nop |
|---|---|---|---|---|---|---|
| S0 prologue constant dance, L1–4 (`dmwrite`/`dmread`/`iinc` → GRF0 1..7) | 4 | 4 | 2 | 2 | 0 | 0 |
| S1 block-coordinate build, L5–13 (`iand`/`ilsl`/`ior` on `$l1bid,$peid,$l2bid`) | 9 | 9 | 0 | 0 | 0 | 0 |
| S2 base/threshold/mask setup, L14–25 (2^23 float trick, `$s28`, `n1=8b+8`, compare masks) | 12 | 10 | 6 | 7 | 4 | 0 |
| S3 digit estimate + Fizz/Buzz selection, L26–49 (reciprocals 1/63,1/71,1/79, `lsub` T-chain) | 24 | 22 | 17 | 10 | 4 | 0 |
| S4 canvas value/position, L50–56 (scroll offset, `fftoi` into T) | 7 | 6 | 4 | 4 | 1 | 0 |
| S5 canvas drawing, L57–77 (T-register character writes, `ladd` position chain) | 21 | 8 | 14 | 0 | 0 | 4 |
| S6 pack, L78–84 (3×`ilsl`+`ior` into `$s0v/1100`, `imm 8`) | 7 | 7 | 0 | 1 | 1 | 0 |
| S7 transfer, L85–93 (`l1bmd`, 2×`l2bmd`, `mvd`, `mvp`) | 9 | 0 | 0 | 0 | 0 | 4 |
| **total** | **93** | **66** | **43** | **24** | **10** | **8** |

Line classes (sums to 93): ALU-only 37, ALU+MAU co-issued 29, **MAU-only 14**, nop 8,
block-only (L1BM/L2BM) 3, MV 2. The 66 words that carry an ALU expression are the hard core;
every other word is a word whose ALU slot is empty.

Waste / head-room:

| bucket | words | comment |
|---|---|---|
| `nop` | 8 | L63,67,71,74 (canvas T/LM0 hazards), L85,87,88,91 (transfer hazards). A `nop` cannot co-issue with anything, so each is a full word. Could be filled with independent ALU work. |
| `imm`-only words | 10 | L14,18,19,20,26,30,31,49,56,78. An `imm` attached to a MAU/L1BM/L2BM line costs **0** extra words (`imm` is an ALU expression; it just needs the ALU slot free and no LM0 access). 14 MAU-only lines with free ALU slots exist. |
| MAU-only lines | 14 | L17,21,40,41,50,60,61,64,65,68,69,72,75,76 — one expression per word with the ALU slot idle (L40/L41 write LM0 and L60 writes `$lm0v`, so those 3 cannot host an `imm`; the other 11 can). |
| block-only lines | 3 | L86 `l1bmd`, L89/90 `l2bmd` (mergeable into ALU lines in principle). |

Consequences for the 52-word target:

- With the *current* instruction mix, the floor is **66 (one ALU per word) + 2 MV = 68
  words**, provided all 43 MAU expressions, the L1BM/L2BM work and the 10 constants are
  co-issued into ALU lines and all 8 `nop`s are removed/filled. So 93 → 68 is, in principle,
  a pure scheduling problem (the 25 non-ALU words are the slack).
- Reaching **52 requires ALU 66 → ≤ 50** (16 fewer ALU expressions), because 52 − 2 MV = 50
  ALU-bearing words. That is the real barrier; transfer and bandwidth are not.

### 7. Corrections to prior claims

- "転送短縮: 直接 `mvp` 不可" — `mvp` L2BM→DRAM exists (SDM 3.5.8.7/3.5.8.12) and was
  executed here at n=32704 (`logs/e1_dram_extent.log`). What fails is the *byte layout*: the
  93-word solution's L2BM content is in `l2bmd` interleave order (8-long chunks per L1B), not
  in output order, so a direct `mvp` would emit the wrong permutation; the `mvd` gather is
  what performs the permutation. The 2-word chain (mvd+mvp) is therefore a *layout* choice,
  not an ISA limit — but with 4096 output longs spread over 8 L2BMs (512 longs each), mvd is
  the only single-instruction gather to one group, so 2 MV words remain the practical floor.
- "mvn128" does not exist as a mnemonic; only `/n<size>` on the standard forms.
- The answer's last `mvp/n4096 $p0@0 $d0@0` is the single-group form: it writes **32,768 B to
  group 0 only**, not to all four groups (verified: `logs/e1_parallel_vs_single.log`).
- Transfer floor for the current data layout is 5 words, not 2: `l1bmd` (PE→L1BM, 1 word) +
  2×`l2bmd` (256 longs per L2BM per word, need 512) + `mvd` (gather 4096) + `mvp` (to DRAM).
  The answer uses exactly these 5 + 4 `nop` hazard spacers.

### 8. Evidence index (`research/experiments/isa-analyst/`)

- `runner.py` — assemble + emulate + dump helper; `sweep_mv.py`, `boundary_tests.sh`,
  `probe_lines.py`, `probe_coissue.py`, `probe_coissue2.py`, `probe_imm.py`, `probe_mread.py`,
  `census.py`, `stage_table.py`.
- `logs/e1_mv_size_sweep.log`, `logs/mvp_size_sweep.log` — size limits / 1 word per MV.
- `logs/e1_dram_extent.log`, `logs/e1_parallel_vs_single.log` — DRAM bytes per MV word,
  group scope.
- `logs/e2_l1bmd_extent.dmp` — 256 longs per L1B from one `l1bmd` word.
- `logs/e2_three_mem.dmp`, `logs/e2_multiwrite.dmp` — one word writing several memories.
- `logs/e2_pe_lines.log`, `logs/e2_coissue.log`, `logs/e2_coissue2.log` — co-issue matrix,
  word cost of a line, 4-cycle packing, 8-expression line.
- `logs/e3_imm.log`, `logs/e3_mread.log` — imm/constant economics, mread co-issue.
- `logs/e2_nop_mv_share.log` — `nop/n` = n words; MV cannot share a PE line.
- `logs/answer_census.log`, `logs/stage_table.md` — the tables above.
- `logs/answer.asm`, `logs/answer.asm.err` — assembled 93-word answer (91 j + 2 m).
