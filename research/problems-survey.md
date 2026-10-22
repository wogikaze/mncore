# Problems survey — Phase 0 routing

Date: 2026-10-21 (JST) / 2026-10-20T15:27Z. Scope: all 25 `problems/challenge/*/`
problems, plus a brief note on the 48 MNIST problems in `problems/`.
I did not edit any shared files; scratch scripts and raw data are in
`research/experiments/survey/`.

This is a survey, not a proof. The only hard gate measured here is
`lake build ProofsLean`, which I ran from `proofs_lean/`: **Build completed
successfully (900 jobs), exit 0**, with two unused-`simp` warnings in
`WelcomeWholeMachineOptimal.lean`. `check.py` was not run; per the task brief it is stale-evidence-red, so it was
not used as a gate.

## 0. Bottom line

- **Cheapest new certifications (my ranking):** `3.a-plus-b`, `2.plus-two`,
  `5.abs`, `24.log2`, `8.fle`, then `12.convert-endian` (correctness already
  formalized; only the bound-3 lower bound remains). `4.mul7` has a nearly
  complete lower-bound shell but is **blocked by a float-model gap** (FTZ /
  subnormals); see §1.4. The full 25-row ranking is in §5.
- **`1.plus-one` is the baseline and is done:** `Optimal welcomeWholeMachine
  welcomeWholeSpec welcomeAnswer` is proved in
  [`WelcomeWholeMachineOptimal.lean`](proofs_lean/ProofsLean/WelcomeWholeMachineOptimal.lean).
  Measured sunk cost of that chain: **49 `Welcome*.lean` modules, 52,258 lines**.
- **Reuse is large but uneven:** 7 modules (9,096 lines, 17.4%) contain the
  generic core; 36 modules (38,967 lines, 74.6%) are portable *patterns* that
  must be re-instantiated; 6 modules (4,195 lines, 8.0%) are Welcome-only facts.
  See §3.
- **Literal mnemonic grep is not enough:** of 91 distinct mnemonics in the 25
  answers, **63 have zero literal occurrences** in `ProofsLean/*.lean`. The Lean
  AST is structured (`ParsedAluName`, `ParsedOp`, `ParsedL1Op`, `ParsedL2Op`,
  precision prefixes), so I normalized each answer by mirroring
  `viz/core/src/vsm.rs::classify`, `blockop.rs` and `mv.rs`, then mapped
  families to modules. Details in §1 and §2.3.
- **The challenge set is tiny but heterogeneous:** 25 answers, **348 `wc -l`
  lines**, **343 issue rows/words**, **568 instructions**, **91 distinct
  mnemonics**, 1–25 distinct kinds and 1–20 normalized families per answer.
- **All 73 problems are still `unproven`** in
  [`audit.json`](proofs_lean/audit.json); `full_isa_optimality_proven: 0`,
  `restricted_mncore_optimality_proven: 0`. The 48 MNIST answers are locally
  golfed (16 beat their recorded Top) but are matrix/MAU/MV-heavy; defer them.

## 1. What was measured

### 1.1 Line counts and recorded score

For each challenge directory I ran `wc -l answer.vsm` and read `answer.json`:

- `answer.json.lines` is the recorded score (`j+m`) and equals the number of
  issue rows. It can differ from `wc -l` when the file contains comments: only
  `2.plus-two` does (10 physical lines, 5 comments, score 5).
- The answer score is `j+m`: `j` PE words plus `m` MV words. A PE source line
  with several `;`-separated expressions still costs one word; e.g.
  `10.gather-easy` has 7 instructions on 6 issue lines and scores 6.
- “Shortest known” was checked against the `Top`/`Par` recorded in
  `problem.md` and against `answer.md`, which says the saved submission is the
  minimum-line accepted entry visible in the standings at fetch time. **24 of
  25 scores equal `Top`; `20.fizzbuzz` is 93 lines against a recorded `Top` of
  98.** I did not re-fetch the live leaderboard, so “shortest” means
  “shortest recorded in this repository at fetch time”, not a fresh global
  claim.

### 1.2 Mnemonic extraction and normalization

Scripts (scratch, reproducible):

- [`extract_mnemonics.py`](research/experiments/survey/extract_mnemonics.py):
  strips `#` comments, splits `;` parallel issue, takes the leading
  `[a-z][a-z0-9]*` token, and records the full instruction text.
- [`classify.py`](research/experiments/survey/classify.py): normalizes each
  opcode the way the Rust simulator does — `[dfgh]` precision, `[mv]`
  MAU/matrix form, `fma/mul/add/passa`, `m`-read/write, `l1bm*`, `l2bm*`, `mv*`,
  and ALU `[u]?[dfghlis]?<name>`. “Families” in the tables are these normalized
  families (e.g. `alu.add`, `mau.fma`, `l1bm.reduce`, `mv`), not raw mnemonics.
- [`grep_lean.py`](research/experiments/survey/grep_lean.py): word-boundary
  literal grep of every mnemonic in `proofs_lean/ProofsLean/*.lean`;
  [`lean_hits.json`](research/experiments/survey/lean_hits.json) is the raw hit
  matrix.

Measured result of the literal grep:

| Metric | Value |
| --- | --- |
| Distinct mnemonics in the 25 answers | 91 |
| Mnemonics with at least one literal hit in Lean | 28 |
| Mnemonics with zero literal hits | **63** |
| Files with the most distinct mnemonic hits | `Issue.lean` (16), `WholeMachineStep.lean` (14) |

Examples of zero-hit mnemonics: `dmread`, `dmwrite`, `dvmulu`, `dvfmad`,
`hmmul`, `hmwrite`, `hmread`, `ipackbit`, `lpassa`, `l1bmrdfadd`,
`l2bmriiadd`, `mvr2iiadd`, `smax`, `sadd`, `sand`. Conversely, `msl`
and `msr` do have literal hits, but almost all are in Welcome module names and
prose, not opcode semantics. **Do not use literal grep alone to decide
coverage.**

### 1.3 Lean coverage mapping

All 25 challenge answers are parsed by
[`Issue.lean`](proofs_lean/ProofsLean/Issue.lean) (`ParsedOp`, `ParsedAluName`,
`ParsedL1Op`, `ParsedL2Op`, operand roles, issue checks) and executed by
[`WholeMachineStep.lean`](proofs_lean/ProofsLean/WholeMachineStep.lean). Table 2
therefore lists only the *additional/specialized* modules. Where a family is
covered only by `WholeMachineStep.lean`, that is stated as a gap.

Precision caveats that matter for reuse:

- [`SingleFMA.lean`](proofs_lean/ProofsLean/SingleFMA.lean) is a bit-exact
  **single-precision** FMA for normal inputs. `FloatAdd/Subtract/Multiply/Relu.lean`
  are single-precision value wrappers. **`SingleFMA.decode` flushes every
  exponent-zero pattern to zero** (no subnormals / FTZ). This is not a minor
  detail: several answers reinterpret integer data as `f32`. `Mul7FloatGap.lean`
  proves every admissible `4.mul7` input is exponent-zero and the modelled MAU
  maps it to `0`, so the published `mul7` answer cannot be proved correct
  against this datapath. Any integer-as-float proof must either show the
  relevant patterns are normal or extend the float model.
- Double/half MAU, half ALU, double relu, matrix MAU and block-float dot are
  dispatched in `WholeMachineStep.lean`; matrix/block-float pieces also live in
  [`ParsedIntegerStep.lean`](proofs_lean/ProofsLean/ParsedIntegerStep.lean) and
  [`RRN.lean`](proofs_lean/ProofsLean/RRN.lean). These are less exercised than
  the f32 path and are a real certification cost.
- [`UntypedALU.lean`](proofs_lean/ProofsLean/UntypedALU.lean) deliberately returns
  `.unknown` for `msl`/`msr` because the manual and the reference binary disagree
  about the LSB; `WholeMachineStep.lean` implements the reference behavior.
  Any proof involving `msl`/`msr` must state which target it certifies.
- [`PEParser.lean`](proofs_lean/ProofsLean/PEParser.lean) covers operands,
  including L1/L2/DAR/matrix; complete-line/opcode parsing is in `Issue.lean`
  and the Rust parser, not a single Lean module.
- [`Optimality.lean`](proofs_lean/ProofsLean/Optimality.lean) supplies the target
  vocabulary (`LowerBound`, `Optimal`, `SymbolicBoundCertificate`).

### 1.4 Concurrent work observed in the shared tree (not edited by me)

At survey time the working tree contained untracked files from other agents.
They are relevant to routing and may change:

- [`ABLowerBound.lean`](proofs_lean/ProofsLean/ABLowerBound.lean) (791 lines) —
  **MNIST `1.a-b` (float A−B), not challenge `3.a-plus-b`.** It puts the problem
  on the sealed whole-machine value model and reduces `LowerBound 2` to two
  explicitly stated residuals (`ABNarrowTransfer`, `AbDoubleOrIndependent`),
  which are not proved. It shows that even a 3-line float elementwise answer is
  not cheap: the Welcome zero-state write shapes cannot close it directly because
  the target equals the initial LM1 value at the zero input.
- [`Mul7Spec.lean`](proofs_lean/ProofsLean/Mul7Spec.lean) (260 lines),
  [`Mul7LowerBound.lean`](proofs_lean/ProofsLean/Mul7LowerBound.lean) (280 lines),
  [`Mul7FloatGap.lean`](proofs_lean/ProofsLean/Mul7FloatGap.lean) (97 lines) —
  `4.mul7` spec, a one-line footprint lower-bound reduction, and the FTZ gap
  described above. The lower-bound shell is close (residual
  `Mul7PELineFootprint`); correctness is the blocker.
- These are concurrent scratch/shared modules, untracked and possibly still
  changing. I did not edit them. I also observed `research/lean-plan-progress.md`
  modified during the survey; this was not my edit. The `4.mul7` ranking in §5
  is adjusted for the reported model gap.

## 2. The 25 challenge problems

### 2.1 Counts, shortest-known status, instruction mix, and output bank

`kinds` = distinct raw mnemonics excluding `nop`/`noforward`/`wait`; `families`
= normalized opcode families excluding `nop`/control. `flags` record unit use
(`MAU`, `matrix`, `MV`, `mask`, `L1`, `L2`). Output bank is from `## Outputs`.

| # | Problem | `wc -l` | score (`j+m`) | Top / Par | instrs / kinds | families | flags | output |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 1 | [`1.plus-one`](problems/challenge/1.plus-one/answer.vsm) | 2 | 2 | 2 / 2 | 2 / 1 | 1 | — | LM1 |
| 2 | [`2.plus-two`](problems/challenge/2.plus-two/answer.vsm) | 10 | 5 | 5 / 9 | 5 / 2 | 2 | — | LM1 |
| 3 | [`3.a-plus-b`](problems/challenge/3.a-plus-b/answer.vsm) | 6 | 6 | 6 / 14 | 6 / 2 | 2 | — | LM0 |
| 4 | [`4.mul7`](problems/challenge/4.mul7/answer.vsm) | 6 | 6 | 6 / 24 | 10 / 3 | 3 | MAU, mask | LM1 |
| 5 | [`5.abs`](problems/challenge/5.abs/answer.vsm) | 13 | 13 | 13 / 44 | 45 / 4 | 4 | MAU, L1, mask | LM1 |
| 6 | [`6.fadd-mul`](problems/challenge/6.fadd-mul/answer.vsm) | 14 | 14 | 14 / 20 | 32 / 7 | 7 | MAU, L1 | LM1 |
| 7 | [`7.mul2`](problems/challenge/7.mul2/answer.vsm) | 9 | 9 | 9 / 14 | 19 / 5 | 5 | MAU, L1 | LM1 |
| 8 | [`8.fle`](problems/challenge/8.fle/answer.vsm) | 4 | 4 | 4 / 11 | 7 / 4 | 3 | MAU, mask | LM1 |
| 9 | [`9.transpose-addr`](problems/challenge/9.transpose-addr/answer.vsm) | 10 | 10 | 10 / 64 | 16 / 3 | 3 | MAU | LM1 |
| 10 | [`10.gather-easy`](problems/challenge/10.gather-easy/answer.vsm) | 6 | 6 | 6 / 15 | 7 / 4 | 4 | MAU | LM1 |
| 11 | [`11.square-sum`](problems/challenge/11.square-sum/answer.vsm) | 11 | 11 | 11 / 191 | 11 / 7 | 5 | MAU, L1, mask | LM1 |
| 12 | [`12.convert-endian`](problems/challenge/12.convert-endian/answer.vsm) | 3 | 3 | 3 / 48 | 4 / 4 | 3 | MAU | LM1 |
| 13 | [`13.mod3`](problems/challenge/13.mod3/answer.vsm) | 8 | 8 | 8 / 124 | 18 / 6 | 6 | MAU, L1, mask | LM1 |
| 14 | [`14.mat-sq`](problems/challenge/14.mat-sq/answer.vsm) | 10 | 10 | 10 / 160 | 18 / 4 | 4 | MAU, matrix, mask | LM1 |
| 15 | [`15.contains`](problems/challenge/15.contains/answer.vsm) | 20 | 20 | 20 / 220 | 34 / 12 | 9 | MAU, matrix, L1, mask | LM1 |
| 16 | [`16.count-up`](problems/challenge/16.count-up/answer.vsm) | 21 | 21 | 21 / 100 | 37 / 22 | 10 | MAU, MV, L1, L2, mask | DRAM |
| 17 | [`17.transpose-mab`](problems/challenge/17.transpose-mab/answer.vsm) | 15 | 15 | 15 / 112 | 24 / 3 | 3 | MAU, L1, mask | LM1 |
| 18 | [`18.inversion-small`](problems/challenge/18.inversion-small/answer.vsm) | 9 | 9 | 9 / 359 | 11 / 9 | 8 | MAU, matrix, L1, mask | LM1 |
| 19 | [`19.inversion`](problems/challenge/19.inversion/answer.vsm) | 31 | 31 | 31 / 1080 | 48 / 12 | 10 | MAU, MV, L1, L2, mask | LM1 |
| 20 | [`20.fizzbuzz`](problems/challenge/20.fizzbuzz/answer.vsm) | 93 | 93 | 98 / 400 | 123 / 25 | 20 | MAU, matrix, MV, L1, L2, mask | DRAM |
| 21 | [`21.hello-world`](problems/challenge/21.hello-world/answer.vsm) | 9 | 9 | 9 / 14 | 11 / 7 | 7 | MAU, MV, L1, L2, mask | DRAM |
| 22 | [`22.bit-reverse`](problems/challenge/22.bit-reverse/answer.vsm) | 10 | 10 | 10 / 330 | 17 / 13 | 8 | MAU, L1, mask | LM1 |
| 23 | [`23.fizzbuzz-pe`](problems/challenge/23.fizzbuzz-pe/answer.vsm) | 9 | 9 | 9 / 24 | 17 / 7 | 7 | MAU, L1, mask | LM1 |
| 24 | [`24.log2`](problems/challenge/24.log2/answer.vsm) | 7 | 7 | 7 / 35 | 16 / 6 | 6 | MAU, L1, mask | LM1 |
| 25 | [`25.hsv2rgb`](problems/challenge/25.hsv2rgb/answer.vsm) | 12 | 12 | 12 / 60 | 30 / 15 | 12 | MAU, L1, mask | LM1 |

Totals: 348 `wc -l`, 343 score/issue rows, 568 instructions, 91 mnemonics.

What the flags mean for the lower-bound work:

- **No MAU/matrix/MV/mask at all:** `1.plus-one` (done), `2.plus-two`,
  `3.a-plus-b`. These are the only three answers whose entire computation is
  integer ALU (with `passa` only in `3.a-plus-b`). `3.a-plus-b` is the only LM0-output challenge problem.
- **MAU + mask, no L1/L2/MV:** `4.mul7`, `8.fle`. Short answers whose output is a
  constant/selected value; a constant-write count is plausible. `4.mul7` is
  additionally **blocked by the FTZ gap** (§1.4), so its flags understate the
  cost.
- **MAU + L1 (+ mask):** `5.abs`, `6.fadd-mul`, `7.mul2`, `11.square-sum`,
  `13.mod3`, `17.transpose-mab`, `23.fizzbuzz-pe`, `24.log2`, `25.hsv2rgb`,
  `22.bit-reverse`. The L1 path is a copy/transfer path; the value question is
  whether the answer's values can be produced without the target ALU/MAU.
- **Matrix:** `14.mat-sq`, `15.contains`, `18.inversion-small`, plus
  `20.fizzbuzz` (matrix read/write used inside the renderer).
- **MV/DRAM:** `16.count-up`, `20.fizzbuzz`, `21.hello-world`; `19.inversion`
  uses L2/MV internally but writes LM1.
- Only `16`, `20`, `21` require reading the answer back from **DRAM**; `3`
  requires **LM0**; the other 21 require **LM1**.

### 2.2 Which Lean modules already model the instructions

Common base for every row: `Issue.lean` (parsed opcode/operand AST and issue
roles) and `WholeMachineStep.lean` (whole-state transition). The table lists
additional specialized modules and the specific coverage gap that matters for a
full-ISA lower bound. All module names are under `proofs_lean/ProofsLean/`.

| # | Problem | Additional Lean models (beyond the base) | Coverage / exactness gap |
| --- | --- | --- | --- |
| 1 | `1.plus-one` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`ParsedIntegerStep`](proofs_lean/ProofsLean/ParsedIntegerStep.lean), [`PlusOne`](proofs_lean/ProofsLean/PlusOne.lean), [`WelcomeWholeMachineOptimal`](proofs_lean/ProofsLean/WelcomeWholeMachineOptimal.lean) | **Done** on the hazard-aware machine; full chain in §3. |
| 2 | `2.plus-two` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean) | `idec`/`ixor` have AST + executor only; no source-level value lemma or answer-specific module. |
| 3 | `3.a-plus-b` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`PEMemory`](proofs_lean/ProofsLean/PEMemory.lean) (LM0 bank) | Same: `iadd`/`ipassa` are generic; no answer-specific module. |
| 4 | `4.mul7` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean) (`smax`), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`UntypedALU`](proofs_lean/ProofsLean/UntypedALU.lean) (`imm`), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`Mul7Spec`](proofs_lean/ProofsLean/Mul7Spec.lean), [`Mul7LowerBound`](proofs_lean/ProofsLean/Mul7LowerBound.lean), [`Mul7FloatGap`](proofs_lean/ProofsLean/Mul7FloatGap.lean) | **Blocked by FTZ:** every admissible input is an exponent-zero `f32` pattern, which `SingleFMA` decodes as zero, so the answer’s correctness cannot be stated against that datapath. The one-line LB is reduced to `Mul7PELineFootprint`. |
| 5 | `5.abs` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | f32 FMA is exact; the abs/mask interaction is not packaged. |
| 6 | `6.fadd-mul` | [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`FloatAdd`](proofs_lean/ProofsLean/FloatAdd.lean), [`FloatRelu`](proofs_lean/ProofsLean/FloatRelu.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean) | `hvadd` is half-precision; exactness lives in `WholeMachineStep`. |
| 7 | `7.mul2` | [`FloatRelu`](proofs_lean/ProofsLean/FloatRelu.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (half MAU/ALU) | Half rounding/conversion and `hrelu`/`hilrelud` are only in the whole-machine dispatcher. |
| 8 | `8.fle` | [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean) (`inot`), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Mask-register/infinity semantics not packaged; `hvfma` half in `WholeMachineStep`. |
| 9 | `9.transpose-addr` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (`drelu`, `dvpassa`) | Double relu/passa are only in the dispatcher; no layout/permutation module. |
| 10 | `10.gather-easy` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`UntypedALU`](proofs_lean/ProofsLean/UntypedALU.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) | **`msl` is `.unknown` in `UntypedALU`** (manual/reference LSB disagreement); `WholeMachineStep` implements reference behavior. |
| 11 | `11.square-sum` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (double MAU) | Double MAU and `l1bmrdfadd` reduction are only covered compositionally. |
| 12 | `12.convert-endian` | [`ConvertEndian`](proofs_lean/ProofsLean/ConvertEndian.lean), [`ByteSwap`](proofs_lean/ProofsLean/ByteSwap.lean), [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`UntypedALU`](proofs_lean/ProofsLean/UntypedALU.lean) | 511-line bit-level datapath/readback; **no full-program correctness or lower bound**. |
| 13 | `13.mod3` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | FMA mod-3 reciprocal trick is not proved exact; masks involved. |
| 14 | `14.mat-sq` | [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean), [`ParsedIntegerStep`](proofs_lean/ProofsLean/ParsedIntegerStep.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`WelcomeMatrixMAUShape`](proofs_lean/ProofsLean/WelcomeMatrixMAUShape.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Matrix MAU/block-float exactness vs Rust is the dominant gap. |
| 15 | `15.contains` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`WelcomeMatrixMAUShape`](proofs_lean/ProofsLean/WelcomeMatrixMAUShape.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (half matrix) | Matrix write + L1 broadcast/reduce + membership spec. |
| 16 | `16.count-up` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`MVSemantics`](proofs_lean/ProofsLean/MVSemantics.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Expansion to 16K words + L2/MV/DRAM delivery; no reusable lower-bound template. |
| 17 | `17.transpose-mab` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (double MAU) | Multi-destination L1 broadcast; `WelcomeL1MultiDest` shows the naïve singleton shape is false. |
| 18 | `18.inversion-small` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`WelcomeMatrixMAUShape`](proofs_lean/ProofsLean/WelcomeMatrixMAUShape.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (half MAU) | Matrix write + half MAU + global inversion count. |
| 19 | `19.inversion` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`MVSemantics`](proofs_lean/ProofsLean/MVSemantics.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | L2/MV + global inversion count. |
| 20 | `20.fizzbuzz` | all of the above plus [`WelcomeMatrixMAUShape`](proofs_lean/ProofsLean/WelcomeMatrixMAUShape.lean), [`MVSemantics`](proofs_lean/ProofsLean/MVSemantics.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean) | 20 families, DRAM string spec; full-ISA lower bound currently out of reach. |
| 21 | `21.hello-world` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`MVSemantics`](proofs_lean/ProofsLean/MVSemantics.lean), [`RRN`](proofs_lean/ProofsLean/RRN.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Constant DRAM output; delivery/pipeline lower bound is the main missing piece. |
| 22 | `22.bit-reverse` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`UntypedALU`](proofs_lean/ProofsLean/UntypedALU.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean), [`WholeMachineStep`](proofs_lean/ProofsLean/WholeMachineStep.lean) (half MAU) | `msl`/`msr` gap plus a 1024-bit permutation; half MAU in `WholeMachineStep`. |
| 23 | `23.fizzbuzz-pe` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Branchless mod-15 selection; only 8 output words, so counting bounds are weak. |
| 24 | `24.log2` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | Exponent-extraction invariant; `sadd` is short-precision ALU. |
| 25 | `25.hsv2rgb` | [`IntegerALU`](proofs_lean/ProofsLean/IntegerALU.lean), [`FloatRelu`](proofs_lean/ProofsLean/FloatRelu.lean), [`SingleFMA`](proofs_lean/ProofsLean/SingleFMA.lean), [`L1Transfer`](proofs_lean/ProofsLean/L1Transfer.lean), [`Masks`](proofs_lean/ProofsLean/Masks.lean) | 12 families, branchy float relu/floor/ilrelud. |

The strongest existing instruction-level assets for reuse outside Welcome are
`IntegerALU.lean` (all pure integer ALU ops: inc/dec/add/sub, logic, shifts,
max/min, packbit, passa), `SingleFMA.lean` (exact f32 FMA), `L1Transfer.lean`
(pbcast/mbcast/m4bcast/distrib/mwrite/m4write/reduce/readback), `MVSemantics.lean`
(MV copy/reduction plans and snapshot commit), `RRN.lean` (integer RRN and
block-float dot), and `WholeMachineStep.lean` (the only module that connects all
of these into a whole-state step).

## 3. Reuse from the Welcome optimality chain

### 3.1 Inventory

Measured with [`welcome_scan.py`](research/experiments/survey/welcome_scan.py)
and [`welcome_scan.json`](research/experiments/survey/welcome_scan.json):

| Class | Definition | Modules | Lines | Share |
| --- | --- | ---: | ---: | ---: |
| **G — generic core** | statements quantify over arbitrary `State` / `IntegerRegisterFiles` / prepared-write lists, not the Welcome answer; re-usable with little or no change | 7 | 9,096 | 17.4% |
| **P — portable pattern** | the proof recipe (stage assembly, writer dispatch, row shape, `.lm1` provenance, certificate reduction) is reusable, but hypotheses/instances are Welcome-specific and must be re-instantiated | 36 | 38,967 | 74.6% |
| **W — Welcome-only** | facts about the two `iinc` lines, the Welcome spec, or a hypothesis that is false in general | 6 | 4,195 | 8.0% |
| **Total** | | **49** | **52,258** | 100% |

The P share is the important number for planning: **about three quarters of the
chain is a pattern, not a fact.** A new problem pays the pattern cost again
unless the pattern is factored into a parameterized module.

### 3.2 G — generic core (7 modules, 9,096 lines)

| Module | Lines | Generic content worth importing |
| --- | ---: | --- |
| [`WelcomeLm1Frame.lean`](proofs_lean/ProofsLean/WelcomeLm1Frame.lean) | 1,585 | LM1 write/frame lemmas: `isLm1Write_eq_false_of_destination_ne`, `destination_bank_ne_of_static`, `prepareParsedMaskedWrite_lm1_free`, `prepareParsedIntegerALU…_lm1_free`, `welcomePEIntegerStageLm1Provenance`. Mostly about `PreparedParsedMaskedWrite`, not Welcome values. |
| [`WelcomeStageCommit.lean`](proofs_lean/ProofsLean/WelcomeStageCommit.lean) | 1,724 | The per-stage commit induction recipe: single-destination writer, destination loop, cycle loop, per-PE walk, producer filter. Proved for msl/msr, float-relu, L1-to-PE, integer+float-MAU, block-float. The core inductions are over `IntegerRegisterFiles`/`State`; the `welcome…StageCommit` wrappers are instances (the module does contain other Welcome-named helpers). |
| [`WelcomeStageProvenance.lean`](proofs_lean/ProofsLean/WelcomeStageProvenance.lean) | 1,874 | `Lm1FreePreparedWrites` and its algebra, plus the “clean commit” companion of every stage: a successful stage is a commit whose write list is `.lm1`-free. This is the reusable replacement for “the stage does not write LM1” reasoning. |
| [`WelcomeWriterDispatch.lean`](proofs_lean/ProofsLean/WelcomeWriterDispatch.lean) | 1,351 | `Lm1WritesShape` block algebra, append/split lemmas, six-position corollaries (`lm1WritesShape_of_six_first` … `_sixth`), filter bridges, six-list commit split. The dispatch theorem shapes are reusable; the writer kinds are Welcome-specific. |
| [`WelcomeWriterShape.lean`](proofs_lean/ProofsLean/WelcomeWriterShape.lean) | 1,194 | `lm1WritesShape_append_of_only`, `welcomePEWriteShape_of_commit_shape`, and the plain/matrix-read row shapes. The “commit of a shaped list ⇒ line shape” step is generic. |
| [`WelcomeMatrixMAUCommit.lean`](proofs_lean/ProofsLean/WelcomeMatrixMAUCommit.lean) | 645 | Matrix-MAU write-list commit induction (`writeParsedMatrixMAUDestinationsAtPE_commit` … `executeParsedMatrixMAUAndWrites_commit`). The final `welcomePE…` theorem is an instance. |
| [`WelcomeLm1FrameResidual.lean`](proofs_lean/ProofsLean/WelcomeLm1FrameResidual.lean) | 723 | LM1 frames for the L1-to-PE and matrix-MAU stages, plus the final stage-frame assembly. Generic stage frames; Welcome names on the last two theorems. |

### 3.3 P — portable patterns (36 modules, 38,967 lines)

Grouped by the role named in the task. Line counts are `wc -l`.

**Line assembly / final assembly (2 modules, 1,663 lines)**

- [`WelcomeAssembly.lean`](proofs_lean/ProofsLean/WelcomeAssembly.lean) (1,212) — seven-stage `.pe` line assembly, six per-stage commit obligations.
- [`WelcomeAssemblyFinal.lean`](proofs_lean/ProofsLean/WelcomeAssemblyFinal.lean) (451) — final assembly of the line-level write-shape obligation.

**Writer dispatch and writer-kind packages (8 modules, 10,541 lines)**

- [`WelcomeWriterPackages.lean`](proofs_lean/ProofsLean/WelcomeWriterPackages.lean) (1,209)
- [`WelcomeFamilyInstances.lean`](proofs_lean/ProofsLean/WelcomeFamilyInstances.lean) (688)
- [`WelcomeFinalShape.lean`](proofs_lean/ProofsLean/WelcomeFinalShape.lean) (929)
- [`WelcomeResiduals.lean`](proofs_lean/ProofsLean/WelcomeResiduals.lean) (1,662)
- [`WelcomeSlotFree.lean`](proofs_lean/ProofsLean/WelcomeSlotFree.lean) (1,275)
- [`WelcomeFlagFreePlain.lean`](proofs_lean/ProofsLean/WelcomeFlagFreePlain.lean) (2,627)
- [`WelcomePlainReadPackages.lean`](proofs_lean/ProofsLean/WelcomePlainReadPackages.lean) (1,166)
- [`WelcomeFloatCompanion.lean`](proofs_lean/ProofsLean/WelcomeFloatCompanion.lean) (985)

These implement the same idea repeatedly: a line has one `.lm1` writer; classify
the writer kind, use the row shape for that kind, and use `.lm1`-freeness for
every other stage. The *case split* is reusable; the *packages* are Welcome's.

**Plain integer-ALU class (3 modules, 5,878 lines)**

- [`WelcomePlainClose.lean`](proofs_lean/ProofsLean/WelcomePlainClose.lean) (1,671)
- [`WelcomePlainShape.lean`](proofs_lean/ProofsLean/WelcomePlainShape.lean) (1,323)
- [`WelcomePlainStep.lean`](proofs_lean/ProofsLean/WelcomePlainStep.lean) (2,884)

**`.lm1` / row / stage shapes (15 modules, 14,689 lines)**

- MAU / float / matrix row shapes:
  [`WelcomeMAUShape.lean`](proofs_lean/ProofsLean/WelcomeMAUShape.lean) (1,040),
  [`WelcomeFloatMAUShape.lean`](proofs_lean/ProofsLean/WelcomeFloatMAUShape.lean) (1,249),
  [`WelcomeMatrixMAUShape.lean`](proofs_lean/ProofsLean/WelcomeMatrixMAUShape.lean) (1,618),
  [`WelcomeMatrixMAUZero.lean`](proofs_lean/ProofsLean/WelcomeMatrixMAUZero.lean) (804),
  [`WelcomeMatrixMAUUnconditional.lean`](proofs_lean/ProofsLean/WelcomeMatrixMAUUnconditional.lean) (269).
- L1/L2 and special ALU shapes:
  [`WelcomeL12Shape.lean`](proofs_lean/ProofsLean/WelcomeL12Shape.lean) (1,169),
  [`WelcomeL1PEShape.lean`](proofs_lean/ProofsLean/WelcomeL1PEShape.lean) (705),
  [`WelcomeL1MultiDest.lean`](proofs_lean/ProofsLean/WelcomeL1MultiDest.lean) (1,465),
  [`WelcomeSpecialShape.lean`](proofs_lean/ProofsLean/WelcomeSpecialShape.lean) (745),
  [`WelcomeReluBlockShape.lean`](proofs_lean/ProofsLean/WelcomeReluBlockShape.lean) (1,018),
  [`WelcomeHalfBlockFloat.lean`](proofs_lean/ProofsLean/WelcomeHalfBlockFloat.lean) (967),
  [`WelcomeHalfMAUCopy.lean`](proofs_lean/ProofsLean/WelcomeHalfMAUCopy.lean) (696),
  [`WelcomeGapShape.lean`](proofs_lean/ProofsLean/WelcomeGapShape.lean) (1,065),
  [`WelcomeShapes.lean`](proofs_lean/ProofsLean/WelcomeShapes.lean) (344),
  [`WelcomeFrameFix.lean`](proofs_lean/ProofsLean/WelcomeFrameFix.lean) (1,535).

The most directly portable of these are the zero-state ones:
`WelcomeL12Shape` (L1/L2 buses are zero at the zero state),
`WelcomeMatrixMAUZero` (`welcomePEMatrixMAUZeroBus`), `WelcomeHalfMAUCopy`, and
`WelcomeHalfBlockFloat`. They apply to any problem that starts from the
all-zero state and uses the same unit; only the zero-state context needs
re-instantiation.

**Provenance / reduction / certificate patterns (7 modules, 5,261 lines)**

- [`WelcomeIntegerProvenance.lean`](proofs_lean/ProofsLean/WelcomeIntegerProvenance.lean) (701)
- [`WelcomeFloatProvenance.lean`](proofs_lean/ProofsLean/WelcomeFloatProvenance.lean) (1,047)
- [`WelcomeProvenance.lean`](proofs_lean/ProofsLean/WelcomeProvenance.lean) (717)
- [`WelcomeBoundTwo.lean`](proofs_lean/ProofsLean/WelcomeBoundTwo.lean) (637)
- [`WelcomeLowerBoundTwo.lean`](proofs_lean/ProofsLean/WelcomeLowerBoundTwo.lean) (550)
- [`WelcomeLowerBound.lean`](proofs_lean/ProofsLean/WelcomeLowerBound.lean) (532)
- [`WelcomeValueBound.lean`](proofs_lean/ProofsLean/WelcomeValueBound.lean) (1,077)

**Final lift (1 module, 935 lines)**

- [`WelcomeWholeMachineOptimal.lean`](proofs_lean/ProofsLean/WelcomeWholeMachineOptimal.lean) (935) —
  mostly Welcome-specific hazard checks, but contains the generic projection
  `executeHazardAwareNormalizedLineCore_ok_project`: a successful hazard-aware
  step is the sealed value step on `state.machine`. This is the reusable bridge
  from a sealed-machine lower bound to the hazard-aware machine.

### 3.4 W — Welcome-only (6 modules, 4,195 lines)

| Module | Lines | Why it is not reusable as-is |
| --- | ---: | --- |
| [`WelcomeComplete.lean`](proofs_lean/ProofsLean/WelcomeComplete.lean) | 685 | `.unknown`-freedom for the two `iinc` lines / Welcome line class. |
| [`WelcomeValue.lean`](proofs_lean/ProofsLean/WelcomeValue.lean) | 1,502 | Exact value/readback and hazard-event facts for the two `iinc` lines. |
| [`WelcomeOptimal.lean`](proofs_lean/ProofsLean/WelcomeOptimal.lean) | 411 | Defines `welcomeSealedMachine` and proves `welcomeAnswer_correct`; not the final optimality. |
| [`WelcomeOptimalFinal.lean`](proofs_lean/ProofsLean/WelcomeOptimalFinal.lean) | 171 | Final sealed assembly; `welcomeLowerBound_two` and `welcomeAnswer_optimal`. |
| [`WelcomeMixedStructure.lean`](proofs_lean/ProofsLean/WelcomeMixedStructure.lean) | 941 | The mixed plain/inert line structure specific to Welcome's row set. |
| [`WelcomeFlagAgreement.lean`](proofs_lean/ProofsLean/WelcomeFlagAgreement.lean) | 485 | Proves a specific mixed mask-flag agreement hypothesis **false**; a warning, not a reusable lemma. |

### 3.5 The reusable proof artifacts to extract first

If the next problem is another PE/ALU elementwise problem, these are the pieces
I would lift into a parameterized module before re-proving anything:

1. `ProofsLean.SymbolicBoundCertificate` and its `sound` theorem in
   [`Optimality.lean`](proofs_lean/ProofsLean/Optimality.lean) — the certificate
   interface is already problem-independent.
2. `welcomeBoundTwoCertificate_rejects_every_short_line` in
   [`WelcomeLowerBound.lean`](proofs_lean/ProofsLean/WelcomeLowerBound.lean) —
   the observation, stated for `welcomeSealedMachine`, that a sealed machine
   with `legal = True` forces any bound-2 certificate to reject *every* one-line
   program; the proof only uses `legal = True` and cost 1.
3. `welcomeLowerBound_two_iff_rejects_short_lines` in
   [`WelcomeLowerBound.lean`](proofs_lean/ProofsLean/WelcomeLowerBound.lean) —
   reduces `LowerBound 2` to one-line refutation; the same decomposition idea
   should generalize to larger bounds by induction on the program prefix, but
   only bound 2 is formalized here.
4. The stage-commit induction of
   [`WelcomeStageCommit.lean`](proofs_lean/ProofsLean/WelcomeStageCommit.lean)
   (`writeParsedMslMsrDestination?_commit` → destination loop → cycle loop →
   per-PE walk → producer filter).
5. `Lm1FreePreparedWrites` and the clean-commit theorems of
   [`WelcomeStageProvenance.lean`](proofs_lean/ProofsLean/WelcomeStageProvenance.lean).
6. The `Lm1WritesShape` block algebra of
   [`WelcomeWriterDispatch.lean`](proofs_lean/ProofsLean/WelcomeWriterDispatch.lean)
   and `welcomePEWriteShape_of_commit_shape` in
   [`WelcomeWriterShape.lean`](proofs_lean/ProofsLean/WelcomeWriterShape.lean).
7. The value/counting pattern of
   [`WelcomeValueBound.lean`](proofs_lean/ProofsLean/WelcomeValueBound.lean):
   `IsWelcomeCopy` (a masked merge of copies is a copy),
   `exists_uncovered_of_windows` (counting uncovered `.lm1` words), and
   `welcome_not_correct_of_word_ne_one` (one wrong output word refutes a line).
   This is the closest existing template for `plus-two`/`a-plus-b`/`abs`.
8. `executeHazardAwareNormalizedLineCore_ok_project` in
   [`WelcomeWholeMachineOptimal.lean`](proofs_lean/ProofsLean/WelcomeWholeMachineOptimal.lean)
   — the sealed-to-hazard-aware lift.

### 3.6 Pitfalls to carry into the next problem

- **Don't copy the hypotheses.** Several P modules take `WelcomePEUnrefuted`,
  `floatEmpty`, `mauFilter = [e]`, `l1Filter = [e]`, or a residual-class
  hypothesis. The chain's history is largely the removal of such hypotheses
  round by round; e.g. `WelcomeFlagAgreement.lean` proves one of them false.
  A new problem must state the obligation without the class it is trying to
  refute.
- **`welcomeLm1Writer_unique` is about the Welcome line set.** For multi-target
  L1 rows the singleton-writer shape is false; `WelcomeL1MultiDest.lean` has the
  counterexample and the corrected split. Do not assume “one writer per line”
  without checking the issue group.
- **The chain is PE-0/LM1-centric.** `WelcomePELm1WriteShapeObligation` is about
  PE 0's `.lm1` words read after the program. `3.a-plus-b` writes LM0; `16/20/21`
  write DRAM. Those need new destination frames and a different readback
  theorem, not a re-labeling.
- **The zero-state lemmas are strong but conditional.** `WelcomeMatrixMAUZero`,
  `WelcomeHalfMAUCopy`, `WelcomeL12Shape` etc. are valuable for any zero-initial
  matrix/L1 problem, but they are stated at `welcomeInitialState`/`welcomeZeroFiles`
  and must be re-pointed at the new initial state.
- **Precision.** `SingleFMA` is f32 and is **FTZ/no-subnormal**; any answer using
  `h*`/`d*` MAU or half ALU is relying on `WholeMachineStep`'s d/h paths, which
  are not backed by a standalone exact datapath module of the same maturity.
  `7.mul2`, `11.square-sum`, `9.transpose-addr`, `18.inversion-small`,
  `22.bit-reverse` are in this class. Any answer that reinterprets integer words
  as `f32` (`4.mul7`, and the mask/reciprocal tricks in `5.abs`, `13.mod3`,
  `23.fizzbuzz-pe`, `24.log2`) must also discharge the FTZ/subnormal question or
  extend the float model; `Mul7FloatGap.lean` is a concrete instance.
- **`1.a-b` is not `3.a-plus-b`.** The untracked `ABLowerBound.lean` is the
  MNIST float A−B problem, not the challenge A+B. Do not merge their routing.

## 4. The 48 MNIST problems (brief)

The `problems/` root contains 48 non-challenge MNIST problems (`1.a-b` …
`48.matmul-tra-pkg-lmdram-16-256-1024`), in addition to the 25 challenge
directories. Measured:

- **48 answers**, **679 total `wc -l`**, median 10, min 2 (`3.relu`), max 68
  (`23.dram-dl-256-1024`).
- Categories: 1–16 elementwise/reduction/softmax-like (16), 17–31 DRAM
  transfer/expansion (15), 32–48 matmul variants (17).
- **10 DRAM-output problems:** `18`, `20`, `25`, `27`, `29`, `31`, `39`, `46`,
  `48`, and `8.sumcol`.
- All 48 have recorded `answer.json` scores; **32 tie the recorded `Top`, 16 are
  shorter than the recorded `Top`, none are longer**. That indicates local
  golfing, not a fresh leaderboard check.
- All 48 are in [`audit.json`](proofs_lean/audit.json) and are `unproven`
  (`73 = 25 + 48`). They are matrix/MAU/L1/L2/MV-heavy; certifying them would
  multiply the matrix/block-float and MV/L2 work rather than reuse the
  Welcome chain cheaply. **Exception already in flight:** `1.a-b` is being
  formalized in [`ABLowerBound.lean`](proofs_lean/ProofsLean/ABLowerBound.lean)
  (sealed model, reduced to two residuals); it is a 3-line float elementwise
  answer and is still not cheap.

**Recommendation:** defer the 48 MNIST problems until the matrix/block-float
and MV/L2 semantics are independently validated on `14.mat-sq`,
`18.inversion-small`, and `21.hello-world`. Use them as a regression corpus for
`WholeMachineStep`, `RRN`, and `MVSemantics`, not as Phase 1 certification
targets.

## 5. Ranked recommendation: expected cost to certify optimality

### 5.1 Rubric

This is a judgment call, not a measured cost. I ranked by:

1. **Lower-bound shape.** Elementwise value problems can use a
   provenance/value invariant plus a writer-window count; copy/permutation
   problems need an address/data-movement argument; reductions and matrix
   products need information-flow or matrix semantics; DRAM problems need a
   delivery model.
2. **Instruction homogeneity.** Fewer normalized families and fewer unit types
   mean fewer case splits in the one-line/two-line refutation.
3. **Semantics gaps.** `msl`/`msr` (`UntypedALU` returns `.unknown`), half/double
   exactness, matrix/block-float, and L2/MV are multipliers.
4. **Existing formalization.** `12.convert-endian` has a 511-line bit-level
   datapath proof, which removes the correctness half.
5. **Bound size.** A small bound is not automatically cheap: bound 2 already
   cost 52k lines because it had to refute *every* one-line program. A large
   heterogeneous answer is usually worse, but a clean counting/invariant
   argument can beat a brute-force classification.

### 5.2 Ranked table (cheapest first; `1.plus-one` baseline)

| Rank | Problem | Score | Lower-bound shape | Why this rank |
| ---: | --- | ---: | --- | --- |
| 1 | `1.plus-one` | 2 | value/count (done) | **Baseline:** 2 `iinc` lines proved optimal on the hazard-aware machine; measured chain cost 49 modules / 52,258 lines. |
| 2 | `3.a-plus-b` | 6 | value + write count | 6 pure integer-ALU lines (`iadd`+`ipassa`), no MAU/mask/L1/MV, LM0 output; 4 add lines + 2 copy lines is the closest analogue to the Welcome chain. |
| 3 | `2.plus-two` | 5 | value + long-word count | 5 pure integer-ALU lines (`idec`+`ixor`), no MAU/mask/MV; the 20-long output makes a per-line long-word count plausible, but the borrow/carry bit trick needs its own value lemma. |
| 4 | `5.abs` | 13 | value + write count | 13 lines/88 words, ALU+MAU+L1+mask; 11 ALU lines is a near-matching count bound, with only mask generation to explain the extra 2. |
| 5 | `24.log2` | 7 | value + shift invariant | 7 lines/32 words; only integer shifts plus L1/MAU add/passa, but the exponent-extraction invariant must be proved. |
| 6 | `8.fle` | 4 | constant/count | 4 lines/40 constants (0 or inf), MAU+mask; a constant-write count plus mask semantics may pin 4, but the output is not a copy. |
| 7 | `12.convert-endian` | 3 | permutation | Correctness datapath is already in `ConvertEndian.lean` (511 lines); remaining work is a 2-line permutation impossibility for bound 3. |
| 8 | `13.mod3` | 8 | modular invariant | 8 lines/32 words, FMA reciprocal + masks; exact mod-3 semantics and a modular invariant are the blockers. |
| 9 | `23.fizzbuzz-pe` | 9 | predicate/selection | 9 lines but only 8 output words; branchless mod-15 selection makes count bounds weak and the predicate proof heavy. |
| 10 | `7.mul2` | 9 | half-precision value/count | 9 lines/96 half words; half multiply/rounding plus relu/ilrelud, so exactness and a per-word count both need work. |
| 11 | `6.fadd-mul` | 14 | MAU value/count | 14 lines/128 floats; homogeneous MAU add/mul/fma+relu+L1, but the count bound (8) is far from 14. |
| 12 | `25.hsv2rgb` | 12 | branchy float value | 12 lines, 12 families, branchy float relu/floor/ilrelud; correctness and LB are both large. |
| 13 | `21.hello-world` | 9 | constant + delivery | 9 lines, constant 13-byte string in a 2-word DRAM window; correctness is easy and the preliminary fizzbuzz delivery-LB template applies (Python/CP-SAT, not Lean), but MV/L1/L2 readback must be modeled. |
| 14 | `9.transpose-addr` | 10 | layout permutation | 10 lines, pure layout permutation (`lpassa`/`drelu`/`dvpassa`); output is a copy, so no value invariant—needs an address-window permutation bound. |
| 15 | `10.gather-easy` | 6 | gather/address | 6 lines but uses `msl`, whose manual/reference semantics disagree; resolve that gap before any LB. |
| 16 | `22.bit-reverse` | 10 | bit permutation | 10 lines, `msl`/`msr` gap plus a 1024-bit global permutation and L1 movement. |
| 17 | `11.square-sum` | 11 | reduction | 11 lines, L1 reduction + double MAU; output is a 128-term reduction, so an information-flow bound is required. |
| 18 | `17.transpose-mab` | 15 | L1 layout | 15 lines, multi-destination L1 broadcast/gather; `WelcomeL1MultiDest` already shows the naïve singleton shape is false. |
| 19 | `14.mat-sq` | 10 | matrix | 10 lines, matrix MAU + block float + masks; matrix/block-float exactness is the dominant cost. |
| 20 | `4.mul7` | 6 | **blocked** | **Blocked, not merely hard:** the lower-bound shell (`Mul7Spec`/`Mul7LowerBound`) reduces to a one-line footprint, but `Mul7FloatGap` proves the current `SingleFMA` model maps every admissible input to zero. Fix the float model first; if fixed, this moves up to about rank 7. |
| 21 | `18.inversion-small` | 9 | matrix + global count | 9 lines, matrix write + half MAU + L1 reduce; global inversion count compounds matrix semantics. |
| 22 | `15.contains` | 20 | matrix + L1 | 20 lines, 12 kinds incl matrix write and L1 broadcast/reduce; membership spec plus many families. |
| 23 | `19.inversion` | 31 | L2/MV + global count | 31 lines, L2/MV/L1/MAU; global inversion count plus multi-unit movement. |
| 24 | `16.count-up` | 21 | DRAM expansion | 21 lines, 22 kinds, DRAM/MV/L1/L2; expansion to 16K words has no reusable lower-bound template. |
| 25 | `20.fizzbuzz` | 93 | DRAM string + full ISA | 93 lines, 25 kinds, every unit, DRAM string spec; full-ISA LB is currently out of reach (only a preliminary 9-word delivery LB exists, and it is not Lean-verified). |

**FTZ caveat on the order.** Ranks 4 (`5.abs`), 5 (`24.log2`), 8 (`13.mod3`), 9 (`23.fizzbuzz-pe`) and 20 (`4.mul7`) use integer-as-`f32` bit tricks and are provisional until the FTZ/subnormal question is audited for their exact input domains. If one of them is blocked like `4.mul7`, it should move below `12.convert-endian` or lower. `3.a-plus-b` and `2.plus-two` are unaffected (pure integer ALU).

### 5.3 Suggested parallel tracks

If the parent wants to fan out immediately, I would split the effort this way:

- **Track A — pure integer elementwise (start now):** `3.a-plus-b` first, then
  `2.plus-two`. Factor `SymbolicBoundCertificate` + the `WelcomeValueBound`
  copy/window argument + `WelcomeStageCommit`/`StageProvenance` into a
  problem-parameterized module. These two should share almost all machinery.
- **Track B — short MAU/mask elementwise:** `5.abs`, `24.log2`, `8.fle`.
  `5.abs` is the best first target because its output count is close to an ALU
  line count. **Do not start `4.mul7`** until the FTZ/subnormal gap is resolved;
  if it is, the existing `Mul7LowerBound` shell makes it a strong candidate.
- **Track C — Convert Endian lower bound:** assign separately. Correctness is
  already in `ConvertEndian.lean`; the remaining task is a bound-3 lower bound
  (2-line permutation impossibility). This is a good pilot for “permutation”
  lower bounds without the matrix/MV burden.
- **Do not start yet:** `4.mul7` (FTZ gap), `10.gather-easy`/`22.bit-reverse`
  (resolve `msl`/`msr` target first), `11.square-sum`/`17.transpose-mab` (L1
  reduction/layout), `14.mat-sq`/`18.inversion-small`/`15.contains`
  (matrix/block-float), `19.inversion`/`16.count-up`/`20.fizzbuzz` (L2/MV/DRAM).
  `21.hello-world` is a reasonable later delivery pilot once MV/L1/L2 semantics
  are trusted.

## 6. Limitations

- **No live leaderboard check.** “Shortest” means the saved answer's recorded
  `score` equals/beats the `Top` recorded in `problem.md` at fetch time. The
  repository’s `answer.md` documents a minimum-line selection from the standings
  at fetch time, but that is not a proof of global optimality.
- **The module mapping is semantic, not a completeness proof.** I normalized
  opcodes by mirroring the Rust classifier and then listed modules that model
  the family or the executor path. It is possible that a module proves a
  related fact under a different constructor name; the 63/91 zero-literal-hit
  result shows why literal grep cannot settle this.
- **The ranking is a judgment.** I did not measure proof effort. The ordering
  is based on the lower-bound shape, instruction heterogeneity, semantic gaps,
  and the one completed chain. The top two are the most defensible; ranks 6–14
  are close and could move after a spike. `4.mul7` is placed by its *blocked*
  status, not by its lower-bound difficulty.
- **Concurrent files may move.** The `1.a-b` and `4.mul7` modules in §1.4 were
  untracked and being written while this survey was prepared. Their status,
  theorem names and even file names can change. The FTZ behavior itself is not
  hearsay: I read `SingleFMA.decode` and confirmed that exponent zero returns
  `.zero` for every mantissa.
- **`check.py` is not green.** It was not used as a gate; the gate is
  `cd proofs_lean && lake build ProofsLean` (900 jobs, measured here). The
  repository’s evidence-staleness issue is independent of this survey.
- **Welcome chain cost is not a clean unit.** 52,258 lines include failed
  attempts, restatements, and rounds of hypothesis removal; it is an upper
  bound on the reusable output, not the minimum cost of a similar proof.
- **The 48 MNIST answers are summarized, not surveyed problem-by-problem.**
  Their line counts and output banks are measured; their instruction-level
  module mapping is not tabulated because they are out of the immediate
  certification path.

## 7. Scratch artifacts

All under `research/experiments/survey/`:

- [`extract_mnemonics.py`](research/experiments/survey/extract_mnemonics.py),
  [`mnemonics.json`](research/experiments/survey/mnemonics.json),
  [`vocab.txt`](research/experiments/survey/vocab.txt)
- [`classify.py`](research/experiments/survey/classify.py),
  [`classified.json`](research/experiments/survey/classified.json)
- [`grep_lean.py`](research/experiments/survey/grep_lean.py),
  [`lean_hits.json`](research/experiments/survey/lean_hits.json)
- [`build_table.py`](research/experiments/survey/build_table.py),
  [`table.json`](research/experiments/survey/table.json)
- [`welcome_scan.py`](research/experiments/survey/welcome_scan.py),
  [`welcome_scan.json`](research/experiments/survey/welcome_scan.json),
  [`headers.txt`](research/experiments/survey/headers.txt)
