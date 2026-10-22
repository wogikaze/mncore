# `12.convert-endian` — true minimum and lower-bound report

Date: 2026-10-21.  Workspace: `/home/wogikaze/wgkz/mncore`.
Deliverables:

* `proofs_lean/ProofsLean/ConvertEndianLowerBound.lean` — the challenge problem
  on the sealed whole-machine value model, the unconditional line-kind
  refutations, and the exact reductions of `LowerBound 2` and `LowerBound 3`.
* `proofs_lean/ProofsLean/ValueProvenance.lean` — the problem-free one-stage
  value provenance core (the data half of a one-line argument).
* this report, the search scripts, and the saved JSON witnesses.

Both Lean modules build with

```sh
cd proofs_lean
lake build ProofsLean.ConvertEndianLowerBound
lake build ProofsLean.ValueProvenance
```

No `sorry`/`admit`/`native_decide`/new axioms.  `#print axioms` on the main
theorems gives `[propext, Classical.choice, Quot.sound]` only.

## 0. Bottom line

* **The official three-line answer is accepted**:
  `judge.py testcase.vsm answer.vsm` → `ACCEPTED!! score=3 j=3 m=0 bytes=102`.
* **The true minimum is 3** on the evidence collected here: the 5,675-form
  one-line source space was enumerated, a 110-form execution sample produced
  zero survivors, and the two-stage datapath value closure excludes both 32-bit
  halves of the byte-swapped word for several explicit witnesses (see §1.3).
  The sandbox reaps long subprocess-heavy sweeps, so the full execution sweep
  was not completed; the semantic closure is the primary evidence.  The `line1 = imm P` shape is the
  one two-line shape outside that closure analysis; it is a functional equation
  in the 32-bit payload `P` and does not admit a constant witness, so it needs a
  program-dependent witness (see §1.4).
* **`LowerBound 2` is reduced to the single-`.pe`-line value argument**, with
  the empty program, every `nop`, every `mv`, and every syntactically rejected
  or all-`.noforward` `.pe` line refuted unconditionally.  The exact residual is
  `CendPEUnrefuted` / `CendPELinesRefuted`.
* **`LowerBound 3` is reduced to that one-line residual plus the exact
  two-unit-line obligation** `CendTwoLinesRefuted`.
* The executor-level data half of the one-line argument is now a problem-free
  Lean component (`ValueProvenance.lean`).  What remains for the *executor*
  link is the per-expression branch induction `PlainALUPreparedDataInClosure`
  (the direct-memory branch is proved) and the read-source closure
  `ReadWordsInClosure`; the remaining *value* step is a finite certificate that
  the two target halves are outside the one-stage closure for the witness.

## 1. Empirical minimum

### 1.1 Baseline

```sh
python3 judge/judge-py/judge.py \
  problems/challenge/12.convert-endian/testcase.vsm \
  problems/challenge/12.convert-endian/answer.vsm
# ACCEPTED!! score=3 j=3 m=0 bytes=102
```

The same result is obtained with a synthetic four-PE testcase in
`harness.py` (`judge()`), so the answer is not tied to the single shipped
input.

### 1.2 One-line sweep

`search_clean.py` (`single()`) enumerates 5,675 distinct one-line source forms:

* integer ALU `inc/dec/passa/not/lnot`, binary
  `and/or/xor/add/sub/lsl/lsr/bsl/bsr/packbit/max/min`, at `.l`/`.i`/`.s`
  precision,
* `msl`/`msr`, `hbfe/6..9`, `hbfn/6..9`,
* sources `$m0v`, `$r0v`, `$s0v`, `$t`, `$msb1`, `$subpeid`, `$peid`,
* LM1 destinations `$n0v`, `$n[1,0,3,2]`, `$ln0v`, `$n[0,1,2,3]`,
  `$ln[0,2,4,6]`,
* `imm` and single-line MAU `passa` forms.

Each form is assembled with `assemble3 --instruction-mode flat` and executed
with `gpfn3_package_main --offchip-memory-init zero`; a survivor must produce
`byteSwap` at all four PE outputs on four inputs
`0x0123456789ABCDEF`, `0x0102030405060708`, `0xFEDCBA9876543210`,
`0xFFFFFFFFFFFFFFFF`.  A 110-form foreground sample of this space produced
**0 survivors** (57 wrong / 3 assembler-invalid / 50 wrong in the first batch);
the full space was not executed because the sandbox reaps long subprocess-heavy
runs.  The earlier hand probes agree: `msl`/`msr` and `hbfe`/`hbfn` shift/mix
lanes but do not reverse the bytes, and `imm` alone cannot write LM1.

### 1.3 Two-stage datapath value closure

The stronger evidence is a closed-world value analysis.  For a fixed witness
`x`, let `V0` be the finite set of 64-bit buses visible at PE0 in the initial
state (the input word, zero-filled layouts, and the fixed constants), `V1` the
union of `V0` and one supported lane-op image, and `W2` all 32-bit words of one
more lane-op image of `V1`.  A two-line program whose first line does not read
an `imm` constant can only put a word of `W2` at LM1.

`value_table.py` (saved in `value_table.json`) gives:

| witness `x` | target low / high | `|V1|` | `|W2|` | halves in `W2`? |
|---|---:|---:|---:|---|
| `0x0123456789ABCDEF` | `0x67452301` / `0xEFCDAB89` | 379 | 69,039 | **yes** |
| `0x0102030405060708` | `0x04030201` / `0x08070605` | 385 | 57,740 | no |
| `0x0807060504030201` | `0x05060708` / `0x01020304` | 375 | 48,292 | no |
| `0xDEADBEEFCAFEBABE` | `0xEFBEADDE` / `0xBEBAFECA` | 372 | 72,125 | no |
| `0x0000000000000000` | `0` / `0` | 54 | 144 | yes |
| `0xFFFFFFFFFFFFFFFF` | all-ones | 70 | 348 | yes |

So `x = 0x0102030405060708`, `x = 0x0807060504030201` and
`x = 0xDEADBEEFCAFEBABE` are witnesses for which **neither** target half is
reachable after two stages, while `0x0123456789ABCDEF` is *not* such a witness.
The witness in the Lean module is `0x0102030405060708`.

The closure is a **superset** of what the executor can produce: it allows any
two source buses from the closure for the second op, and all precisions/ops.
It does not include float-MAU, `msl`/`msr`, block-float, matrix, or L1/L2
producers; those need to be added to the source set (or excluded by a
family argument) before this becomes a full-machine statement.

### 1.4 The `imm P` shape

If line 1 is `imm i"P" $r0v`, the second line is a single op applied to the
input and the constant bus `P ++ P` (or to the constant alone).  There is no
single fixed witness that defeats every `P`: for the witness above,
`x xor byteSwap(x)` is a 64-bit constant whose two 32-bit halves differ, so a
`P ++ P` XOR cannot produce it; but for other ops/sources a `P` may exist (for
`add`, the two lane equations can sometimes both be solved by one `P`).  The
correct refutation is a **program-dependent witness**: e.g. choose `x` from a
finite set such that no `P` satisfies the resulting pair of bit-vector
equations.  This is a small `bv_decide`-shaped case split over the supported
ops and is *not* covered by the closure table above, which is stated for a
fixed witness.

## 2. Lean deliverable I — `ConvertEndianLowerBound.lean`

### 2.1 Model

```lean
cendSealedMachine : ProofsLean.Machine
  -- Line := InstructionLine, State := State, Input := BitVec 64,
  -- step := executeNormalizedLine with non-.ok sealed to none
cendSpec : ProofsLean.Problem cendSealedMachine
  -- PE0 projection: input word at LM0 long address 0, output pair at LM1 long address 0,
  -- post: readPair .lm1 (...) 0 = byteSwap64 input, bit-exact
cendWitness : BitVec 64 := 0x0102030405060708
```

The input is a single 64-bit word per PE (`$lm[0:2]` projected to long address
0); the postcondition observes PE `n0c0b0m0p0` only and is bit-exact.  Both are
weakenings/strengthenings as follows: observing one PE is a weakening (sound
for a lower bound); bit-exactness is *stronger* than the official `1e-4`
tolerance (the formal lower bound is for the stronger specification).

### 2.2 Unconditional refutations

```
cendEmpty_not_correct : ¬ Correct cendSealedMachine cendSpec []
cendNop_not_correct   : count → wait → ¬ Correct ... [.nop count wait]
cendMv_not_correct    : transfer → ¬ Correct ... [.mv transfer]
cendPE_checkFalse_not_correct, cendPE_waitPending_not_correct,
cendPE_unsupported_not_correct, cendPE_notSupported_not_correct,
cendPE_noforward_not_correct
```

All use the witness `cendWitness`, whose target pair
`0x0807060504030201` is non-zero, while LM1 starts at zero.

### 2.3 Exact reductions

```lean
CendPELinesRefuted : Prop :=
  ∀ expressions, ¬ Correct cendSealedMachine cendSpec [.pe expressions]

cendLowerBound_two_of_peLines :
  CendPELinesRefuted → LowerBound cendSealedMachine cendSpec 2
cendLowerBound_two_iff_peLines :
  LowerBound cendSealedMachine cendSpec 2 ↔ CendPELinesRefuted

CendPEAccepted (expressions) : Prop :=
  checkParsedTopLine ... = true ∧
  any (parsedExprWaitPending ...) = false ∧
  any parsedExprIsUnsupportedRustAlu = false ∧
  all parsedExprIsSupportedPELineProducer = true
CendPEUnrefuted (expressions) : Prop :=
  CendPEAccepted expressions ∧ ¬ CendAllNoForward expressions

cendLowerBound_two_of_unrefuted :
  (∀ e, CendPEUnrefuted e → ¬ Correct ... [.pe e]) →
  LowerBound cendSealedMachine cendSpec 2

CendTwoLinesRefuted : Prop :=
  ∀ first second, cost first = 1 → cost second = 1 →
    ¬ Correct cendSealedMachine cendSpec [first, second]

cendLowerBound_three_of_residuals :
  CendPELinesRefuted → CendTwoLinesRefuted →
  LowerBound cendSealedMachine cendSpec 3
cendLowerBound_three_iff_residuals :
  LowerBound cendSealedMachine cendSpec 3 ↔
    CendPELinesRefuted ∧ CendTwoLinesRefuted
```

`cend_score_lt_three_iff` records the case split: a program of score below 3 is
empty, a single line of cost at most 2, or two unit-cost lines.  The single
cost-2 case is only a `nop/2` and is refuted by the frame lemma.

## 3. Lean deliverable II — `ValueProvenance.lean`

Problem-free, state-general.  `OneStageValue S` is the closure of a set `S` of
32-bit words under: old words, `0`, one `evaluateParsedIntegerAlu` application to
two buses whose words are in the closure, a masked merge, and half rounding.

Proved:

```lean
prepareParsedMaskedWriteWithForwarding_data_eq :
  prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced = .ok write →
  ∃ x y output,
    readWithForwarding ... sourceX = .ok x ∧
    readWithForwarding ... sourceY = .ok y ∧
    evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
    write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value)

prepareParsedMaskedWriteWithForwarding_data_in_closure :
  (prepared ... = .ok write) →
  (∀ i, OneStageValue S (unpackALUBus x i)) →
  (∀ i, OneStageValue S (unpackALUBus y i)) →
  ∀ i, OneStageValue S (write.data i)

welcomeCommitStep_lm1_closure :
  OneStageValue S (files.lm1 target) →
  (every .lm1 destination avoids target or its data words are in S) →
  OneStageValue S ((welcomeCommitStep files write).lm1 target)

commitParsedMaskedWrites_lm1_closure :
  same for a list of writes

executeIntegerProducerLineAtPECore_lm1_closure_of_commit :
  next.peRegisters pe = commit (prepared ++ floatWrites) →
  OneStageValue S (old .lm1 target) →
  (data words of prepared and floatWrites in closure) →
  OneStageValue S (new .lm1 target)

executeIntegerProducerLineAtPECore_lm1_closure_floatFree :
  float-filter empty → same with the integer preparation list only

LinePreparedDataInClosure (state) (pe) (expressions) (S) : Prop :=
  every write of the actual integer preparation list has its data words in S

executeIntegerProducerLineAtPECore_lm1_closure_floatFree_of_line :
  executed → float-filter empty →
  OneStageValue S (old .lm1 target) →
  LinePreparedDataInClosure state pe expressions S →
  OneStageValue S (new .lm1 target)
```

`LinePreparedDataInClosure` is the **single named executor link** left open.
Its direct-memory branch is
`prepareParsedMaskedWriteWithForwarding_data_in_closure`; the other seven
branches of `prepareParsedIntegerALUExprCycle` need the same induction.  The
read-source companion is `ReadWordsInClosure`.

The **remaining executor link** is named `LinePreparedDataInClosure` (with the
prepared-write-level companion `PlainALUPreparedDataInClosure`): for a prepared
write of the plain integer-ALU cycle, its data words are in the closure
whenever the register-file/forwarding words are.  The direct-memory branch is
exactly `prepareParsedMaskedWriteWithForwarding_data_in_closure`; the
mask/OMR/BAR/constant/no-write branches need the same induction over
`prepareParsedIntegerALUExprCycle`.  `ReadWordsInClosure` states the companion
read-source closure (memory, known forwarding, fixed).

## 4. What remains for `LowerBound 3` unconditionally

1. **One-line `.pe` value argument** (`CendPELinesRefuted`):
   * discharge `PlainALUPreparedDataInClosure` for all eight branches of
     `prepareParsedIntegerALUExprCycle`;
   * add the non-plain families (float MAU, matrix, L1/L2, `msl`/`msr`,
     block float) to the closure or refute them by frame/zero arguments;
   * instantiate `ReadWordsInClosure` at the initial state;
   * prove the finite target exclusion for `OneStageValue S x` at
     `x = 0x0102030405060708` (the Python table says this holds; a Lean
     certificate list would make it kernel-checked).
2. **Two-unit-line obligation** (`CendTwoLinesRefuted`):
   * the one-stage closure above applied to line 1;
   * the two-stage value table / finite certificate for line 2;
   * the `imm P` program-dependent witness case.

Until these are closed, the theorems here are **reductions**, not an
unconditional `LowerBound 2`/`3` on the sealed machine.

## 5. Restrictions / caveats

* The machine is the **sealed** one: `step := executeNormalizedLine`, with
  `.failure`/`.unknown` mapped to `none`.  The issue/address-mode/PE-hazard/
  block-hazard checks of the whole machine are not composed here.
* The specification observes **one PE** and is **bit-exact**.  The one-PE
  observation weakens the official problem (sound for a lower bound); the
  bit-exact postcondition strengthens it (the official judge allows `1e-4`).
  The refutations exhibit a non-zero target against an untouched zero word, so
  the discrepancy is at least `0x0807060504030201`, far above `1e-4`; this
  robustness is argued, not formalised as a tolerance-valued postcondition.
* The search covers a structured operand subset, not every legal VSM operand
  combination; the value-closure argument is the semantic reason behind the
  search, not a formal completeness claim for the assembler grammar.
* The float-MAU model (`SingleFMA`) and the emulator are known to disagree on
  some `$aluf`/OMR-mask interactions elsewhere in the repository; this module's
  value core is about the integer ALU and does not depend on that path.

## 6. Reproduction

```sh
# baseline
python3 judge/judge-py/judge.py \
  problems/challenge/12.convert-endian/testcase.vsm \
  problems/challenge/12.convert-endian/answer.vsm

# structured one/two-line search (bounded; run in foreground)
python3 -u research/experiments/cend-proof/search_clean.py

# value-closure witness table
python3 research/experiments/cend-proof/value_table.py

# Lean
cd proofs_lean
lake build ProofsLean.ConvertEndianLowerBound
lake build ProofsLean.ValueProvenance
```

## 7. File map

| file | content |
|---|---|
| `harness.py` | assemble/emulate/judge harness |
| `value_closure.py`, `value_table.py`, `value_table.json` | two-stage lane-op witness analysis |
| `search_clean.py`, `search_one.txt` | bounded structured one-line execution samples |
| `probe1.py`, `sweep_single.py` | earlier hand probes |
| `../ProofsLean/ConvertEndianLowerBound.lean` | challenge problem + reductions |
| `../ProofsLean/ValueProvenance.lean` | problem-free one-stage value provenance |
