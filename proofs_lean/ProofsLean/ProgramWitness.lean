import ProofsLean.CendUnconditional
import ProofsLean.InputDependence
import ProofsLean.WelcomePlainClose
import ProofsLean.ByteSwapKernel

/-! # Program-dependent witnesses: a diagonalisation kernel for one-line refutations

`ProofsLean/CendUnconditional.lean` closed the `.matrixRead` and inert families of
`12.convert-endian` and then recorded *why* the remaining families cannot be
refuted by a fixed witness: the `.immediate` payload and the `$msb1` fixed
source are **line constants**, and a single `.word` store of the `$msb1`
pattern into LM1 word `0` is *correct* at the input `0x0000000000000080`.  A
correctness refutation must therefore choose its input **after** seeing the
line.  This module builds that technique once, abstractly, and instantiates it.

## The idea

The target of `12.convert-endian` is `byteSwap64`, a bijection of `BitVec 64`.
A single `.pe` line, however, can only see the input through

* the two 32-bit halves of LM0 long word `0` (the high half in LM0 word `0`,
  the low half in LM0 word `1`), and
* finitely many *line constants*: the `.immediate` payloads of its rows, the
  `.fixed` operand channels (`$msb1`, `$peid`, `$subpeid`, `$l2bid`, `$l1bid`,
  `$mabid`) and the mask/forwarding/hazard/matrix channels, which are fixed by
  the initial state.

Hence whatever the line computes, its observed pair is a function of *some
proper subset* of the input halves (or of no input data at all).  The target
pair, on the other hand, is `byteSwap64`, a **bijection** of `BitVec 64`: its
high word is the byte reversal of the low input half and its low word the byte
reversal of the high input half, so it separates inputs that differ in *either*
half.  Two inputs that agree on the halves the line can read are therefore
indistinguishable to the line while their targets differ, so **at least one of
them is a counterexample**.  This is the diagonalisation: the witness is built
from the line's own signature, not chosen in advance.

Five forms are proved here:

* `cendPE_not_correct_of_freeHalves` — the **collision form**.  Given a set
  `halves` of input halves, a proof that some half is outside it, and a proof
  that the line's observed pair is the same at any two inputs agreeing on
  `halves`, the line is refuted.  The two probe inputs are `0` and `0` with the
  free half set to `1`; their targets are `0` and `0x0000000001000000` (high
  half free) or `0x0100000000000000` (low half free), so they differ.
* `cendPE_not_correct_of_signature` — the same on `LineSignature`, the structure
  that names the finite data (payloads, fixed channels, read halves, channels).
* `cendPE_not_correct_of_factorsThrough` — the **fixed-function form**: a line
  whose committed pair is a fixed function `f` of the input is refuted once `f`
  is known to factor through a read set that misses a half.
* `cendPE_not_correct_of_inputIndependent` — the empty-read-set case, which is
  the shape of every zero-data family.
* `cendPE_not_correct_of_candidatePair` — the **programme-dependent witness
  form**.  Let `half` be a half the line cannot read and `x` any base input; if
  the line's observed pair is the same at `write half x 0` and `write half x 1`,
  then it is wrong at one of the two.  The candidates are built from the
  line's own read set (which half is free) and from the line's own output at
  `x`; the targets differ because `byteSwap64` is injective
  (`byteSwap64_injective`, from the project's `ByteSwap.byteSwap64_involutive`)
  while the two inputs differ in the written half.  No byte-level computation
  is needed, so this module introduces no `bv_decide` axiom of its own.

The abstract pigeonhole is stated once, machine-generally, in §2
(`not_correct_of_collision`), together with the finite-range exclusion lemma
asked for by the task (`not_mem_of_range_subset`,
`exists_ne_of_range_subset_of_surjective`).

## What is closed here

§4 closes the **whole constant family end-to-end**: every single-row `.pe` line
whose row is a plain `.zero` or `.immediate` (any destination, any width, any
mask, any payload) is refuted.  The proof is a corollary of the skeleton with
the empty read set: `welcomeIntegerPrep_constant_eq`
(`ProofsLean/WelcomePlainClose.lean`) says the executor's own prepared write
list of such a row is *the same* at any two initial states — only the mask
channel matters, and that is fixed — so the observed pair is input-independent;
`commitParsedMaskedWrites_lm1_congr` lifts this to the commit.  This is exactly
the class the `CendUnconditional` finding identified as "cannot be refuted by a
fixed witness", and the technique refutes it without ever computing a payload.

§5 reduces everything else to **one uniform obligation**,
`CendLineWitnessObligation`: for every line outside the two classes already
closed by `CendUnconditional`, exhibit a *proper* set of input halves that
determines the observed pair.  `cendLowerBound_two_of_lineWitness` composes that
obligation with `CendUnconditional`'s reduction to
`LowerBound cendSealedMachine cendSpec 2`, and
`cendLowerBound_two_of_witnessValueResidual` does the same in the
`CendValueResidual` style.  The per-family instances
(`CendPlainALUNarrowWitness`, `CendPlainALUWideWitness`, `CendMslMsrWitness`,
`CendFloatMAUWitness`, `CendBlockFloatWitness`, `CendL1BMBroadcastWitness`) are
stated with the exact
executor lemma each one still needs, so the remaining work is a list of
congruence and read-set proofs rather than a value analysis.  The bridge from a
read set to the executor's agreement hypothesis is provided here
(`cendInitialPERegisters_agree_of_avoids`,
`cendInitialPERegisters_agree_of_halves`): the initial files differ only in LM0
words `0` and `1`.

## Trust

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms, and no
existing module is edited.  Every result below depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`, with one exception:
`cendPE_not_correct_of_candidatePair` (through `byteSwap64_injective`) also uses
`ByteSwap.byteSwap64_involutive`'s pre-existing `_native.bv_decide` axiom from
`ProofsLean/ByteSwap.lean`.  The collision form
(`cendPE_not_correct_of_freeHalves`), the fixed-function form, the signature
kernel, the whole constant family and every bound reduction are free of it.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

open Issue
open PEMemory

/-- The sealed step of a one-line `.pe` program at an initial input, as a
reducible abbreviation.  Stating it as an `abbrev` keeps the result type `State`
rather than the machine's projection `cendSealedMachine.State`: the tactic
unifier does not unfold the non-reducible `cendSealedMachine` at `implicit`
transparency, so equations stated at the projection type do not compose with
equations stated at `State`. -/
noncomputable abbrev cendStep (expressions : List NormalizedExpr) (input : BitVec 64) :
    Option State :=
  cendSealedMachine.step (.pe expressions) (cendInitialState input)

/-! ## 1. The finite data of one `.pe` line at the initial state

Everything a line can use is either one of the two 32-bit halves of the input
word or a constant fixed by the line and the initial state.  This section names
those two groups. -/

/-- The two 32-bit halves of the 64-bit input word.  `high` is the half the
initial state stores in LM0 word `0`, `low` the half in LM0 word `1`. -/
inductive InputHalf where
  /-- The high 32 bits, LM0 word `0`. -/
  | high
  /-- The low 32 bits, LM0 word `1`. -/
  | low
  deriving DecidableEq, Repr

namespace InputHalf

/-- The 32-bit value the input carries in this half. -/
def value : InputHalf → BitVec 64 → BitVec 32
  | .high, x => x.extractLsb' 32 32
  | .low, x => x.extractLsb' 0 32

/-- Replace one half of the input word, keeping the other. -/
def write : InputHalf → BitVec 64 → BitVec 32 → BitVec 64
  | .high, x, v => v ++ x.extractLsb' 0 32
  | .low, x, v => x.extractLsb' 32 32 ++ v

@[simp] theorem value_high (x : BitVec 64) : value .high x = x.extractLsb' 32 32 := rfl

@[simp] theorem value_low (x : BitVec 64) : value .low x = x.extractLsb' 0 32 := rfl

@[simp] theorem write_high (x : BitVec 64) (v : BitVec 32) :
    write .high x v = v ++ x.extractLsb' 0 32 := rfl

@[simp] theorem write_low (x : BitVec 64) (v : BitVec 32) :
    write .low x v = x.extractLsb' 32 32 ++ v := rfl

/-- Writing a half reads that half back. -/
theorem value_write_same (half : InputHalf) (x : BitVec 64) (v : BitVec 32) :
    value half (write half x v) = v := by
  cases half
  · exact BitVec.extractLsb'_append_eq_left
  · exact BitVec.extractLsb'_append_eq_right

/-- Writing one half leaves the other half untouched. -/
theorem value_write_other (half other : InputHalf) (x : BitVec 64) (v : BitVec 32)
    (different : other ≠ half) :
    value other (write half x v) = value other x := by
  cases half <;> cases other <;>
    first
      | exact absurd rfl different
      | exact BitVec.extractLsb'_append_eq_right
      | exact BitVec.extractLsb'_append_eq_left

/-- Writing back the value of a half leaves the input unchanged. -/
theorem write_value (half : InputHalf) (x : BitVec 64) :
    write half x (value half x) = x := by
  cases half
  · exact BitVec.extractLsb'_append_extractLsb'
  · exact BitVec.extractLsb'_append_extractLsb' 

end InputHalf

/-- **A line's observed pair factors through a set of input halves** when two
inputs that agree on every half of the set produce the same observed pair.  This
is the semantic content of "the line's signature": the finite data listed in
`LineSignature` determines which halves can appear here. -/
def OutputFactorsThrough (f : BitVec 64 → BitVec 64) (halves : Finset InputHalf) : Prop :=
  ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) → f x = f y

/-- The non-register channels a line reads at the initial state.  None of them
depends on the input: the mask register file, the forwarding slots, the
mask/hazard control record and the matrix store are the same at every input. -/
structure LineChannels where
  /-- The observed PE's OMR mask register file. -/
  maskRegisters : ProofsLean.MNCore.Masks.RegisterFile
  /-- The observed PE's forwarding slots (all `poison` at the initial state). -/
  slots : ProofsLean.MNCore.Forwarding.Slots
  /-- The mask directive, BAR/T context and hazard clock. -/
  control : ParsedMaskExecutionControl
  /-- The matrix store of the observed PE's group/L2B/L1B slice. -/
  matrixStore : ParsedMatrixReadStore

/-- The channels of one state at one PE. -/
def channelsOf (state : State) (pe : PEId) : LineChannels where
  maskRegisters := (state.peRegisters pe).maskRegisters
  slots := stateForwardingSlots state pe
  control := parsedPEHazardControl state pe
  matrixStore := state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
    (ParsedIntegerContext.ofLinearIndex pe).l2b
    (ParsedIntegerContext.ofLinearIndex pe).l1b

/-! ### The LM0 footprint of one operand

A `.mem` source of bank LM0 reads `count` words starting at the resolved
address.  The resolved address is one of the four region addresses (selected by
the BAR/T channel) or, under `tIndirect`, address `0`; taking the union over all
four, widened to four words, is a sound over-approximation.  Only LM0 words `0`
and `1` carry input data at the initial state. -/

/-- The address candidates of a region: the four explicit addresses, plus
address `0` when the region is `T`-indirect (the `T` bank is zero at the initial
state, so an indirect region resolves to `0`). -/
def Issue.Region.addressCandidates (region : Region) : List Nat :=
  let bases := [region.address0, region.address1, region.address2, region.address3]
  if region.tIndirect then 0 :: bases else bases

/-- The LM0 word addresses a region may touch.

The resolved address of a region is *width-aligned down*
(`ParsedOperand.toDirectMemoryAccessMode?` computes
`raw / width.words * width.words`), so a region whose base is `1` and whose width
is longer than one word resolves to `0` and reads the input's high half.
The over-approximation therefore widens every candidate address by three words
on **both** sides, and the region's four candidate addresses are all included
because the cycle selects among them.  With `tIndirect` the `T` word is added
(`tWord = 0` at every initial state, so the address equals the aligned base). -/
def Issue.Region.lm0Coverage (region : Region) : Finset Nat :=
  (region.addressCandidates.foldr
    (fun base acc => acc ∪ ((Finset.range 7).image (fun index => base + index - 3))) ∅)

/-- The input halves a single operand may read. -/
def Issue.ParsedOperand.inputHalves : ParsedOperand → Finset InputHalf
  | .mem access _ _ _ _ =>
      if access.bank = Issue.Bank.lm0 then
        ((if 0 ∈ access.region.lm0Coverage then {InputHalf.high} else ∅) ∪
          (if 1 ∈ access.region.lm0Coverage then {InputHalf.low} else ∅))
      else ∅
  | _ => ∅

/-- The `.immediate` payload a row contributes to its signature. -/
def Issue.ParsedOp.immediatePayloads : ParsedOp → List (BitVec 32)
  | .immediate value _ => [value]
  | _ => []

/-- The fixed operand channels one operand mentions. -/
def Issue.ParsedOperand.fixedChannels : ParsedOperand → Finset ParsedFixed
  | .fixed kind => {kind}
  | _ => ∅

/-- **The finite data of one `.pe` line.**  `readHalves` is a sound
over-approximation of the input halves the line can read; `immediates`,
`fixedOperands`, `operands` and `ops` are the line constants; `channels` are the
initial-state channels, which are input-independent. -/
structure LineSignature where
  /-- Every source and destination operand of the line. -/
  operands : List ParsedOperand
  /-- Every row's opcode, carrying the `.immediate` payloads. -/
  ops : List ParsedOp
  /-- The `.immediate` payloads, projected out of `ops`. -/
  immediates : List (BitVec 32)
  /-- The fixed operand channels the line mentions. -/
  fixedOperands : Finset ParsedFixed
  /-- The input halves the line may read. -/
  readHalves : Finset InputHalf
  /-- The input-independent mask/forwarding/control/matrix channels. -/
  channels : LineChannels

namespace LineSignature

/-- The operands of a line, in order. -/
def operandsOf (expressions : List NormalizedExpr) : List ParsedOperand :=
  (expressions.map NormalizedExpr.toParsed).flatMap (fun expression =>
    expression.sources ++ expression.destinations)

/-- The input halves a line may read. -/
def readHalvesOf (expressions : List NormalizedExpr) : Finset InputHalf :=
  (operandsOf expressions).foldr (fun operand acc => acc ∪ operand.inputHalves) ∅

/-- The fixed operand channels a line mentions. -/
def fixedOperandsOf (expressions : List NormalizedExpr) : Finset ParsedFixed :=
  (operandsOf expressions).foldr (fun operand acc => acc ∪ operand.fixedChannels) ∅

/-- The `.immediate` payloads of a line. -/
def immediatesOf (expressions : List NormalizedExpr) : List (BitVec 32) :=
  (expressions.map NormalizedExpr.toParsed).flatMap (fun expression =>
    expression.op.immediatePayloads)

/-- **The signature of a line at a given initial channel state.** -/
def ofExpressions (channels : LineChannels) (expressions : List NormalizedExpr) :
    LineSignature where
  operands := operandsOf expressions
  ops := (expressions.map NormalizedExpr.toParsed).map (fun expression => expression.op)
  immediates := immediatesOf expressions
  fixedOperands := fixedOperandsOf expressions
  readHalves := readHalvesOf expressions
  channels := channels

/-- A signature is **free** when at least one input half is outside its read
set: the line cannot see that half, so the diagonalisation applies. -/
def Free (signature : LineSignature) : Prop :=
  ∃ half, half ∉ signature.readHalves

/-- **The signature determines the observed pair.**  Two initial states whose
inputs agree on every half of the read set produce the same observed pair after
a successful step of the line.  This is the single semantic fact each family
proof has to deliver; the diagonalisation below turns it into a refutation. -/
def Determined (signature : LineSignature) (expressions : List NormalizedExpr) : Prop :=
  ∀ x y, (∀ half ∈ signature.readHalves, InputHalf.value half x = InputHalf.value half y) →
    ∀ nextX nextY : State,
      cendStep expressions x = some nextX →
      cendStep expressions y = some nextY →
      cendOutputPair nextX = cendOutputPair nextY

end LineSignature

/-! ### The fixed operand channels at the observed PE

`$l2bid`, `$l1bid`, `$mabid`, `$peid` and `$subpeid` are all `0` at PE
`n0c0b0m0p0`; `$msb1` is the precision's sign bit.  So the fixed channels carry
a line constant and nothing else. -/

theorem cendFixedOperandValue (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    ParsedFixed.integerValue fixed precision
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe =
    if fixed = .msb1 then 2 ^ (precision.width - 1) else 0 := by
  have index : (cendPE : Nat) = 0 := rfl
  rw [parsed_fixed_integerValue_ofLinearIndex]
  cases fixed <;> simp [index]

/-! ### The channels are fixed by the initial state -/

theorem cendInitialState_channels_eq (x y : BitVec 64) :
    channelsOf (cendInitialState x) cendPE = channelsOf (cendInitialState y) cendPE := rfl

theorem cendInitialState_channels_maskRegisters (x : BitVec 64) :
    (channelsOf (cendInitialState x) cendPE).maskRegisters =
      zeroInitialPERegisterFiles.maskRegisters := rfl

theorem cendInitialState_channels_slots (x : BitVec 64) :
    (channelsOf (cendInitialState x) cendPE).slots =
      stateForwardingSlots (cendInitialState 0) cendPE := rfl

/-! ### What the input actually changes

The two initial register files differ only in LM0 words `0` and `1`.  Every
family refutation ends by feeding `FilesAgreeOn` at some read set into the
executor's congruence lemma, so this is the bridge from "the line reads these
words" to "the line cannot tell the two inputs apart". -/

/-- **Initial files agree outside the two input words.** -/
theorem cendInitialPERegisters_agree_of_avoids (R : Set WordRef)
    (avoids : ∀ w ∈ R, w.1 = PEMemory.Bank.lm0 → w.2.val ≠ 0 ∧ w.2.val ≠ 1)
    (x y : BitVec 64) :
    FilesAgreeOn R (cendInitialPERegisters x) (cendInitialPERegisters y) := by
  intro w member
  obtain ⟨bank, address⟩ := w
  cases bank with
  | lm0 =>
      obtain ⟨neZero, neOne⟩ := avoids ⟨.lm0, address⟩ member rfl
      show (cendInitialPERegisters x).lm0 address = (cendInitialPERegisters y).lm0 address
      have neZero' : address.val ≠ 0 := neZero
      have neOne' : address.val ≠ 1 := neOne
      simp [cendInitialPERegisters_lm0_eq, neZero', neOne']
  | lm1 => rfl
  | grf0 => rfl
  | grf1 => rfl
  | t => rfl

/-- **Initial files agree on any read set covered by a set of input halves.** -/
theorem cendInitialPERegisters_agree_of_halves (halves : Finset InputHalf)
    (R : Set WordRef)
    (covered : ∀ w ∈ R, w.1 = PEMemory.Bank.lm0 →
      (w.2.val = 0 → InputHalf.high ∈ halves) ∧
      (w.2.val = 1 → InputHalf.low ∈ halves))
    (x y : BitVec 64)
    (agreeHalves : ∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) :
    FilesAgreeOn R (cendInitialPERegisters x) (cendInitialPERegisters y) := by
  intro w member
  obtain ⟨bank, address⟩ := w
  cases bank with
  | lm0 =>
      obtain ⟨zeroCase, oneCase⟩ := covered ⟨.lm0, address⟩ member rfl
      show (cendInitialPERegisters x).lm0 address = (cendInitialPERegisters y).lm0 address
      rw [cendInitialPERegisters_lm0_eq, cendInitialPERegisters_lm0_eq]
      by_cases zero : address.val = 0
      · have h := agreeHalves .high (zeroCase zero)
        simpa [cendInitialPERegisters_lm0_eq, InputHalf.value, zero] using h
      · by_cases one : address.val = 1
        · have h := agreeHalves .low (oneCase one)
          simpa [cendInitialPERegisters_lm0_eq, InputHalf.value, zero, one] using h
        · simp [cendInitialPERegisters_lm0_eq, zero, one]
  | lm1 => rfl
  | grf0 => rfl
  | grf1 => rfl
  | t => rfl

theorem cendInitialState_channels_control (x : BitVec 64) :
    (channelsOf (cendInitialState x) cendPE).control =
      parsedPEHazardControl (cendInitialState 0) cendPE := rfl

/-! ## 2. The diagonalisation kernel

The two abstract facts the technique rests on:

* a finite range excludes a target value (`not_mem_of_range_subset`), and a
  surjective target meets any value, so some input misses
  (`exists_ne_of_range_subset_of_surjective`);
* two inputs with different targets cannot both satisfy a postcondition whose
  observation is the same at both (`not_correct_of_collision`).

The second is the one that makes the witness *program dependent*: the pair of
inputs is chosen from the line's signature, and the refutation does not know
which of the two is the counterexample. -/

/-- **Finite-range exclusion.**  If a line's committed value always lies in a
finite set `S`, then it never equals a target value outside `S`. -/
theorem not_mem_of_range_subset {Input Value : Type} [DecidableEq Value]
    (f : Input → Value) (S : Finset Value) (range : ∀ x, f x ∈ S)
    {target : Value} (outside : target ∉ S) (x : Input) :
    f x ≠ target := by
  intro same
  exact outside (same ▸ range x)

/-- **Finite-range exclusion, target-varying form.**  If the line's committed
value lies in a finite set `S` and the target is surjective onto a value outside
`S`, then *some* input makes the line incorrect.  For `12.convert-endian` the
target `byteSwap64` is an involution, hence surjective. -/
theorem exists_ne_of_range_subset_of_surjective {Input Value : Type} [DecidableEq Value]
    (f : Input → Value) (target : Input → Value) (S : Finset Value)
    (range : ∀ x, f x ∈ S) (outside : ∃ value, value ∉ S)
    (surjective : ∀ value, ∃ x, target x = value) :
    ∃ x, f x ≠ target x := by
  obtain ⟨value, outsideValue⟩ := outside
  obtain ⟨x, targetEq⟩ := surjective value
  refine ⟨x, ?_⟩
  rw [targetEq]
  exact not_mem_of_range_subset f S range outsideValue x

/-- **The collision pigeonhole.**  A program cannot be correct if two admissible
inputs have different target values but the same observed value: a correct
program would have to report both targets at once. -/
theorem not_correct_of_collision {m : ProofsLean.Machine} {spec : ProofsLean.Problem m}
    {Observed : Type} (program : ProofsLean.Program m) (observed : m.State → Observed)
    (target : m.Input → Observed) (x y : m.Input)
    (admissibleX : spec.admissible x) (admissibleY : spec.admissible y)
    (different : target x ≠ target y)
    (collide : ∀ resultX resultY,
      ProofsLean.execute m program (spec.initial x) = some resultX →
      ProofsLean.execute m program (spec.initial y) = some resultY →
      observed resultX = observed resultY)
    (reports : ∀ input state, spec.post input state → observed state = target input) :
    ¬ ProofsLean.Correct m spec program := by
  intro correct
  obtain ⟨resultX, executedX, postX⟩ := correct.2 x admissibleX
  obtain ⟨resultY, executedY, postY⟩ := correct.2 y admissibleY
  have same := collide resultX resultY executedX executedY
  rw [reports x resultX postX, reports y resultY postY] at same
  exact different same

/-! ## 3. The one-line kernel for `12.convert-endian`

The kernel comes in two strengths.  The **collision form**
(`cendPE_not_correct_of_freeHalves`) fixes the two probe inputs (`0` and `0`
with the free half set to `1`) and proves their targets differ by evaluation.
The **programme-dependent form** (`cendPE_not_correct_of_candidatePair`) lets
the base input be anything and gets the difference from injectivity of
`byteSwap64` alone, which is the only structural fact about the target used in
this module. -/


/-- `byteSwap64` is injective: it is a byte permutation.

This is the *only* structural fact about the specification the witness technique
needs, and it is the project's existing `ByteSwap.byteSwap64_involutive`
(`ProofsLean/ByteSwap.lean`) applied to `Function.Involutive.injective`.  No
`bv_decide` is used in this module, so no new `_native` axiom is introduced; the
single nonstandard axiom in the closure of
`cendPE_not_correct_of_candidatePair` is the one `ByteSwap.lean` already
carries. -/
theorem byteSwap64_injective : Function.Injective byteSwap64 :=
  byteSwap64_injective_kernel

/-- **The two-candidate programme-dependent witness.**  Let `half` be an input
half the line does not read, `x` any base input, and suppose the line's observed
pair is the same at the two inputs `write half x 0` and `write half x 1`.  Then
the line is incorrect at one of them.

Both candidates are built from the signature (`half` is the free half the read
set misses) and from an arbitrary input `x` — the line's own output at `x` can
serve as the base — and the targets differ because `byteSwap64` is injective
while the two inputs differ in the written half.  This is the sharpest form of
the technique that needs no byte-level computation: the pair of candidates is
the witness, and the refutation does not know which of the two is the
counterexample. -/
theorem cendPE_not_correct_of_candidatePair (expressions : List NormalizedExpr)
    (half : InputHalf) (x : BitVec 64)
    (same : ∀ (nextZero nextOne : State),
      cendStep expressions (InputHalf.write half x 0) = some nextZero →
      cendStep expressions (InputHalf.write half x 1) = some nextOne →
      cendOutputPair nextZero = cendOutputPair nextOne) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  have different : byteSwap64 (InputHalf.write half x 0) ≠
      byteSwap64 (InputHalf.write half x 1) := by
    intro coincident
    have inputsEq : InputHalf.write half x 0 = InputHalf.write half x 1 :=
      byteSwap64_injective coincident
    have valueEq : InputHalf.value half (InputHalf.write half x 0) =
        InputHalf.value half (InputHalf.write half x 1) := by rw [inputsEq]
    rw [InputHalf.value_write_same, InputHalf.value_write_same] at valueEq
    exact absurd valueEq (by decide)
  refine not_correct_of_collision (m := cendSealedMachine) (spec := cendSpec)
    ([InstructionLine.pe expressions]) cendOutputPair byteSwap64
    (InputHalf.write half x 0) (InputHalf.write half x 1)
    (cendSpec_admissible _) (cendSpec_admissible _) different ?_ ?_
  · intro resultZero resultOne executedZero executedOne
    rw [cendSpec_initial] at executedZero executedOne
    have stepZero : cendSealedMachine.step (.pe expressions)
        (cendInitialState (InputHalf.write half x 0)) = some resultZero := by
      simpa [ProofsLean.execute] using executedZero
    have stepOne : cendSealedMachine.step (.pe expressions)
        (cendInitialState (InputHalf.write half x 1)) = some resultOne := by
      simpa [ProofsLean.execute] using executedOne
    exact same resultZero resultOne stepZero stepOne
  · intro input state post
    exact post

/-- The high observed word is the high half of the observed pair. -/
theorem cendOutputWord0_eq_extract (state : State) :
    cendOutputWord0 state = (cendOutputPair state).extractLsb' 32 32 := by
  rw [cendOutputPair_eq_append]
  exact (BitVec.extractLsb'_append_eq_left).symm

/-- The low observed word is the low half of the observed pair. -/
theorem cendOutputWord1_eq_extract (state : State) :
    cendOutputWord1 state = (cendOutputPair state).extractLsb' 0 32 := by
  rw [cendOutputPair_eq_append]
  exact (BitVec.extractLsb'_append_eq_right).symm

theorem cendTarget_zero : byteSwap64 (0 : BitVec 64) = 0 := by
  decide

theorem cendTarget_writeHigh_one :
    byteSwap64 (InputHalf.write .high 0 1) = 0x0000000001000000 := by
  decide

theorem cendTarget_writeLow_one :
    byteSwap64 (InputHalf.write .low 0 1) = 0x0100000000000000 := by
  decide

/-- **The observed pair is wrong at an input.**  If a successful step at `x`
produces an observed pair different from the target pair at `x`, the line is
incorrect.  This is the single-witness kernel: every family refutation ends
here, and `CendUnconditional.cend_not_correct_of_lm1_zero` is its special case
`observed pair = 0`. -/
theorem cend_not_correct_of_output_ne (expressions : List NormalizedExpr)
    (x : BitVec 64) (next : State)
    (step : cendStep expressions x = some next)
    (wrong : cendOutputPair next ≠ byteSwap64 x) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 x (cendSpec_admissible x)
  rw [cendSpec_initial] at executed
  have stepResult : cendSealedMachine.step (.pe expressions) (cendInitialState x) =
      some result := by
    simpa [ProofsLean.execute] using executed
  have step' : cendSealedMachine.step (.pe expressions) (cendInitialState x) = some next := step
  rw [step'] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst resultEq
  exact wrong post

/-- The stuck-step kernel in `cendStep` form: if the line cannot step at an
input, it is incorrect there. -/
theorem cend_not_correct_of_step_stuck (expressions : List NormalizedExpr)
    (x : BitVec 64) (stuck : cendStep expressions x = none) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cend_not_correct_of_step_none (InstructionLine.pe expressions) x stuck

/-- **The free-half kernel.**  If at most the halves in `halves` determine the
observed pair, and `halves` misses some input half, the line is incorrect.

The two probe inputs are `0` and the input whose free half is `1`; they agree on
`halves` but their target pairs `0` and `0x0100000000000000`/`0x0000000001000000`
differ. -/

theorem cendPE_not_correct_of_freeHalves (expressions : List NormalizedExpr)
    (halves : Finset InputHalf) (free : ∃ half, half ∉ halves)
    (determined : ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
      ∀ nextX nextY : State,
        cendStep expressions x = some nextX →
        cendStep expressions y = some nextY →
        cendOutputPair nextX = cendOutputPair nextY) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  obtain ⟨half, outside⟩ := free
  -- `x = 0` and `y = 0` with the free half set to `1`
  let x : BitVec 64 := 0
  let y : BitVec 64 := InputHalf.write half 0 1
  have agree : ∀ other ∈ halves, InputHalf.value other x = InputHalf.value other y := by
    intro other member
    have different : other ≠ half := by
      intro same
      exact outside (same ▸ member)
    rw [InputHalf.value_write_other half other 0 1 different]
  have different : byteSwap64 x ≠ byteSwap64 y := by
    cases half with
    | high =>
        show byteSwap64 (0 : BitVec 64) ≠ byteSwap64 (InputHalf.write .high 0 1)
        rw [cendTarget_zero, cendTarget_writeHigh_one]
        decide
    | low =>
        show byteSwap64 (0 : BitVec 64) ≠ byteSwap64 (InputHalf.write .low 0 1)
        rw [cendTarget_zero, cendTarget_writeLow_one]
        decide
  refine not_correct_of_collision (m := cendSealedMachine) (spec := cendSpec)
    ([InstructionLine.pe expressions]) cendOutputPair byteSwap64 x y
    (cendSpec_admissible x) (cendSpec_admissible y) different ?_ ?_
  · intro resultX resultY executedX executedY
    rw [cendSpec_initial] at executedX executedY
    have stepX : cendSealedMachine.step (.pe expressions) (cendInitialState x) =
        some resultX := by simpa [ProofsLean.execute] using executedX
    have stepY : cendSealedMachine.step (.pe expressions) (cendInitialState y) =
        some resultY := by simpa [ProofsLean.execute] using executedY
    exact determined x y agree resultX resultY stepX stepY
  · intro input state post
    exact post

/-- **The fixed-function form.**  This is the shape the task states: a line whose
committed pair is a *fixed function* `f` of the input is refuted as soon as `f`
factors through a read set that misses some half — no knowledge of `f` is
needed.  The witness is the free-half probe pair of the kernel above. -/
theorem cendPE_not_correct_of_factorsThrough (expressions : List NormalizedExpr)
    (halves : Finset InputHalf) (free : ∃ half, half ∉ halves)
    (f : BitVec 64 → BitVec 64)
    (output : ∀ (x : BitVec 64) (next : State), cendStep expressions x = some next →
      cendOutputPair next = f x)
    (factors : OutputFactorsThrough f halves) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_not_correct_of_freeHalves expressions halves free
    (fun x y agree nextX nextY stepX stepY => by
      rw [output x nextX stepX, output y nextY stepY]
      exact factors x y agree)

/-- **The signature kernel.**  The free-half kernel stated on `LineSignature`:
a signature whose read set misses an input half, plus the semantic
determination fact for that signature, refutes the line. -/
theorem cendPE_not_correct_of_signature (expressions : List NormalizedExpr)
    (signature : LineSignature) (free : signature.Free)
    (determined : signature.Determined expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_not_correct_of_freeHalves expressions signature.readHalves free determined

/-- **The input-independence corollary.**  A line whose observed pair is the
same at every input is refuted by the same pigeonhole with the empty read set:
the target is not constant.  This is the shape the constant family uses, and it
is also the shape of any "zero-data" family (`.matrixRead`, inert, L1BM
broadcast). -/
theorem cendPE_not_correct_of_inputIndependent (expressions : List NormalizedExpr)
    (independent : ∀ (x y : BitVec 64) (nextX nextY : State),
      cendStep expressions x = some nextX →
      cendStep expressions y = some nextY →
      cendOutputPair nextX = cendOutputPair nextY) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_not_correct_of_freeHalves expressions ∅ ⟨InputHalf.high, by simp⟩
    (fun x y _agree nextX nextY stepX stepY => independent x y nextX nextY stepX stepY)

/-! ## 4. The constant family, end to end

`ProofsLean/CendUnconditional.lean` records that the `.immediate` payload and the
`$msb1` fixed source are *line constants* and that no fixed witness refutes
them.  Here the technique refutes the whole family without ever computing a
payload: the executor's own prepared write list of a plain `.zero`/`.immediate`
row is the same at any two initial states (`welcomeIntegerPrep_constant_eq`,
which needs only the mask channel — fixed by the initial state), so the observed
pair is input-independent, and the empty read set is a *proper* subset.  The
refutation is then the skeleton at `halves = ∅`. -/

/-- **The line-level extraction for a plain line, at the `12.convert-endian`
initial state.**  A successful sealed step of a plain `.alu`/`.zero`/`.immediate`
line commits the executor's own integer-stage preparation list at the initial
PE-0 register file.  This is `WelcomePlainClose.welcomeSealed_pe_prepared`
re-proved on `cendSealedMachine` (its step is the same function). -/
theorem cendSealed_pe_prepared (expressions : List NormalizedExpr) (state : State)
    {next : State}
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (step : cendSealedMachine.step (.pe expressions) state = some next) :
    ∃ writes slots bars,
      welcomeIntegerPrep state welcomePE (expressions.map NormalizedExpr.toParsed)
          = .ok (writes, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) writes := by
  have executed : executeNormalizedLine (InstructionLine.pe expressions).toNormalizedLine
      state = .ok next := cendSealed_step_ok step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions) state =
      .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  have accepted := (executeIntegerProducerInstructionLine_pe_conditions expressions state next
    lineExecuted).1
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions state next
      accepted plain lineExecuted
  have filteredEq := plain_peFilter_eq_self (expressions.map NormalizedExpr.toParsed) plain
  rw [filteredEq] at walkExecuted
  have floatEmpty := plain_floatFilter_eq_nil (expressions.map NormalizedExpr.toParsed) plain
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerLineAtPEs_prepared (expressions.map NormalizedExpr.toParsed)
      (List.finRange 4096) state nextPEs floatEmpty walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  exact ⟨writes, slots, bars, prep, by rw [nextEq]; simpa using committed⟩

/-- **The constant family is input independent.**  A plain `.zero`/`.immediate`
row produces the same observed pair at any two inputs: the executor's prepared
list depends only on the mask channel, and the commit only on the old LM1 bank,
which is zero at every initial state. -/
theorem cendPE_constantLine_inputIndependent (e : NormalizedExpr)
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (constant : e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned) :
    ∀ (x y : BitVec 64) (nextX nextY : State),
      cendStep [e] x = some nextX → cendStep [e] y = some nextY →
      cendOutputPair nextX = cendOutputPair nextY := by
  intro x y nextX nextY stepX stepY
  have plainList : ([e].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
    simpa using plain
  have machineStepX : cendSealedMachine.step (.pe [e]) (cendInitialState x) = some nextX :=
    stepX
  have machineStepY : cendSealedMachine.step (.pe [e]) (cendInitialState y) = some nextY :=
    stepY
  obtain ⟨writesX, slotsX, barsX, prepX, commitX⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState x) plainList machineStepX
  obtain ⟨writesY, slotsY, barsY, prepY, commitY⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState y) plainList machineStepY
  have prepEq : welcomeIntegerPrep (cendInitialState x) welcomePE [e.toParsed] =
      welcomeIntegerPrep (cendInitialState y) welcomePE [e.toParsed] :=
    welcomeIntegerPrep_constant_eq (cendInitialState x) (cendInitialState y) e.toParsed
      plain constant rfl rfl rfl rfl
  have writesEq : writesX = writesY := by
    have chained : welcomeIntegerPrep (cendInitialState x) welcomePE [e.toParsed] =
        .ok (writesX, slotsX, barsX) := prepX
    rw [prepEq] at chained
    have triple := chained.symm.trans prepY
    injection triple with tripleEq
    exact (Prod.mk.inj tripleEq).1
  have lm1Eq : (nextX.peRegisters cendPE).lm1 = (nextY.peRegisters cendPE).lm1 := by
    have commitX' : nextX.peRegisters cendPE =
        commitParsedMaskedWrites ((cendInitialState x).peRegisters cendPE) writesX := commitX
    have commitY' : nextY.peRegisters cendPE =
        commitParsedMaskedWrites ((cendInitialState y).peRegisters cendPE) writesY := commitY
    rw [commitX', commitY', writesEq]
    exact commitParsedMaskedWrites_lm1_congr _ _ _ _ rfl rfl
  unfold cendOutputPair
  rw [lm1Eq]

/-- **The constant family is refuted**, by the skeleton with the empty read set:
the observed pair does not depend on the input at all, while the target does. -/
theorem cendPE_constantLine_not_correct (e : NormalizedExpr)
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (constant : e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  exact cendPE_not_correct_of_inputIndependent [e]
    (cendPE_constantLine_inputIndependent e plain constant)

/-- The lines §4 closes: one plain row whose opcode is `.zero` or `.immediate`. -/
def CendConstantLines (expressions : List NormalizedExpr) : Prop :=
  ∃ e : NormalizedExpr, expressions = [e] ∧
    parsedExprIsPlainIntegerALU e.toParsed = true ∧
      (e.toParsed.op = .zero ∨
        ∃ value unsigned, e.toParsed.op = .immediate value unsigned)

/-- **Every constant line is refuted**, on the class name. -/
theorem cendPE_constantLines_not_correct (expressions : List NormalizedExpr)
    (constant : CendConstantLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  obtain ⟨e, same, plain, isConstant⟩ := constant
  subst same
  exact cendPE_constantLine_not_correct e plain isConstant

/-! ## 5. The residual after the technique, and what each family still needs

`CendUnconditional.CendPENonClosedRefuted` is the obligation left after the
`.matrixRead` and inert families; §4 of this module removes the constant family
from it.  What remains is stated below as **one uniform obligation**: for each
line, a proper set of input halves that determines the observed pair.  The
diagonalisation is already proved, and the bridge from a read set to the
executor's `FilesAgreeOn` hypothesis is provided in §1
(`cendInitialPERegisters_agree_of_halves`), so what is left is a congruence
statement about the executor and a syntactic read-set inclusion — no value
analysis, and no fixed witness. -/

/-- **The residual after this module.**  Every line outside the two classes
closed by `CendUnconditional` and outside the constant family closed here. -/
def CendPENonConstantRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, ¬ CendClosedLines expressions →
    ¬ CendConstantLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **`CendPENonClosedRefuted` from the smaller residual.** -/
theorem cendPENonClosedRefuted_of_nonConstant (rest : CendPENonConstantRefuted) :
    CendPENonClosedRefuted := by
  intro expressions closed correct
  by_cases constant : CendConstantLines expressions
  · exact cendPE_constantLines_not_correct expressions constant correct
  · exact rest expressions closed constant correct

/-- **Bound two from the smaller residual.** -/
theorem cendLowerBound_two_of_nonConstant (rest : CendPENonConstantRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_nonClosed (cendPENonClosedRefuted_of_nonConstant rest)

/-- **The uniform remaining obligation, in witness form.**  For every line
outside the closed classes, exhibit a proper set of input halves that determines
the observed pair.  This is the *only* thing between the current state and
`LowerBound cendSealedMachine cendSpec 2`: the diagonalisation
(`cendPE_not_correct_of_freeHalves`) consumes it directly. -/
def CendLineWitnessObligation : Prop :=
  ∀ expressions : List NormalizedExpr, ¬ CendClosedLines expressions →
    ¬ CendConstantLines expressions →
    ∃ halves : Finset InputHalf, (∃ half, half ∉ halves) ∧
      ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
        ∀ nextX nextY : State, cendStep expressions x = some nextX →
          cendStep expressions y = some nextY →
          cendOutputPair nextX = cendOutputPair nextY

/-- **The witness obligation closes the bound.** -/
theorem cendLowerBound_two_of_lineWitness (witness : CendLineWitnessObligation) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 := by
  refine cendLowerBound_two_of_nonConstant ?_
  intro expressions closed constant correct
  obtain ⟨halves, free, determined⟩ := witness expressions closed constant
  refine cendPE_not_correct_of_freeHalves expressions halves free ?_ correct
  intro x y agree nextX nextY stepX stepY
  exact determined x y agree nextX nextY stepX stepY

/-- **The residual in `CendUnconditional`'s `CendValueResidual` style**, so the
two reductions can be compared: every *unrefuted* non-closed, non-constant line
is refuted. -/
def CendWitnessValueResidual : Prop :=
  ∀ expressions : List NormalizedExpr, CendPEUnrefuted expressions →
    ¬ CendClosedLines expressions → ¬ CendConstantLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **Bound two from the witness-value residual.** -/
theorem cendLowerBound_two_of_witnessValueResidual (value : CendWitnessValueResidual) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_residual (fun expressions unrefuted closed => by
    intro correct
    by_cases constant : CendConstantLines expressions
    · exact cendPE_constantLines_not_correct expressions constant correct
    · exact value expressions unrefuted closed constant correct)

/-! ### The per-family obligations

Each `Prop` below is exactly the congruence statement the corresponding family
of `ProofsLean/CendUnconditional.lean` §"What is *not* closed" still needs, with
the diagonalisation already applied.  All of them are *input-independence of the
executor's prepared write list* modulo a read set, followed by
`commitParsedMaskedWrites_lm1_congr`. -/

/-- **Plain ALU rows, narrow (`word`) sources.**  A plain `.alu` row whose
sources cover at most one 32-bit half.

The executor half of this obligation is already written down, in two places:

* `ProofsLean/ChannelResiduals.lean` §3–§4 proves
  `prepareParsedIntegerALUExprCycle_congr` and
  `prepareParsedIntegerALUExprCycles_congr`: the four-cycle prepared list of one
  row is a function of the mask file and the cycle read sets
  `aluCycleReadSet` (nine lowering branches, full write-record congruence).  That
  module currently **does not build**: its final lemma passes `rfl` where the
  hypothesis `oldSlotsA = oldSlotsB` is needed
  (`ChannelResiduals.lean:1283`), so it must be repaired before use.
* `ProofsLean/WelcomePlainClose.welcomeIntegerPrep_single_plain_eq` is the bridge
  from `welcomeIntegerPrep state pe [e]` to that four-cycle preparation.

With those two, the only remaining work is *syntactic*: for a narrow row, the
union of `aluCycleReadSet` over the four cycles at the initial channels avoids
LM0 words `0`/`1`, or meets only the one half the row reads, which is exactly the
`covered` hypothesis of
`cendInitialPERegisters_agree_of_halves`.  Note the alignment subtlety: the
resolved address is width-aligned down, so a region based at `1` of width
longer than a word reads LM0 word `0` (`Region.lm0Coverage` already widens by
three words on both sides for this reason).

`commitParsedMaskedWrites_lm1_congr` then finishes, exactly as in §4. -/
def CendPlainALUNarrowWitness : Prop :=
  ∀ e : NormalizedExpr, parsedExprIsPlainIntegerALU e.toParsed = true →
    ¬ (e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned) →
    ∃ halves : Finset InputHalf, (∃ half, half ∉ halves) ∧
      (halves.card ≤ 1) ∧
      ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
        ∀ nextX nextY : State, cendStep [e] x = some nextX →
          cendStep [e] y = some nextY →
          cendOutputPair nextX = cendOutputPair nextY

/-- **Plain ALU rows, narrow sources: refuted.** -/
theorem cendPE_plainALUNarrow_not_correct (witness : CendPlainALUNarrowWitness)
    (e : NormalizedExpr) (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (notConstant : ¬ (e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨halves, free, _card, determined⟩ := witness e plain notConstant
  exact cendPE_not_correct_of_freeHalves [e] halves free determined

/-- **Plain ALU rows, wide (`.long`/`.double`) sources.**  Both halves are read,
so no free half exists and the finite-range form is the one to use: the ALU
opcode set is finite (`ParsedAluName` × `ParsedIntegerPrecision` × `unsigned`),
so the observed pair at a *fixed* probe input lies in the finite table of that
opcode set.  Needed: the table, one entry per opcode, of the 64-bit word the
opcode computes from the two probe half values, plus the proof that the line's
prepared data is that entry (`evaluateParsedIntegerAlu` on the read bus).  Then
`not_mem_of_range_subset` / `exists_ne_of_range_subset_of_surjective` finish,
provided the target pair at the probe input is outside the table. -/
def CendPlainALUWideWitness : Prop :=
  ∀ e : NormalizedExpr, parsedExprIsPlainIntegerALU e.toParsed = true →
    ¬ (e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned) →
    ∃ (probe : BitVec 64) (table : Finset (BitVec 64)),
      byteSwap64 probe ∉ table ∧
      ∀ next : State, cendStep [e] probe = some next → cendOutputPair next ∈ table

/-- **Plain ALU rows, wide sources: refuted.**  A single probe input whose
target is outside the opcode table refutes the row. -/
theorem cendPE_plainALUWide_not_correct (witness : CendPlainALUWideWitness)
    (e : NormalizedExpr) (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (notConstant : ¬ (e.toParsed.op = .zero ∨
      ∃ value unsigned, e.toParsed.op = .immediate value unsigned)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨probe, table, outside, range⟩ := witness e plain notConstant
  cases step : cendStep [e] probe with
  | none => exact cend_not_correct_of_step_none _ probe step
  | some next =>
      exact cend_not_correct_of_output_ne [e] probe next step (by
        intro same
        exact outside (same ▸ range next step))

/-- **`msl` / `msr` rows.**  The `msl`/`msr` ALU names read the PE mask register
file.  At every initial state that file is identically zero (a signature
channel), so the row's data is a *constant*: the constant-family argument of §4
applies verbatim once the prepared list is shown to depend only on the mask
channel.  Needed: `prepareParsedIntegerALUExprCycle` congruence under equal mask
registers *and* equal source reads — the `.alu` analogue of
`prepareParsedIntegerALUExprCycle_constant_eq` (which covers only `.zero` /
`.immediate`). -/
def CendMslMsrWitness : Prop :=
  ∀ e : NormalizedExpr,
    (∃ (name : ParsedAluName) (precision : Option ParsedPrecision) (unsigned : Bool)
        (arg : Option (Fin 256)), e.toParsed.op = .alu name precision unsigned arg) →
    (∃ (name : ParsedAluName) (precision : Option ParsedPrecision) (unsigned : Bool)
        (arg : Option (Fin 256)), e.toParsed.op = .alu name precision unsigned arg ∧
      (name = .msl ∨ name = .msr)) →
    ∃ halves : Finset InputHalf, (∃ half, half ∉ halves) ∧
      ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
        ∀ nextX nextY : State, cendStep [e] x = some nextX →
          cendStep [e] y = some nextY →
          cendOutputPair nextX = cendOutputPair nextY

/-- **`msl`/`msr` rows: refuted.** -/
theorem cendPE_mslMsr_not_correct (witness : CendMslMsrWitness)
    (e : NormalizedExpr) (isAlu : ∃ (name : ParsedAluName)
      (precision : Option ParsedPrecision) (unsigned : Bool) (arg : Option (Fin 256)),
      e.toParsed.op = .alu name precision unsigned arg)
    (isMsl : ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
      (unsigned : Bool) (arg : Option (Fin 256)),
      e.toParsed.op = .alu name precision unsigned arg ∧ (name = .msl ∨ name = .msr)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨halves, free, determined⟩ := witness e isAlu isMsl
  exact cendPE_not_correct_of_freeHalves [e] halves free determined

/-- **Float MAU rows.**  The MAU stages
(`executeParsedFloatMAUsAtPE`, `executeParsedBlockFloatProducer`) compute a
deterministic float function of their source buses and commit their own write
list.  Needed: the MAU/block-float analogue of
`cendSealed_pe_prepared` (the stage's own prepared list at PE 0, in the style of
`CendUnconditional.cendAllMatrixReadLines_prepared`) plus the congruence under
equal source reads.  The read set is the source halves; a MAU row reading one
32-bit operand leaves the other half free. -/
def CendFloatMAUWitness : Prop :=
  ∀ e : NormalizedExpr,
    (∃ (precision : ParsedPrecision) (matrix : Bool) (kind : CalcKind)
        (half : Option Char) (round : Bool),
        e.toParsed.op = .mau precision matrix kind half round) →
    ∃ halves : Finset InputHalf, (∃ half, half ∉ halves) ∧
      ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
        ∀ nextX nextY : State, cendStep [e] x = some nextX →
          cendStep [e] y = some nextY →
          cendOutputPair nextX = cendOutputPair nextY

/-- **Float MAU rows: refuted.** -/
theorem cendPE_floatMAU_not_correct (witness : CendFloatMAUWitness)
    (e : NormalizedExpr) (isMau : ∃ (precision : ParsedPrecision) (matrix : Bool)
      (kind : CalcKind) (half : Option Char) (round : Bool),
      e.toParsed.op = .mau precision matrix kind half round) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨halves, free, determined⟩ := witness e isMau
  exact cendPE_not_correct_of_freeHalves [e] halves free determined

/-- **Block-float rows.**  `executeParsedBlockFloatProducer` reads a block of
LM0 words through the block-float source operands and commits its own write
list.  Needed: the block-float analogue of `cendSealed_pe_prepared` (the stage's
prepared list at PE 0) plus congruence under agreement on the block's words.
At the initial state only LM0 words `0` and `1` are non-zero, so a block source
whose window avoids them is input-independent; a block containing LM0 word `0`
without word `1` leaves the low half free. -/
def CendBlockFloatWitness : Prop :=
  ∀ e : NormalizedExpr, parsedExprIsBlockFloatProducer e.toParsed = true →
    ∃ halves : Finset InputHalf, (∃ half, half ∉ halves) ∧
      ∀ x y, (∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) →
        ∀ nextX nextY : State, cendStep [e] x = some nextX →
          cendStep [e] y = some nextY →
          cendOutputPair nextX = cendOutputPair nextY

/-- **Block-float rows: refuted.** -/
theorem cendPE_blockFloat_not_correct (witness : CendBlockFloatWitness)
    (e : NormalizedExpr) (isBlock : parsedExprIsBlockFloatProducer e.toParsed = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨halves, free, determined⟩ := witness e isBlock
  exact cendPE_not_correct_of_freeHalves [e] halves free determined

/-- **L1BM broadcast rows.**  The broadcast reads the L1BM store, which is
identically zero at the initial state, so every prepared write carries zero data
and both observed words keep their initial `0` at `cendWitness` — the
`.matrixRead` argument of `CendUnconditional` §4, with
`commitParsedMaskedWrites_lm1_zero_of_data_zero` reused.
Needed: the line-level extraction through `executeParsedL1ToPEProducers`
(analogous to `cendAllMatrixReadLines_prepared`) and the data-zero lemma for the
broadcast path. -/
def CendL1BMBroadcastWitness : Prop :=
  ∀ e : NormalizedExpr,
    (∃ operation : ParsedL1Op, e.toParsed.op = .l1bm operation) →
    (∃ operation : ParsedL1Op, e.toParsed.op = .l1bm operation ∧
      (operation = .pbcast ∨ operation = .mbcast ∨ operation = .m4bcast)) →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [e]] : List InstructionLine)


end ProofsLean.MNCore
