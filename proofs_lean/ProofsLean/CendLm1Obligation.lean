import ProofsLean.CendLm1Witness

/-! # `12.convert-endian`: the executor half of the LM1 word obligation

`ProofsLean/CendLm1Witness.lean` reduced the plain both-halves family of
`12.convert-endian` to `CendLm1WordObligation`: at the witness input every
observed `LM1` word is `0`, a datapath word of `cendDatapathWords`, or an
input-independent row output.  What was missing there is the *executor
assembly*: the proof that the words a plain line actually writes are of that
shape.  This module is that assembly, as far as it goes.

## What is proved here

**Read side (§1–§3).**

* `toDirectMemoryAccess_aligned` — every access produced by the address
  resolver `ParsedOperand.toDirectMemoryAccess?` is aligned to its own
  `count bank width`: the resolver takes `raw / width.words * width.words`
  modulo the bank capacity (and the `.t` bank addresses `cycle * 4`, which is
  4-aligned).  This is the hypothesis of `cendMemoryBus_mem`.
* `cendMemoryBus_rounded_mem` — every memory read at the `12.convert-endian`
  initial state, rounded or not, is one of the ten buses of
  `cendInitialBuses`.
* `CendSourceOk` and its closure lemmas — every source an integer lowering can
  produce reads an initial bus: `.memory` through the alignment lemma, `.fixed`
  through `cendFixedBus_mem`, and `.forward` vacuously, because every forwarding
  slot is `poison` at the initial state, so the read *fails*.
  `cendSourceOk_toParsedIntegerInput`, `cendSourceOk_toUnroundedIntegerSourceAccess`
  and `cendSourceOk_toIntegerMaskSourceAccess` transport this through the three
  operand resolvers the nine branches use.

**Write side (§4).**  The data equation of every prepared-write helper the nine
branches call:

* `prepareParsedIntegerMaskALUWriteWithForwarding_data` (OMR / mask branch),
* `prepareParsedIntegerMaskInputALUWriteWithForwarding_data` (mask-input),
* `prepareParsedIntegerNoWriteALUWithForwarding_data` (no-write),
* `prepareParsedIntegerBarALUWithForwarding_data` (BAR),
* `prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_data`
  (memory-then-OMR; both writes carry the same bus),
* `prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_data`
  (OMR-then-memory; the OMR write carries the bus),
* `prepareParsedConstantTarget_data` (constant destinations: either a
  `.zero`/`.immediate` write with a flushed ALU bus, or a data bus that is
  identically zero).

In every case the write's data bus is exactly

`unpackALUBus (parsedOutputAfterFlush flush (evaluateBus precision op x y reduced))`

where `x` and `y` are the two operand reads and nothing else.  Together with
§1–§3 this says: **at the initial state every write of a plain integer row is
the ALU image of two initial buses (or a constant/zero bus), with the mask
selection and the destination the only branch-dependent data.**

## What remains, exactly

1. **The nine-branch cycle assembly.**  `prepareParsedIntegerALUExprCycle` is a
   nine-way `match`; §4 gives the value equation of each endpoint, but the
   `cases`/`split` analysis that connects the branch taken to its endpoint (the
   same skeleton as `CendWideWitness.prepareParsedIntegerALUExprCycle_noLm1`,
   which does it for the *destination* only) is not carried out here.  Its
   statement is: for every successful cycle and every `write` in its list,
   `write.data = unpackALUBus (parsedOutputAfterFlush … (evaluateBus …))` with
   the two operand reads drawn from `cendInitialBuses`.
2. **The four-cycle fold and the line fold**
   (`prepareParsedIntegerALUExprCycles_four_general`,
   `prepareParsedIntegerMatrixReadLineCycles`): lifting (1) from one cycle to
   the write list of a whole `.pe` line, together with
   `commitParsedMaskedWrites_append`.
3. **The commit step.**  `commitParsedMaskedWrites` folds the writes into the
   pre-line files; for `LM1` word `0`/`1` the observed word is the data word of
   the last *enabled covering* write (all covering writes are at address `0`,
   hence data word `0`/`1`, by the alignment above), or the initial `0`.
4. **The mask caveat.**  The task's premise "at the initial state the mask
   register file is `0`, so the flags are `0` or `15`" holds for every write
   whose selection is resolved from `files.maskRegisters`, but not for the
   OMR-then-memory branch: `prepareParsedIntegerMaskInputThenMemoryALU-Writes-
   WithForwarding` resolves its memory write's selection from
   `Masks.writeRegister files.maskRegisters entry cycle flags selection`, so
   with a memory-operand mask selector pointing at the just-written entry the
   flags become the row's *ALU flag bits* (`0b1100` and friends for `.word`
   precision), and `selectedWordMask` then selects `0xffff0000` or `0x0000ffff`
   of the data word rather than the whole word.  Such a partially masked word
   is not an element of `cendDatapathWords`, so the literal
   `CendLm1WordObligation` disjunction is too narrow for lines that take that
   branch; the refutation still works because the target words
   (`0xefcdab89`, `0x67452301`) have both 16-bit halves non-zero, so a word with
   a zero half can never be the target.  A fully unconditional
   `cendPlainALUBothHalvesRefuted` must therefore either (a) exclude the
   OMR-then-memory feedback shape by a syntactic side condition, or (b) enlarge
   the obligation's value set to `{d, d &&& 0xffff0000, d &&& 0x0000ffff : d ∈
   cendDatapathWords}` and reprove the final target comparison.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.  Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option autoImplicit false

/-! ## 1. Alignment of the resolved accesses -/

/-- **Every access produced by the address resolver is aligned.**  The resolver
rounds the raw address down to a multiple of the access width, except at the
`.t` bank, which always addresses `cycle * 4` words (and `.t` always occupies
four words).  Hence `address % count bank width = 0`, the hypothesis of
`cendMemoryBus_mem`. -/
theorem toDirectMemoryAccess_aligned (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (access : DirectMemoryAccess)
    (resolved : ParsedOperand.toDirectMemoryAccess? operand pe cycle bar0 bar1 tWord = some access) :
    access.address.val % PEMemory.count access.bank access.width = 0 := by
  cases operand with
  | mem memoryAccess negated extended rounded mask =>
      simp only [ParsedOperand.toDirectMemoryAccess?] at resolved
      simp only [ParsedOperand.toDirectMemoryAccessMode?] at resolved
      split at resolved
      · simp at resolved
      · cases hb : issueBankToRegisterBank memoryAccess.bank with
        | none => simp [hb] at resolved
        | some bank =>
            cases hw : parsedWidth? memoryAccess.region.width with
            | none => simp [hb, hw] at resolved
            | some width =>
                simp only [hb, hw] at resolved
                split at resolved
                · simp at resolved
                · simp only [Option.some.injEq] at resolved
                  subst resolved
                  show (if (bank == PEMemory.Bank.t) = true then cycle.val * 4 else
                    ((((if (bank == PEMemory.Bank.lm0) = true then bar0.toNat
                         else if (bank == PEMemory.Bank.lm1) = true then bar1.toNat else 0) +
                        (if memoryAccess.region.tIndirect = true then tWord.toNat else 0)) +
                      parsedRegionAddressAt memoryAccess.region cycle +
                      (match memoryAccess.region.madpe with
                       | some threshold => if (pe.val ≤ threshold) then width.words else 0
                       | none => 0)) / width.words * width.words % bank.capacity)) %
                    PEMemory.count bank width = 0
                  by_cases isT : bank = PEMemory.Bank.t
                  · subst isT
                    rw [if_pos (by decide : ((PEMemory.Bank.t == PEMemory.Bank.t) = true))]
                    cases width <;> simp [PEMemory.count] <;> omega
                  · rw [if_neg (by simp [isT])]
                    have hcount : PEMemory.count bank width = width.words := by
                      simp [PEMemory.count, isT]
                    rw [hcount]
                    have dvd : width.words ∣ bank.capacity := by
                      cases width <;> cases bank <;> decide
                    rw [Nat.mod_mod_of_dvd _ dvd]
                    exact Nat.mod_eq_zero_of_dvd ⟨_, by rw [Nat.mul_comm]⟩
  | bar _ _ mask => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | forward _ _ _ _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | fixed kind => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | omr _ _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | matrix _ _ _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | nowrite => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | l1bm _ _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | l2bm _ _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | dar _ => simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?] at resolved

/-! ## 2. Rounded reads at the initial state -/

theorem cendRoundSingleInputBusToHalf_zero :
    roundSingleInputBusToHalf (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by decide

theorem cendApplyRounding_zero (rounded : Bool) :
    ParsedIntegerInput.applyRounding rounded (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by
  cases rounded with
  | false => rfl
  | true => exact cendRoundSingleInputBusToHalf_zero

theorem cendInitialZeroBus_read (x : BitVec 64) (bank : PEMemory.Bank) (width : PEMemory.Width)
    (start : Fin bank.capacity) (notLm0 : bank ≠ PEMemory.Bank.lm0) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) bank width start) =
      (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases bank with
  | lm0 => exact absurd rfl notLm0
  | lm1 => simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
      zeroInitialPERegisterFiles, PEMemory.pack, BitVec.zero_append_zero]
  | grf0 => simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
      zeroInitialPERegisterFiles, PEMemory.pack, BitVec.zero_append_zero]
  | grf1 => simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
      zeroInitialPERegisterFiles, PEMemory.pack, BitVec.zero_append_zero]
  | t => simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
      zeroInitialPERegisterFiles, PEMemory.pack, BitVec.zero_append_zero]

/-- **Rounded memory reads stay in the initial bus family.** -/
theorem cendMemoryBus_rounded_mem (x : BitVec 64) (bank : PEMemory.Bank)
    (width : PEMemory.Width) (start : Fin bank.capacity) (rounded : Bool)
    (aligned : start.val % PEMemory.count bank width = 0) :
    ParsedIntegerInput.applyRounding rounded
      (PEMemory.pack (readRegisterBank (cendInitialPERegisters x) bank width start)) ∈
        cendInitialBuses x := by
  cases rounded with
  | false => exact cendMemoryBus_mem x bank width start aligned
  | true =>
      cases bank with
      | lm1 =>
          rw [cendInitialZeroBus_read x .lm1 width start (by decide), cendApplyRounding_zero]
          simp [cendInitialBuses, cendZeroBus]
      | grf0 =>
          rw [cendInitialZeroBus_read x .grf0 width start (by decide), cendApplyRounding_zero]
          simp [cendInitialBuses, cendZeroBus]
      | grf1 =>
          rw [cendInitialZeroBus_read x .grf1 width start (by decide), cendApplyRounding_zero]
          simp [cendInitialBuses, cendZeroBus]
      | t =>
          rw [cendInitialZeroBus_read x .t width start (by decide), cendApplyRounding_zero]
          simp [cendInitialBuses, cendZeroBus]
      | lm0 =>
          cases width with
          | word =>
              have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x)
                  PEMemory.Bank.lm0 PEMemory.Width.word start) =
                  (⟨(cendInitialPERegisters x).lm0 start ++ (0 : BitVec 32), 0⟩ :
                    IntegerALU.Bus) := by
                simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
                  PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
              rw [shape]
              by_cases h0 : start.val = 0
              · have h : (cendInitialPERegisters x).lm0 start = x.extractLsb' 32 32 := by
                  rw [cendInitialLm0Word, if_pos h0]
                rw [h]
                simp [cendInitialBuses, ParsedIntegerInput.applyRounding]
              · by_cases h1 : start.val = 1
                · have h : (cendInitialPERegisters x).lm0 start = x.extractLsb' 0 32 := by
                    rw [cendInitialLm0Word, if_neg h0, if_pos h1]
                  rw [h]
                  simp [cendInitialBuses, ParsedIntegerInput.applyRounding]
                · have h : (cendInitialPERegisters x).lm0 start = 0 := by
                    rw [cendInitialLm0Word, if_neg h0, if_neg h1]
                  rw [h]
                  rw [show (⟨(0 : BitVec 32) ++ (0 : BitVec 32), 0⟩ : IntegerALU.Bus) =
                    (⟨0, 0⟩ : IntegerALU.Bus) from by decide]
                  rw [cendApplyRounding_zero]
                  simp [cendInitialBuses, cendZeroBus]
          | long =>
              have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x)
                  PEMemory.Bank.lm0 PEMemory.Width.long start) =
                  (⟨(cendInitialPERegisters x).lm0 start ++
                    (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 1), 0⟩ :
                    IntegerALU.Bus) := by
                simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
                  PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
              rw [shape]
              by_cases h0 : start.val = 0
              · have hstart : start = (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) :=
                  Fin.ext h0
                subst hstart
                have hone : PEMemory.advance PEMemory.Bank.lm0
                    (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 1 =
                    (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
                rw [hone]
                rw [show (⟨(cendInitialPERegisters x).lm0
                      (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) ++
                    (cendInitialPERegisters x).lm0
                      (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity), 0⟩ : IntegerALU.Bus) =
                  (⟨x, 0⟩ : IntegerALU.Bus) from by
                    simp [cendInitialLm0Word,
                      BitVec.extractLsb'_append_extractLsb' (w := 32) (len := 32)]]
                simp [cendInitialBuses, ParsedIntegerInput.applyRounding]
              · have hstart0 : (cendInitialPERegisters x).lm0 start = 0 := by
                  rw [cendInitialLm0Word, if_neg h0]
                  have hne : ¬ start.val = 1 := by
                    intro hone
                    rw [hone] at aligned
                    exact absurd aligned (by decide)
                  rw [if_neg hne]
                have hadv : (PEMemory.advance PEMemory.Bank.lm0 start 1).val = start.val + 1 := by
                  rw [cendAdvanceLm0Val]
                  show (start.val + 1) % PEMemory.Bank.lm0.capacity = start.val + 1
                  have hv : start.val < 4096 := start.isLt
                  have hp : start.val % 2 = 0 := by
                    simpa [PEMemory.count, PEMemory.Width.words] using aligned
                  have hc : PEMemory.Bank.lm0.capacity = 4096 := rfl
                  exact Nat.mod_eq_of_lt (by omega)
                have hnext : (cendInitialPERegisters x).lm0
                    (PEMemory.advance PEMemory.Bank.lm0 start 1) = 0 := by
                  rw [cendInitialLm0Word, hadv]
                  have hne0 : ¬ start.val + 1 = 0 := by omega
                  have hne1 : ¬ start.val + 1 = 1 := by omega
                  rw [if_neg hne0, if_neg hne1]
                simp only [hstart0, hnext]
                rw [show (⟨(0 : BitVec 32) ++ (0 : BitVec 32), 0⟩ : IntegerALU.Bus) =
                  (⟨0, 0⟩ : IntegerALU.Bus) from by decide]
                rw [cendApplyRounding_zero]
                simp [cendInitialBuses, cendZeroBus]
          | double =>
              have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x)
                  PEMemory.Bank.lm0 PEMemory.Width.double start) =
                  (⟨(cendInitialPERegisters x).lm0 start ++
                      (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 1),
                    (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 2) ++
                      (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 3)⟩ :
                    IntegerALU.Bus) := by
                simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
                  PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
              rw [shape]
              by_cases h0 : start.val = 0
              · have hstart : start = (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) :=
                  Fin.ext h0
                subst hstart
                have hone : PEMemory.advance PEMemory.Bank.lm0
                    (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 1 =
                    (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
                have htwo : PEMemory.advance PEMemory.Bank.lm0
                    (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 2 =
                    (⟨2, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
                have hthree : PEMemory.advance PEMemory.Bank.lm0
                    (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 3 =
                    (⟨3, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
                rw [hone, htwo, hthree]
                rw [show (⟨(cendInitialPERegisters x).lm0
                      (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) ++
                    (cendInitialPERegisters x).lm0
                      (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity),
                    (cendInitialPERegisters x).lm0
                      (⟨2, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) ++
                      (cendInitialPERegisters x).lm0
                        (⟨3, by decide⟩ : Fin PEMemory.Bank.lm0.capacity)⟩ : IntegerALU.Bus) =
                  (⟨x, 0⟩ : IntegerALU.Bus) from by
                    simp [cendInitialLm0Word,
                      BitVec.extractLsb'_append_extractLsb' (w := 32) (len := 32),
                      BitVec.zero_append_zero]]
                simp [cendInitialBuses, ParsedIntegerInput.applyRounding]
              · have hge : 4 ≤ start.val := by
                  have hv : start.val < 4096 := start.isLt
                  have hp : start.val % 4 = 0 := by
                    simpa [PEMemory.count, PEMemory.Width.words] using aligned
                  omega
                have hword : ∀ offset : Nat, offset < 4 →
                    (PEMemory.advance PEMemory.Bank.lm0 start offset).val =
                      start.val + offset := by
                  intro offset hoff
                  rw [cendAdvanceLm0Val]
                  show (start.val + offset) % PEMemory.Bank.lm0.capacity = start.val + offset
                  have hv : start.val < 4096 := start.isLt
                  have hp : start.val % 4 = 0 := by
                    simpa [PEMemory.count, PEMemory.Width.words] using aligned
                  have hc : PEMemory.Bank.lm0.capacity = 4096 := rfl
                  exact Nat.mod_eq_of_lt (by omega)
                have hzero : ∀ offset : Nat, offset < 4 →
                    (cendInitialPERegisters x).lm0
                      (PEMemory.advance PEMemory.Bank.lm0 start offset) = 0 := by
                  intro offset hoff
                  rw [cendInitialLm0Word, hword offset hoff]
                  have hne0 : ¬ start.val + offset = 0 := by omega
                  have hne1 : ¬ start.val + offset = 1 := by omega
                  rw [if_neg hne0, if_neg hne1]
                have hzeroStart : (cendInitialPERegisters x).lm0 start = 0 := by
                  rw [cendInitialLm0Word, if_neg h0]
                  have hne1 : ¬ start.val = 1 := by omega
                  rw [if_neg hne1]
                simp only [hzeroStart, hzero 1 (by decide), hzero 2 (by decide), hzero 3 (by decide)]
                rw [show (⟨(0 : BitVec 32) ++ (0 : BitVec 32),
                    (0 : BitVec 32) ++ (0 : BitVec 32)⟩ : IntegerALU.Bus) =
                  (⟨0, 0⟩ : IntegerALU.Bus) from by decide]
                rw [cendApplyRounding_zero]
                simp [cendInitialBuses, cendZeroBus]

/-! ## 3. Source provenance of the integer lowerings -/

/-- The forwarding-slot state of the `12.convert-endian` initial machine: every
slot is `poison`. -/
def cendPoisonSlots : ProofsLean.MNCore.Forwarding.Slots := fun _ _ => .poison

/-- **A source input reads an initial bus.**  Every `.memory` read at the initial
state (rounded or not) is one of `cendInitialBuses`, every `.fixed` value built
from a `ParsedFixed` identifier is one of them, and a `.forward` read fails. -/
def CendSourceOk (x : BitVec 64) (cycle : Fin 4) (input : ParsedIntegerInput) : Prop :=
  ∀ bus, ParsedIntegerInput.readWithForwarding (cendInitialPERegisters x) cendPoisonSlots
    cycle input = .ok bus → bus ∈ cendInitialBuses x

theorem cendSourceOk_memory (x : BitVec 64) (cycle : Fin 4) (access : DirectMemoryAccess)
    (rounded : Bool) (aligned : access.address.val % PEMemory.count access.bank access.width = 0) :
    CendSourceOk x cycle (.memory access rounded) := by
  intro bus read
  simp only [CendSourceOk, ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    StepResult.ok.injEq] at read
  subst read
  exact cendMemoryBus_rounded_mem x access.bank access.width access.address rounded aligned

theorem cendSourceOk_fixed (x : BitVec 64) (cycle : Fin 4) (fixed : ParsedFixed)
    (precision : IntegerALU.Precision) :
    CendSourceOk x cycle (.fixed (replicateIntegerLane precision
      (ParsedFixed.integerValue fixed precision
        (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b
        (ParsedIntegerContext.ofLinearIndex cendPE).mab
        (ParsedIntegerContext.ofLinearIndex cendPE).pe))) := by
  intro bus read
  simp only [CendSourceOk, ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    StepResult.ok.injEq] at read
  subst read
  exact cendFixedBus_mem x fixed precision

theorem cendSourceOk_forward (x : BitVec 64) (cycle : Fin 4) (kind : ParsedForward)
    (rounded : Bool) : CendSourceOk x cycle (.forward kind rounded) := by
  intro bus read
  simp [CendSourceOk, ParsedIntegerInput.readWithForwarding, cendPoisonSlots] at read


/-! ## 4. The data equation of every prepared-write helper

`unpackALUBus` of the flushed `evaluateParsedIntegerAlu` result of the two
operand reads: this section proves it for each of the helpers the nine branches
of `prepareParsedIntegerALUExprCycle` call.  The helpers differ in their write
list shape, destination and selection only; the value is always this bus. -/

theorem prepareParsedIntegerMaskALUWriteWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskALUWriteWithForwarding files slots cycle accesses
      flushSelection reduced = .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle
          (.memory accesses.sourceX accesses.sourceXRounded) = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle
          (.memory accesses.sourceY accesses.sourceYRounded) = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) := by
  unfold prepareParsedIntegerMaskALUWriteWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle
      (.memory accesses.sourceX accesses.sourceXRounded) with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle
          (.memory accesses.sourceY accesses.sourceYRounded) with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl⟩

theorem prepareParsedIntegerMaskInputALUWriteWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskInputALUWriteWithForwarding files slots cycle accesses
      flushSelection reduced = .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) := by
  unfold prepareParsedIntegerMaskInputALUWriteWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl⟩

theorem prepareParsedIntegerNoWriteALUWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerNoWriteAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerNoWriteALUWithForwarding files slots cycle accesses reduced =
      .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value) := by
  unfold prepareParsedIntegerNoWriteALUWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl⟩

theorem prepareParsedIntegerBarALUWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerBarAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerBarALUWithForwarding files slots cycle accesses reduced =
      .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value) := by
  unfold prepareParsedIntegerBarALUWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl⟩

theorem prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files slots cycle
      accesses flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      memoryWrites.map (fun write => write.data) = [unpackALUBus (parsedOutputAfterFlush
        flushSelection output.value)] ∧
      omrWrite.data = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) ∧
      omrWrite.maskUpdate.isSome = true := by
  unfold prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨hList, hOmr⟩ := prepared
              subst hList
              subst hOmr
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl, rfl, rfl⟩

theorem prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_data
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files slots cycle
      accesses directive hasSingleLineMask flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      omrWrite.data = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) ∧
      omrWrite.maskUpdate.isSome = true := by
  unfold prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated] at prepared
              split at prepared
              · simp at prepared
              · simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
                obtain ⟨-, hOmr⟩ := prepared
                subst hOmr
                exact ⟨x, y, output, rfl, rfl, evaluated, rfl, rfl⟩

theorem prepareParsedConstantTarget_data
    (files : IntegerRegisterFiles) (cycle : Fin 4) (target : ParsedConstantDestination)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedConstantTarget files cycle target = .ok write) :
    (∃ (accesses : ParsedMaskedIntegerAccesses) (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      target = .memory accesses ∧
      ParsedIntegerInput.read files accesses.sourceX = .ok x ∧
      ParsedIntegerInput.read files accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y false = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value)) ∨
    (write.data = fun _ => 0) := by
  cases target with
  | memory accesses =>
      left
      have prepared' : prepareParsedMaskedWrite files accesses false = .ok write := by
        simpa [prepareParsedConstantTarget] using prepared
      obtain ⟨x, y, output, readX, readY, evaluated, data⟩ :=
        prepareParsedMaskedWrite_data files accesses false write prepared'
      exact ⟨accesses, x, y, output, rfl, readX, readY, evaluated, data⟩
  | maskRegister entry => right; simp [prepareParsedConstantTarget] at prepared; subst prepared; rfl
  | noWrite => right; simp [prepareParsedConstantTarget] at prepared; subst prepared; rfl


/-! ## 3b. The resolvers produce initial sources -/

/-- A resolved direct access at the `12.convert-endian` initial context is
aligned, hence its read (rounded or not) is an initial bus. -/
theorem cendSourceOk_resolvedAccess (x : BitVec 64) (cycle : Fin 4)
    (access : DirectMemoryAccess) (rounded : Bool) (aligned : access.address.val %
      PEMemory.count access.bank access.width = 0) :
    CendSourceOk x cycle (.memory access rounded) :=
  cendSourceOk_memory x cycle access rounded aligned

/-- **Every `.memory`/`.fixed`/`.forward` input produced by the integer source
resolver is an initial source** (and the `.forward` case is vacuous because the
slot is `poison`). -/
theorem cendSourceOk_toParsedIntegerInput (x : BitVec 64) (operand : ParsedOperand)
    (precision : IntegerALU.Precision) (cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (input : ParsedIntegerInput)
    (resolved : ParsedOperand.toParsedIntegerInput? operand precision
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle bar0 bar1 tWord = some input) :
    CendSourceOk x cycle input := by
  cases operand with
  | fixed fixed =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at resolved
      subst resolved
      exact cendSourceOk_fixed x cycle fixed precision
  | forward kind negated extended rounded =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at resolved
      subst resolved
      exact cendSourceOk_forward x cycle kind rounded
  | mem access negated extended rounded mask =>
      simp only [ParsedOperand.toParsedIntegerInput?] at resolved
      cases hr : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
          (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle bar0 bar1 tWord with
      | none => simp [hr] at resolved
      | some resolvedAccess =>
          simp only [hr, Option.map_some, Option.some.injEq] at resolved
          subst resolved
          exact cendSourceOk_memory x cycle resolvedAccess rounded
            (toDirectMemoryAccess_aligned (.mem access false false false none)
              (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle
              bar0 bar1 tWord resolvedAccess hr)
  | nowrite => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | omr entry mask => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | bar lm1 width mask => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | matrix group width row => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l1bm width address => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l2bm address l2b => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | dar address => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim

/-- The unrounded direct-access resolver produces an initial source. -/
theorem cendSourceOk_toUnroundedIntegerSourceAccess (x : BitVec 64) (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (access : DirectMemoryAccess)
    (resolved : ParsedOperand.toUnroundedIntegerSourceAccess? operand pe cycle bar0 bar1 tWord =
      some access) :
    CendSourceOk x cycle (.memory access false) := by
  cases operand with
  | mem source negated extended rounded mask =>
      simp only [ParsedOperand.toUnroundedIntegerSourceAccess?] at resolved
      cases rounded with
      | true => simp at resolved
      | false =>
          exact cendSourceOk_memory x cycle access false
            (toDirectMemoryAccess_aligned (.mem source false false false none) pe cycle
              bar0 bar1 tWord access resolved)
  | nowrite => try simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | omr entry mask => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | bar lm1 width mask => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | forward kind negated extended rounded =>
      simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | fixed kind => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | matrix group width row => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l1bm width address => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l2bm address l2b => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | dar address => simp [ParsedOperand.toUnroundedIntegerSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim

/-- The mask-source resolver produces an initial source. -/
theorem cendSourceOk_toIntegerMaskSourceAccess (x : BitVec 64) (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (access : DirectMemoryAccess) (rounded : Bool)
    (resolved : ParsedOperand.toIntegerMaskSourceAccess? operand pe cycle bar0 bar1 tWord =
      some (access, rounded)) :
    CendSourceOk x cycle (.memory access rounded) := by
  cases operand with
  | mem source negated extended rounded' mask =>
      simp only [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
      cases hr : ParsedOperand.toDirectMemoryAccess? (.mem source false false false none)
          pe cycle bar0 bar1 tWord with
      | none => simp [hr] at resolved
      | some resolvedAccess =>
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at resolved
          obtain ⟨rfl, rfl⟩ := resolved
          exact cendSourceOk_memory x cycle resolvedAccess rounded'
            (toDirectMemoryAccess_aligned (.mem source false false false none) pe cycle
              bar0 bar1 tWord resolvedAccess hr)
  | nowrite => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | omr entry mask => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | bar lm1 width mask => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | forward kind negated extended rounded' =>
      simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | fixed kind => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | matrix group width row => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l1bm width address => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | l2bm address l2b => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim
  | dar address => simp [ParsedOperand.toIntegerMaskSourceAccess?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved; try exact resolved.elim


/-! ## 5. The mask caveat, kernel checked

The two mask facts quoted in the header.  `0b1000` and `0b0100` are the flag
patterns at which a non-`ll` selection covers only the high or only the low
16-bit half of a word.  Such a value is a partial image of a datapath word, not
a datapath word itself. -/

theorem cendSelectedWordMask_highHalf :
    PEMemory.selectedWordMask (0b1000 : BitVec 4) false ⟨0, by decide⟩ = 0xffff0000 := by
  decide

theorem cendSelectedWordMask_lowHalf :
    PEMemory.selectedWordMask (0b0100 : BitVec 4) false ⟨0, by decide⟩ = 0x0000ffff := by
  decide

theorem cendMergeSelectedWord_highHalf (data : BitVec 32) :
    PEMemory.mergeSelectedWord 0 data (0xffff0000 : BitVec 32) = data &&& 0xffff0000 := by
  simp [PEMemory.mergeSelectedWord]

theorem cendMergeSelectedWord_lowHalf (data : BitVec 32) :
    PEMemory.mergeSelectedWord 0 data (0x0000ffff : BitVec 32) = data &&& 0x0000ffff := by
  simp [PEMemory.mergeSelectedWord]

/-! ## 5. Trust report -/

#print axioms toDirectMemoryAccess_aligned
#print axioms cendMemoryBus_rounded_mem
#print axioms cendSourceOk_toParsedIntegerInput
#print axioms cendSourceOk_toUnroundedIntegerSourceAccess
#print axioms cendSourceOk_toIntegerMaskSourceAccess
#print axioms prepareParsedIntegerMaskALUWriteWithForwarding_data
#print axioms prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_data
#print axioms prepareParsedConstantTarget_data
#print axioms cendSelectedWordMask_highHalf
#print axioms cendMergeSelectedWord_highHalf

end ProofsLean.MNCore
