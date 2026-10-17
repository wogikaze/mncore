import ProofsLean.ByteSwap
import ProofsLean.SingleFMA
import ProofsLean.FloatPEMemory
import ProofsLean.PEParser

/-! Bit-level datapath reconstruction of the public Convert Endian answer.

The integer barrel shift first exchanges the two 16-bit halves within each
32-bit lane. The single
precision MAU FMA transforms the immediate bit pattern into the halfword shift
count used by the next issue word. That barrel shift rotates each 16-bit lane
by one byte, and the destination selector exchanges the 32-bit lanes again. -/
namespace ProofsLean.MNCore.ConvertEndian

open ProofsLean.MNCore.Issue

/-! The public answer's operands are first parsed by the repository's VSM
operand parser. These facts pin down the exact per-cycle addresses and
forwarding selectors consumed by the execution models below. -/

theorem answer_operands_parse :
    parseParsedPEOperand? "$r0v" =
        some (.mem ⟨.grf0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none) ∧
    parseParsedPEOperand? "$m0v" =
        some (.mem ⟨.lm0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none) ∧
    parseParsedPEOperand? "$aluf" = some (.forward .aluf false false false) ∧
    parseParsedPEOperand? "$s0v" =
        some (.mem ⟨.grf1, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none) ∧
    parseParsedPEOperand? "$mauf" = some (.forward .mauf false false false) ∧
    parseParsedPEOperand? "$n[1,0,3,2]" =
        some (.mem ⟨.lm1, ⟨1, 1, 0, 3, 2, false, none⟩⟩ false false false none) := by
  decide

theorem answer_operands_parse_all :
    (parseParsedPEOperand? "$r0v").isSome ∧
    (parseParsedPEOperand? "$m0v").isSome ∧
    (parseParsedPEOperand? "$aluf").isSome ∧
    (parseParsedPEOperand? "$s0v").isSome ∧
    (parseParsedPEOperand? "$mauf").isSome ∧
    (parseParsedPEOperand? "$n[1,0,3,2]").isSome := by
  rcases answer_operands_parse with ⟨h0, h1, h2, h3, h4, h5⟩
  simp [h0, h1, h2, h3, h4, h5]

/-- Opcode slice for the public Convert Endian answer. The immediate payload
is kept as a separate token, matching the source grammar. This deliberately
recognizes only the operations used by these three lines. -/
def parseAnswerOperation? (opcode literal : String) : Option ParsedOp :=
  match opcode, literal with
  | "imm", "i\"0x34f80010\"" => some (.immediate 0x34f80010 false)
  | "ibsl", "" => some (.alu .bsl (some .i) false none)
  | "fvfma", "" => some (.mau .f false .fma none false)
  | "sbsl", "" => some (.alu .bsl (some .s) false none)
  | _, _ => none

theorem answer_operations_parse :
    parseAnswerOperation? "imm" "i\"0x34f80010\"" =
        some (.immediate 0x34f80010 false) ∧
    parseAnswerOperation? "ibsl" "" = some (.alu .bsl (some .i) false none) ∧
    parseAnswerOperation? "fvfma" "" = some (.mau .f false .fma none false) ∧
    parseAnswerOperation? "sbsl" "" = some (.alu .bsl (some .s) false none) := by
  decide

theorem answer_operations_source_arities :
    (parseAnswerOperation? "imm" "i\"0x34f80010\"").map ParsedOp.parserSourceLimit =
        some 0 ∧
    (parseAnswerOperation? "ibsl" "").map ParsedOp.parserSourceLimit = some 2 ∧
    (parseAnswerOperation? "fvfma" "").map ParsedOp.parserSourceLimit = some 3 ∧
    (parseAnswerOperation? "sbsl" "").map ParsedOp.parserSourceLimit = some 2 := by
  decide

/-- Restricted expression parser used to turn the answer's opcode and operand
tokens into the same `ParsedExpr` record consumed by the execution lowering.
Source arity is checked before operands are classified. -/
def parseAnswerExpr? (opcode literal : String) (sources destinations : List String)
    (text : String) : Option ParsedExpr := do
  let operation ← parseAnswerOperation? opcode literal
  if sources.length != operation.parserSourceLimit then none else
    let parsedSources ← sources.mapM parseParsedPEOperand?
    let parsedDestinations ← destinations.mapM parseParsedPEOperand?
    some ⟨operation, parsedSources, parsedDestinations, none, text⟩

def answerImmediateExpr? : Option ParsedExpr :=
  parseAnswerExpr? "imm" "i\"0x34f80010\"" [] ["$r0v"]
    "imm i\"0x34f80010\" $r0v"

def answerIntegerShiftExpr? : Option ParsedExpr :=
  parseAnswerExpr? "ibsl" "" ["$m0v", "$aluf"] ["$r8v"]
    "ibsl $m0v $aluf $r8v"

def answerFloatFmaExpr? : Option ParsedExpr :=
  parseAnswerExpr? "fvfma" "" ["$aluf", "$aluf", "$aluf"] ["$s0v"]
    "fvfma $aluf $aluf $aluf $s0v"

def answerByteShiftExpr? : Option ParsedExpr :=
  parseAnswerExpr? "sbsl" "" ["$aluf", "$mauf"] ["$n[1,0,3,2]"]
    "sbsl $aluf $mauf $n[1,0,3,2]"

theorem answer_expressions_parse :
    answerImmediateExpr?.isSome ∧ answerIntegerShiftExpr?.isSome ∧
      answerFloatFmaExpr?.isSome ∧ answerByteShiftExpr?.isSome := by
  decide

/-- The parallel middle issue contains two independently parsed expressions;
this preserves the instruction boundary needed by issue checking. -/
def answerParallelExpressions? : Option (List ParsedExpr) := do
  let integer ← answerIntegerShiftExpr?
  let fma ← answerFloatFmaExpr?
  some [integer, fma]

theorem answer_parallel_expression_count :
    answerParallelExpressions?.map List.length = some 2 := by
  decide

def swap32 (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 0 32) ++ (word.extractLsb' 32 32)

def swapHalfwordsWithin32 (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 32 16) ++ (word.extractLsb' 48 16) ++
    (word.extractLsb' 0 16) ++ (word.extractLsb' 16 16)

def ibsl (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 32 32).rotateLeft 16 ++
    (word.extractLsb' 0 32).rotateLeft 16

def sbsl (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 48 16).rotateLeft 8 ++
    (word.extractLsb' 32 16).rotateLeft 8 ++
    (word.extractLsb' 16 16).rotateLeft 8 ++
    (word.extractLsb' 0 16).rotateLeft 8

/-- The FMA is issued with three copies of the same immediate lane. -/
def immediateWord : BitVec 32 := 0x34F80010
def mauShiftWord : BitVec 32 := 0x34F80018

theorem immediate_fma_generates_shift_word :
    SingleFMA.singleFma immediateWord immediateWord immediateWord = mauShiftWord := by
  decide

theorem ibsl_is_32bit_lane_rotate (word : BitVec 64) :
    ibsl word = swapHalfwordsWithin32 word := by
  unfold ibsl swapHalfwordsWithin32
  bv_decide

/-- The `[1,0,3,2]` destination selector exchanges the two 32-bit groups. -/
def selector2103 (word : BitVec 64) : BitVec 64 := swap32 word

def answerDatapath (input : BitVec 64) : BitVec 64 :=
  selector2103 (sbsl (ibsl input))

theorem answerDatapath_is_byteSwap (input : BitVec 64) :
    answerDatapath input = byteSwap64 input := by
  unfold answerDatapath selector2103 sbsl ibsl swap32 byteSwap64
  bv_decide

theorem answerDatapath_involutive (input : BitVec 64) :
    answerDatapath (answerDatapath input) = input := by
  rw [answerDatapath_is_byteSwap, answerDatapath_is_byteSwap]
  exact byteSwap64_involutive input

def packedSingleFma (a b c : BitVec 64) : BitVec 64 :=
  (SingleFMA.singleFma (a.extractLsb' 32 32) (b.extractLsb' 32 32)
    (c.extractLsb' 32 32)) ++
  (SingleFMA.singleFma (a.extractLsb' 0 32) (b.extractLsb' 0 32)
    (c.extractLsb' 0 32))

def mauShiftBus : BitVec 64 := mauShiftWord ++ mauShiftWord
def immediateBus : BitVec 64 := immediateWord ++ immediateWord

def shiftHalfword (value count : BitVec 16) : BitVec 16 :=
  let raw := count.toNat % 32
  let amount := if raw >= 16 then raw - 16 else raw
  value.rotateLeft amount

def sbslWithShift (word shifts : BitVec 64) : BitVec 64 :=
  shiftHalfword (word.extractLsb' 48 16) (shifts.extractLsb' 48 16) ++
    shiftHalfword (word.extractLsb' 32 16) (shifts.extractLsb' 32 16) ++
    shiftHalfword (word.extractLsb' 16 16) (shifts.extractLsb' 16 16) ++
    shiftHalfword (word.extractLsb' 0 16) (shifts.extractLsb' 0 16)

theorem packed_fma_produces_shift_bus :
    packedSingleFma immediateBus immediateBus immediateBus = mauShiftBus := by
  unfold packedSingleFma immediateBus mauShiftBus
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rfl

theorem mauf_count_selects_byte_rotation (word : BitVec 64) :
    sbslWithShift word mauShiftBus = sbsl word := by
  unfold sbslWithShift sbsl shiftHalfword mauShiftBus mauShiftWord
  bv_decide

def abstractMauShift {Atom : Type} : AbstractValue Atom (BitVec 64) :=
  let immediate := AbstractValue.constant UnitKind.integerAlu immediateBus
  AbstractValue.ternary UnitKind.floatingMau packedSingleFma
    immediate immediate immediate

theorem abstractMauShift_evaluation {Atom : Type}
    (environment : Atom → BitVec 64) :
    abstractMauShift.evaluate environment = mauShiftBus := by
  calc
    abstractMauShift.evaluate environment =
        packedSingleFma immediateBus immediateBus immediateBus := by
      exact AbstractValue.ternary_evaluation UnitKind.floatingMau packedSingleFma
        (AbstractValue.constant UnitKind.integerAlu immediateBus)
        (AbstractValue.constant UnitKind.integerAlu immediateBus)
        (AbstractValue.constant UnitKind.integerAlu immediateBus) environment
    _ = mauShiftBus := packed_fma_produces_shift_bus

def abstractConvertEndian {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) : AbstractValue Atom (BitVec 64) :=
  let afterIbs := AbstractValue.unary UnitKind.integerAlu ibsl input
  let afterSbs := AbstractValue.binary UnitKind.integerAlu sbslWithShift
    afterIbs abstractMauShift
  AbstractValue.unary UnitKind.peTransfer selector2103 afterSbs

theorem abstractConvertEndian_evaluation {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) (environment : Atom → BitVec 64) :
    (abstractConvertEndian input).evaluate environment =
      answerDatapath (input.evaluate environment) := by
  unfold abstractConvertEndian
  rw [AbstractValue.unary_evaluation, AbstractValue.binary_evaluation,
    AbstractValue.unary_evaluation]
  rw [abstractMauShift_evaluation, mauf_count_selects_byte_rotation]
  rfl

theorem abstractConvertEndian_is_byteSwap {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) (environment : Atom → BitVec 64) :
    (abstractConvertEndian input).evaluate environment =
      byteSwap64 (input.evaluate environment) := by
  rw [abstractConvertEndian_evaluation, answerDatapath_is_byteSwap]

theorem abstractConvertEndian_dependencies_are_sound {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (leftEnvironment rightEnvironment : Atom → BitVec 64)
    (agree : ∀ atom, atom ∈ (abstractConvertEndian input).dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    (abstractConvertEndian input).evaluate leftEnvironment =
      (abstractConvertEndian input).evaluate rightEnvironment :=
  AbstractValue.depends_only_on_inputs _ leftEnvironment rightEnvironment agree

/-- Forwarding values carried between the three public answer lines. The
second line reads the old ALUF value for both parallel instructions, then
produces the next ALUF and MAUF values together. -/
structure ForwardState where
  aluf : BitVec 64
  mauf : BitVec 64

def firstLineState : ForwardState :=
  ⟨immediateBus, 0⟩

def executeParallelSecondLine (input : BitVec 64) (old : ForwardState) : ForwardState :=
  ⟨ibsl input, packedSingleFma old.aluf old.aluf old.aluf⟩

def executeThirdLine (state : ForwardState) : BitVec 64 :=
  selector2103 (sbslWithShift state.aluf state.mauf)

def answerProgram (input : BitVec 64) : BitVec 64 :=
  executeThirdLine (executeParallelSecondLine input firstLineState)

theorem answerProgram_eq_answerDatapath (input : BitVec 64) :
    answerProgram input = answerDatapath input := by
  unfold answerProgram executeThirdLine executeParallelSecondLine firstLineState
  rw [packed_fma_produces_shift_bus, mauf_count_selects_byte_rotation]
  rfl

/-- Apply the composed Convert Endian datapath to one 64-bit LM0 element and
write its result to one 64-bit LM1 element. This connects the bit-level
datapath to the repository's physical two-word memory layout. -/
def answerMemoryCycle (input : PEMemory.Memory .lm0) (output : PEMemory.Memory .lm1)
    (inputAddress : Fin (PEMemory.Bank.capacity .lm0))
    (outputAddress : Fin (PEMemory.Bank.capacity .lm1)) : PEMemory.Memory .lm1 :=
  FloatPEMemory.writePair output outputAddress
    (answerProgram (FloatPEMemory.readPair .lm0 input inputAddress))

theorem answerMemoryCycle_readback (input : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (inputAddress : Fin (PEMemory.Bank.capacity .lm0))
    (outputAddress : Fin (PEMemory.Bank.capacity .lm1)) :
    FloatPEMemory.readPair .lm1
      (answerMemoryCycle input output inputAddress outputAddress) outputAddress =
      answerDatapath (FloatPEMemory.readPair .lm0 input inputAddress) := by
  unfold answerMemoryCycle
  rw [FloatPEMemory.readPair_after_writePair]
  exact answerProgram_eq_answerDatapath _

theorem answerMemoryCycle_byteSwap (input : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (inputAddress : Fin (PEMemory.Bank.capacity .lm0))
    (outputAddress : Fin (PEMemory.Bank.capacity .lm1)) :
    FloatPEMemory.readPair .lm1
      (answerMemoryCycle input output inputAddress outputAddress) outputAddress =
      byteSwap64 (FloatPEMemory.readPair .lm0 input inputAddress) := by
  rw [answerMemoryCycle_readback, answerDatapath_is_byteSwap]

end ProofsLean.MNCore.ConvertEndian
