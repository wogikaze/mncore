import ProofsLean.Issue
import ProofsLean.L1Transfer

/- L1BM/L2BM hazard access extraction from the parsed expression record, following
`viz/core/src/hazard.rs::expr_accesses`. -/
namespace ProofsLean.MNCore.HazardTrace

open ProofsLean.MNCore.Issue
open ProofsLean.MNCore.L1Transfer

def firstL1bm : List ParsedOperand → Option (Nat × Option Nat)
  | .l1bm width address :: _ => some (width, address)
  | _ => none

def firstMemoryExt : List ParsedOperand → Bool
  | .mem _ _ ext _ _ :: _ => ext
  | _ => false

def isHalfFloatAdd (rrn : ParsedRrn) : Bool :=
  rrn.precision == 'h' && rrn.op == .fadd

def parsedL1HazardInfo (op : ParsedL1Op) :
    L1HazardOp × Bool :=
  match op with
  | .pbcast => (.pbcast, false)
  | .mbcast => (.mbcast, false)
  | .mwrite _ => (.mwrite, false)
  | .m4bcast => (.m4bcast, false)
  | .m4write _ => (.m4write, false)
  | .reduce rrn round => (.reduce, round || isHalfFloatAdd rrn)
  | .reduce4 rrn round => (.reduce4, round || isHalfFloatAdd rrn)
  | .distrib _ => (.distrib, false)
  | .gather _ => (.gather, false)

def operandBlockAddress (operand : ParsedOperand) : Nat :=
  match operand with
  | .l1bm _ address => address.getD 0
  | .l2bm address _ => address
  | _ => 0

def l1BlockRangeEvents (mask : Nat) (write : Bool)
    (path : ProofsLean.MNCore.PEMemory.BlockHazardPath)
    (base stride length startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  (List.finRange 8).flatMap fun bank =>
    if Nat.testBit mask bank.val then
      (List.finRange 4).map fun cycle =>
        ⟨.l1bm bank, path, write,
          some ((base + cycle.val * stride) % l1bmLongWords),
          length, startWord, cycle⟩
    else []

def l2BlockRangeEvents (write : Bool)
    (path : ProofsLean.MNCore.PEMemory.BlockHazardPath)
    (base stride startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  (List.finRange 2).flatMap fun bank =>
    (List.finRange 4).map fun cycle =>
      ⟨.l2bm bank, path, write,
        some ((base + cycle.val * stride) % 32768), stride, startWord, cycle⟩

theorem l2BlockRangeEvents_count (write : Bool)
    (path : ProofsLean.MNCore.PEMemory.BlockHazardPath)
    (base stride startWord : Nat) :
    (l2BlockRangeEvents write path base stride startWord).length = 8 := by
  simp [l2BlockRangeEvents, List.finRange]

def multicastDestinationMask (sourceMask immode : Nat) : Nat := Id.run do
  let mut destinationMask := 0
  for source in List.range 8 do
    if Nat.testBit sourceMask source then
      for destination in List.range 8 do
        if destination != source &&
            (Nat.land destination immode) == (Nat.land source immode) then
          destinationMask := Nat.lor destinationMask (2 ^ destination)
  return destinationMask

def l1ExprHazardEvents (expr : ParsedExpr) (startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  match expr.op with
  | .l1bm op =>
      let toPE := match expr.sources with
        | .l1bm _ _ :: _ => true
        | _ => false
      let blockOperand := if toPE then firstL1bm expr.sources else firstL1bm expr.destinations
      match blockOperand with
      | none => []
      | some (width, some base) =>
          let twoLongWords := width == 4
          let ext := firstMemoryExt expr.sources
          let (hazardOp, rounded) := parsedL1HazardInfo op
          (List.finRange 8).flatMap fun bank =>
            (List.finRange 4).map fun cycle =>
              l1HazardEvent bank ⟨base % l1bmLongWords,
                Nat.mod_lt _ (by decide)⟩ hazardOp twoLongWords rounded ext toPE
                startWord cycle
      | some (_, none) => []
  | .l2bm op =>
      let a0 := match expr.sources with
        | operand :: _ => operandBlockAddress operand
        | [] => 0
      let a1 := match expr.destinations with
        | operand :: _ => operandBlockAddress operand
        | [] => 0
      let l1 := fun mask write (path : ProofsLean.MNCore.PEMemory.BlockHazardPath)
          base stride length =>
        l1BlockRangeEvents mask write path base stride length startWord
      let l2 := fun write (path : ProofsLean.MNCore.PEMemory.BlockHazardPath)
          base stride =>
        l2BlockRangeEvents write path base stride startWord
      match op with
      | .bcast set => l1 set.mask true .l2ToL1 a1 16 16 ++
          l2 false .l2ToL1 a0 16
      | .bcast2 set => l1 set.mask true .l2ToL1 a1 16 16 ++
          l2 false .l2ToL1 a0 64
      | .distrib set => l1 set.mask true .l2ToL1 a1 8 8 ++
          l2 false .l2ToL1 a0 64
      | .fromL1b bank => l1 (2 ^ bank) false .l1ToL2 a0 16 16 ++
          l2 true .l1ToL2 a1 16
      | .reduce _ set => l1 set.mask false .l1ToL2 a0 16 16 ++
          l2 true .l1ToL2 a1 16
      | .reduce2 _ => l1 255 false .l1ToL2 a0 16 16 ++
          l2 true .l1ToL2 a1 64
      | .gather => l1 255 false .l1ToL2 a0 8 8 ++
          l2 true .l1ToL2 a1 64
      | .imcast set =>
          let destinationMask := multicastDestinationMask set.mask set.immode
          l1 set.mask false .multicast a0 16 16 ++
            l1 destinationMask true .multicast a1 16 16
      | .dars | .darw => []
  | _ => []

def l1LineHazardEvents
    (line : ProofsLean.MNCore.PEMemory.ParsedMaskedIssueLine) (startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  match line with
  | ProofsLean.MNCore.PEMemory.ParsedMaskedIssueLine.nop => []
  | ProofsLean.MNCore.PEMemory.ParsedMaskedIssueLine.pe expressions => expressions.flatMap fun expression =>
      l1ExprHazardEvents expression startWord

/-- Gather parsed L1BM events over a source stream. Directives have zero issue
cost; each issue word advances the event clock by one word. -/
def l1SourceHazardEvents :
    List (ProofsLean.ControlNormalization.Statement
      ParsedMaskDirective
      ProofsLean.MNCore.PEMemory.ParsedMaskedIssueLine) → Nat →
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess
  | [], _ => []
  | ProofsLean.ControlNormalization.Statement.directive _ :: rest, startWord =>
      l1SourceHazardEvents rest startWord
  | ProofsLean.ControlNormalization.Statement.issue line :: rest, startWord =>
      l1LineHazardEvents line startWord ++
        l1SourceHazardEvents rest (startWord + 1)

def blockHazardConstraintsBetween
    (earlier later : List ProofsLean.MNCore.PEMemory.TimedBlockAccess) :
    List ProofsLean.MNCore.PEMemory.TimedBlockHazardConstraint :=
  earlier.flatMap fun write => later.filterMap fun access =>
    ProofsLean.MNCore.PEMemory.makeTimedBlockHazardConstraint? write access

theorem blockHazardConstraintsBetween_complete
    (earlier later : List ProofsLean.MNCore.PEMemory.TimedBlockAccess)
    (constraint : ProofsLean.MNCore.PEMemory.TimedBlockHazardConstraint) :
    constraint ∈ blockHazardConstraintsBetween earlier later ↔
      ∃ write, write ∈ earlier ∧ ∃ access, access ∈ later ∧
        ProofsLean.MNCore.PEMemory.makeTimedBlockHazardConstraint? write access =
          some constraint := by
  simp [blockHazardConstraintsBetween, List.mem_flatMap, List.mem_filterMap]

def collectBlockHazardConstraintsAux
    (events : List ProofsLean.MNCore.PEMemory.TimedBlockAccess) :
    List ProofsLean.MNCore.PEMemory.TimedBlockHazardConstraint :=
  match events with
  | [] => []
  | event :: rest =>
      blockHazardConstraintsBetween [event] rest ++
        collectBlockHazardConstraintsAux rest

def collectBlockHazardConstraints
    (events : List ProofsLean.MNCore.PEMemory.TimedBlockAccess) :=
  collectBlockHazardConstraintsAux events

def l1SourceHazardConstraints
    (source : List (ProofsLean.ControlNormalization.Statement
      ParsedMaskDirective ProofsLean.MNCore.PEMemory.ParsedMaskedIssueLine))
    (startWord : Nat) :=
  collectBlockHazardConstraints (l1SourceHazardEvents source startWord)

def parsedMvOperandHazardEvents (transfer : ParsedMv) (write : Bool)
    (operand : Option ParsedMvOperand) (startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  match operand with
  | some (.l2bm address _ selectedBank) =>
      (List.finRange 2).filterMap fun bank =>
        if selectedBank.isNone || selectedBank.map Fin.val == some bank.val then
          some ⟨.l2bm bank, .mv, write, some (address.val % 2 ^ 32),
            if transfer.kind == .nop then 0 else transfer.size.val % 2 ^ 32,
            startWord, ⟨0, by decide⟩⟩
        else none
  | _ => []

theorem mv_u64_cast_to_u32_range (value : Nat) :
    value % 2 ^ 32 < 2 ^ 32 := by
  exact Nat.mod_lt _ (by decide)

theorem parsedMvOperandHazardEvents_count (transfer : ParsedMv) (write : Bool)
    (operand : Option ParsedMvOperand) (startWord : Nat) :
    (parsedMvOperandHazardEvents transfer write operand startWord).length =
      match operand with
      | some (.l2bm _ _ none) => 2
      | some (.l2bm _ _ (some bank)) => if bank.val < 2 then 1 else 0
      | _ => 0 := by
  cases operand with
  | none => rfl
  | some operand =>
    cases operand with
    | pdm address group => simp [parsedMvOperandHazardEvents]
    | dram address group indirect => simp [parsedMvOperandHazardEvents]
    | l2bm address group selected =>
      cases selected with
      | none => simp [parsedMvOperandHazardEvents]
      | some bank =>
        have bank_cases : bank.val = 0 ∨ bank.val = 1 ∨ 2 ≤ bank.val := by omega
        rcases bank_cases with h | h | h
        · have hb : bank = 0 := Fin.ext h
          subst bank
          simp [parsedMvOperandHazardEvents, List.finRange]
        · have hb : bank = 1 := Fin.ext h
          subst bank
          simp [parsedMvOperandHazardEvents, List.finRange]
        · have hneq0 : bank.val ≠ 0 := by omega
          have hneq1 : bank.val ≠ 1 := by omega
          simp [parsedMvOperandHazardEvents, List.finRange, hneq0, hneq1, h]

def parsedMvHazardEvents (transfer : ParsedMv) (startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  parsedMvOperandHazardEvents transfer false transfer.source startWord ++
    parsedMvOperandHazardEvents transfer true transfer.destination startWord

theorem parsedMvHazardEvents_count (transfer : ParsedMv) (startWord : Nat) :
    (parsedMvHazardEvents transfer startWord).length =
      (parsedMvOperandHazardEvents transfer false transfer.source startWord).length +
        (parsedMvOperandHazardEvents transfer true transfer.destination startWord).length := by
  simp [parsedMvHazardEvents]

def parsedLineBlockHazardEvents (line : ParsedLine) (startWord : Nat) :
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess :=
  match line with
  | .pe expressions => expressions.flatMap fun expression =>
      l1ExprHazardEvents expression startWord
  | .mv transfer => parsedMvHazardEvents transfer startWord
  | _ => []

def parsedSourceBlockHazardEvents : List ParsedLine → Nat →
    List ProofsLean.MNCore.PEMemory.TimedBlockAccess
  | [], _ => []
  | line :: rest, startWord =>
      parsedLineBlockHazardEvents line startWord ++
        parsedSourceBlockHazardEvents rest
          (startWord +
            (ProofsLean.MNCore.PEMemory.ParsedLine.parsedMaskedIssueWords? line).getD 0)

theorem parsedSourceBlockHazardEvents_single_mv_count
    (transfer : ParsedMv) (startWord : Nat) :
    (parsedSourceBlockHazardEvents [.mv transfer] startWord).length =
      (parsedMvHazardEvents transfer startWord).length := by
  simp [parsedSourceBlockHazardEvents, parsedLineBlockHazardEvents, parsedMvHazardEvents]

def parsedSourceBlockHazardConstraints (source : List ParsedLine)
    (startWord : Nat) :=
  collectBlockHazardConstraints (parsedSourceBlockHazardEvents source startWord)

end ProofsLean.MNCore.HazardTrace
