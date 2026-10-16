import ProofsLean.Issue
import ProofsLean.L1Transfer

/- L1BM hazard access extraction from the parsed expression record, following
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

end ProofsLean.MNCore.HazardTrace
