import ProofsLean.MachineState
import ProofsLean.PEMachine

/-! A whole-state transition for the PE integer ALU producer family. It runs
the same issue-line transaction independently at every physical PE, then
updates ALU/MAU/MREADF/LBF forwarding state using the emulator's ordinary-step
rules. Other producer units remain explicitly unresolved. -/
namespace ProofsLean.MNCore

open Issue
open PEMemory

def parsedExprIsIntegerProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. => true
  | _ => false

def parsedExprIsSupportedPELineProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. | .matrixRead .. | .wait .. | .noforward => true
  | _ => false

def parsedExprIsMatrixReadProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .matrixRead .. => true
  | _ => false

def forwardingValueValid : Forwarding.Value IntegerALU.Bus → Bool
  | .known _ => true
  | .poison | .unknown => false

def updateSupportedPELineForwarding (old prepared : Forwarding.Slots)
    (noForward hasALUProducer hasMatrixReadProducer : Bool) :
    ProofsLean.StepResult Forwarding.Slots :=
  match Forwarding.advanceReference old (.issue noForward fun unit =>
      match unit with
      | .alu => if hasALUProducer then some fun cycle => prepared .alu cycle else none
      | .matrixRead =>
          if hasMatrixReadProducer then some fun cycle => prepared .matrixRead cycle else none
      | .mau | .l1ToPE => none) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok advanced =>
      .ok (fun unit cycle =>
        if unit = .l1ToPE then old unit cycle else advanced unit cycle)

def updateIntegerLineForwardingValid
    (old : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) (noForward : Bool) :
    Forwarding.Unit → Fin 4 → Bool :=
  fun unit cycle =>
    if noForward then old unit cycle
    else if unit = .l1ToPE then old unit cycle
    else forwardingValueValid (slots unit cycle)

def executeIntegerProducerLineAtPE (expressions : List ParsedExpr)
    (state : State) (pe : PEId) : ProofsLean.StepResult State :=
  let oldContext := state.peContext pe
  let coordinates := PEMemory.ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let control : ParsedMaskExecutionControl :=
    { directive := state.maskDirective
      context := context
      elapsedWords := state.hazardClock }
  let oldSlots := state.forwarding pe
  let matrixStore := state.matrixRegisters context.group context.l2b context.l1b
  match parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe) oldSlots
      matrixStore expressions control false with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (registers, preparedSlots) =>
      let noForward := expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false
      let hasALUProducer := expressions.any parsedExprIsIntegerProducer
      let hasMatrixReadProducer := expressions.any parsedExprIsMatrixReadProducer
      match updateSupportedPELineForwarding oldSlots preparedSlots
          noForward hasALUProducer hasMatrixReadProducer with
      | .failure => .failure
      | .unknown => .unknown
      | .ok forwarding =>
          let forwardingValid := updateIntegerLineForwardingValid
            (state.forwardingValid pe) forwarding noForward
          .ok { state with
            peRegisters := fun other =>
              if other = pe then registers else state.peRegisters other
            forwarding := fun other =>
              if other = pe then forwarding else state.forwarding other
            forwardingValid := fun other =>
              if other = pe then forwardingValid else state.forwardingValid other }

def executeIntegerProducerLineAtPEs (expressions : List ParsedExpr)
    (pes : List PEId) (state : State) : ProofsLean.StepResult State :=
  match pes with
  | [] => .ok state
  | pe :: rest =>
      match executeIntegerProducerLineAtPE expressions state pe with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeIntegerProducerLineAtPEs expressions rest next

/-- Whole-machine line transition for parsed integer ALU, zero, immediate,
matrix-read, wait, and noforward expressions. Reads and prepared writes use the
existing per-PE transactional semantics; matrix data is read from the PE's
physical group/L2B/L1B MAB bank. The PE traversal is pure, so a failure or
unknown on any PE returns no partially updated state. -/
noncomputable def executeIntegerProducerInstructionLine
    (line : InstructionLine) (state : State) : ProofsLean.StepResult State :=
  if !checkParsedTopLine line.toParsed then .failure
  else
    match line with
    | .pe normalizedExpressions =>
        let expressions := normalizedExpressions.map NormalizedExpr.toParsed
        if expressions.all parsedExprIsSupportedPELineProducer then
          match executeIntegerProducerLineAtPEs expressions (List.finRange 4096) state with
          | .failure => .failure
          | .unknown => .unknown
          | .ok next =>
              .ok { next with hazardClock := next.hazardClock + InstructionLine.cost line }
        else .unknown
    | .nop _ _ | .mv _ => .unknown

noncomputable def integerProducerMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := State
  Input := Unit
  step := fun line state => executeIntegerProducerInstructionLine line state
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem integerProducerMachine_issue_failure (line : InstructionLine)
    (state : State) (rejected : checkParsedTopLine line.toParsed = false) :
    integerProducerMachine.step line state = .failure := by
  simp [integerProducerMachine, executeIntegerProducerInstructionLine, rejected]

theorem executeIntegerProducerInstructionLine_pe_success
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (supported : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (executed : executeIntegerProducerLineAtPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state =
        .ok next) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { next with
        hazardClock := next.hazardClock + InstructionLine.cost (.pe normalizedExpressions) } := by
  simp [executeIntegerProducerInstructionLine, accepted, supported, executed]

end ProofsLean.MNCore
