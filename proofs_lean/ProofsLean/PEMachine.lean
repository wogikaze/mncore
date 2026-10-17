import ProofsLean.ProgramLegality

/-! A four-cycle PE-line transition built from the existing integer register
stepper. This is deliberately a one-PE fragment: forwarding, hazard timing,
MV transfers, and non-integer units stay unknown. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

structure ParsedPEState where
  registers : IntegerRegisterFiles
  control : ParsedMaskExecutionControl

def executeParsedPECycles (expressions : List ParsedExpr)
    (cycles : List (Fin 4)) (state : ParsedPEState) :
    ProofsLean.StepResult ParsedPEState :=
  match cycles with
  | [] => .ok state
  | cycle :: rest =>
      let cycleControl :=
        { state.control with context := { state.control.context with cycle := cycle } }
      match parsedIntegerMaskedLineStep state.registers expressions cycleControl with
      | .failure => .failure
      | .unknown => .unknown
      | .ok registers =>
          executeParsedPECycles expressions rest { state with registers := registers }

noncomputable def executeParsedPEInstructionLine (line : InstructionLine)
    (state : ParsedPEState) : ProofsLean.StepResult ParsedPEState :=
  if checkParsedTopLine line.toParsed then
    match line with
    | .pe expressions =>
        match executeParsedPECycles (expressions.map NormalizedExpr.toParsed)
            (List.finRange 4) state with
        | .failure => .failure
        | .unknown => .unknown
        | .ok next =>
            .ok { next with control := { next.control with
              elapsedWords := next.control.elapsedWords + 1 } }
    | .nop count none =>
        .ok { state with control := { state.control with
          elapsedWords := state.control.elapsedWords + count.val } }
    | .nop _ (some _) => .unknown
    | .mv _ => .unknown
  else
    .failure

theorem executeParsedPECycles_empty (state : ParsedPEState) :
    executeParsedPECycles [] [] state = .ok state := rfl

theorem executeParsedPEInstructionLine_issue_failure
    (line : InstructionLine) (state : ParsedPEState)
    (rejected : checkParsedTopLine line.toParsed = false) :
    executeParsedPEInstructionLine line state = .failure := by
  simp [executeParsedPEInstructionLine, rejected]

/-! The first stateful machine projection. Its legal domain remains every
normalized row; the transition reports the issue checker and the supported
integer-PE fragment directly. Rows whose effects are not implemented remain
`.unknown`, so this machine cannot yet be sealed as a complete ISA model. -/

noncomputable def instructionMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := ParsedPEState
  Input := Unit
  step := executeParsedPEInstructionLine
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem instructionMachine_legal_all
    (program : instructionMachine.Program) : instructionMachine.legal program := by
  trivial

theorem instructionMachine_issue_failure
    (line : InstructionLine) (state : ParsedPEState)
    (rejected : checkParsedTopLine line.toParsed = false) :
    instructionMachine.step line state = .failure :=
  executeParsedPEInstructionLine_issue_failure line state rejected

theorem instructionMachine_accepted_pe_executes
    (expressions : List NormalizedExpr) (state next : ParsedPEState)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (executed : executeParsedPECycles (expressions.map NormalizedExpr.toParsed)
      (List.finRange 4) state = .ok next) :
    instructionMachine.step (.pe expressions) state =
      .ok { next with control := { next.control with
        elapsedWords := next.control.elapsedWords + 1 } } := by
  simp [instructionMachine, executeParsedPEInstructionLine, accepted, executed]

theorem instructionMachine_nop_advances
    (count : {n : Nat // 0 < n}) (state : ParsedPEState)
    (accepted : checkParsedTopLine
      (InstructionLine.nop count none).toParsed = true) :
    instructionMachine.step (.nop count none) state =
      .ok { state with control := { state.control with
        elapsedWords := state.control.elapsedWords + count.val } } := by
  simp [instructionMachine, executeParsedPEInstructionLine, accepted]

end ProofsLean.MNCore.PEMemory
