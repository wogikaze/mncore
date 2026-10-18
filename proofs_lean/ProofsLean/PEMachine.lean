import ProofsLean.ProgramLegality

/-! A four-cycle PE-line transition built from the issue-line preparer. This is
deliberately a one-PE fragment: block transfers, MAU/matrix/L1BM/L2BM units,
and whole-machine hazard timing stay unknown. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

structure ParsedPEState where
  registers : IntegerRegisterFiles
  forwarding : ProofsLean.MNCore.Forwarding.Slots
  control : ParsedMaskExecutionControl

noncomputable def executeParsedPEInstructionLine (line : InstructionLine)
    (state : ParsedPEState) : ProofsLean.StepResult ParsedPEState :=
  if checkParsedTopLine line.toParsed then
    match line with
    | .pe expressions =>
        let parsedExpressions := expressions.map NormalizedExpr.toParsed
        match parsedALUProducerLineFourCycleStep state.registers state.forwarding
            parsedExpressions state.control false with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (registers, forwarding) =>
            .ok { state with
              registers := registers
              forwarding := forwarding
              control := { state.control with
                elapsedWords := state.control.elapsedWords + 1 } }
    | .nop count none =>
        .ok { state with control := { state.control with
          elapsedWords := state.control.elapsedWords + count.val } }
    | .nop _ (some _) => .unknown
    | .mv _ => .unknown
  else
    .failure

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
    (expressions : List NormalizedExpr) (state : ParsedPEState)
    (nextRegisters : IntegerRegisterFiles)
    (nextForwarding : ProofsLean.MNCore.Forwarding.Slots)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (executed : parsedALUProducerLineFourCycleStep state.registers state.forwarding
      (expressions.map NormalizedExpr.toParsed) state.control false =
        .ok (nextRegisters, nextForwarding)) :
    instructionMachine.step (.pe expressions) state =
      .ok { state with
        registers := nextRegisters
        forwarding := nextForwarding
        control := { state.control with elapsedWords := state.control.elapsedWords + 1 } } := by
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
