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

end ProofsLean.MNCore.PEMemory
