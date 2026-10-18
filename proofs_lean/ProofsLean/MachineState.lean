import ProofsLean.ParsedIntegerStep
import ProofsLean.L1Transfer
import ProofsLean.MVSemantics

/-! Whole-machine state vocabulary assembled from the existing PE, block-memory,
forwarding, mask-control, and hazard-clock components. This is a state type,
not yet a complete transition semantics or an initialization policy. -/
namespace ProofsLean.MNCore

abbrev PEId := Fin 4096

structure State where
  /-- LM0/LM1/GRF0/GRF1/T and per-PE OMR mask registers. -/
  peRegisters : PEId → PEMemory.IntegerRegisterFiles
  /-- Sixty-four independent L1B banks, each holding 8192 long words. -/
  l1bm : Fin 64 → L1Transfer.L1Bank
  /-- Per-L1B turnaround values ($lbi), four cycles by 64 long words. -/
  l1bmTurnaround : Fin 64 → L1Transfer.L1Turnaround
  /-- Rust's `lbi_error.is_none()`: false after a PE step without a transfer. -/
  l1bmTurnaroundValid : Bool
  /-- Unified cell-addressed store for L2BM, PDM, and DRAM. -/
  blockMemory : MVSemantics.Memory
  /-- Matrix registers, indexed by physical group/L2B/L1B and local MAB. -/
  matrixRegisters : Fin 4 → Fin 2 → Fin 8 → PEMemory.ParsedMatrixReadStore
  /-- ALUF, MAUF, matrix-read forwarding, and L1-to-PE forwarding buses. -/
  forwarding : PEId → Forwarding.Slots
  /-- Per-PE validity is separate from known/poison/unknown bus contents. -/
  forwardingValid : PEId → Forwarding.Unit → Fin 4 → Bool
  /-- Current multiline mask selection. -/
  maskDirective : Issue.ParsedMaskDirective
  /-- Per-PE BAR/T/coordinate context used by address lowering. -/
  peContext : PEId → PEMemory.ParsedIntegerContext
  /-- Scored issue-word clock used by PE and block hazard timing. -/
  hazardClock : Nat

/-- A state predicate for use until the judge's initialization behavior is
settled. It deliberately makes no zero-fill or arbitrary-memory claim. -/
def InitialStateUnspecified : State → Prop := fun _ => True

theorem every_state_is_currently_admissible (state : State) :
    InitialStateUnspecified state := trivial

end ProofsLean.MNCore
