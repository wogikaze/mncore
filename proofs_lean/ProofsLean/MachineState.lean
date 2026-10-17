import ProofsLean.ParsedIntegerStep
import ProofsLean.L1Transfer
import ProofsLean.MVSemantics

/-! Whole-machine state vocabulary assembled from the existing PE, block-memory,
forwarding, mask-control, and hazard-clock components. This is a state type,
not yet a complete transition semantics or an initialization policy. -/
namespace ProofsLean.MNCore

abbrev PEId := Fin 2048

structure State where
  /-- LM0/LM1/GRF0/GRF1/T and per-PE OMR mask registers. -/
  peRegisters : PEId → PEMemory.IntegerRegisterFiles
  /-- Eight independent L1B banks, each holding 8192 long words. -/
  l1bm : Fin 8 → L1Transfer.L1Bank
  /-- Unified cell-addressed store for L2BM, PDM, and DRAM. -/
  blockMemory : MVSemantics.Memory
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
