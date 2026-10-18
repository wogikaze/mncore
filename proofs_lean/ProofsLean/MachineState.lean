import ProofsLean.ParsedIntegerStep
import ProofsLean.L1Transfer
import ProofsLean.MVSemantics

/-! Whole-machine state vocabulary assembled from the existing PE, block-memory,
forwarding, mask-control, and hazard-clock components. This is a state type,
not yet a complete transition semantics or an initialization policy. -/
namespace ProofsLean.MNCore

abbrev PEId := Fin 4096

structure PendingMv where
  tag : Option (Fin 256)
  writes : List (MVSemantics.Cell × BitVec 64)

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
  /-- Per-group 32-bit DRAM address registers and their 512-word staging buffers. -/
  dar : Fin 4 → Fin 1024 → BitVec 32
  darBuffer : Fin 4 → Fin 512 → BitVec 32
  /-- Shared DARBUF read pointer and DAR write pointer used by l2bmdarw. -/
  darBufferReadAddress : Fin 512
  darWriteAddress : Fin 1024
  /-- MV tags whose transfers have completed in the synchronous transfer model. -/
  mvCompletedTags : Fin 256 → Bool
  /-- MV writes staged from the issue-time memory snapshot, in issue order. -/
  pendingMv : List PendingMv
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

/-- Zeroed PE register files used by `viz/core/src/machine.rs::Machine::new`.
Untouched LM/GRF/T and mask-register locations all read as zero there. -/
def zeroInitialPERegisterFiles : PEMemory.IntegerRegisterFiles where
  lm0 := fun _ => 0
  lm1 := fun _ => 0
  grf0 := fun _ => 0
  grf1 := fun _ => 0
  t := fun _ => 0
  maskRegisters := fun _ _ => 0

/-- Concrete initial state of the Rust whole-machine simulator. PE memories,
matrix registers, L1BM/L2BM/PDM/DRAM, BAR/T, and forwarding payloads start at
zero. Forwarding and turnaround validity start false, matching the simulator's
uninitialized-forwarding and unwritten-`$lbi` errors. The Rust default mask
width is zero with every target disabled. -/
def rustSimulatorInitialState : State where
  peRegisters := fun _ => zeroInitialPERegisterFiles
  l1bm := fun _ _ => 0
  l1bmTurnaround := fun _ _ _ => 0
  l1bmTurnaroundValid := false
  blockMemory := fun _ => 0
  dar := fun _ _ => 0
  darBuffer := fun _ _ => 0
  darBufferReadAddress := ⟨0, by decide⟩
  darWriteAddress := ⟨0, by decide⟩
  mvCompletedTags := fun _ => false
  pendingMv := []
  matrixRegisters := fun _ _ _ _ _ _ => 0
  forwarding := fun _ unit _ => .known (match unit with
    | .alu | .mau | .matrixRead | .l1ToPE => ⟨0, 0⟩)
  forwardingValid := fun _ _ _ => false
  maskDirective :=
    { widthWords := 0, targets := {}, entry := ⟨0, by decide⟩ }
  peContext := fun pe => PEMemory.ParsedIntegerContext.ofLinearIndex pe
  hazardClock := 0

theorem rustSimulatorInitialState_pe_registers_zero (pe : PEId) :
    rustSimulatorInitialState.peRegisters pe = zeroInitialPERegisterFiles := rfl

theorem rustSimulatorInitialState_forwarding_invalid (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) :
    rustSimulatorInitialState.forwardingValid pe unit cycle = false := rfl

theorem rustSimulatorInitialState_l1bm_turnaround_invalid :
    rustSimulatorInitialState.l1bmTurnaroundValid = false := rfl

theorem rustSimulatorInitialState_clock_zero :
    rustSimulatorInitialState.hazardClock = 0 := rfl

end ProofsLean.MNCore
