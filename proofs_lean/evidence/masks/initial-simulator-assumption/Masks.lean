import ProofsLean.PEMemory

/- MN-Core 2 manual (2026-06-02), §3.6.2. Pure mask datapath/state primitives.
No full VSM syntax, instruction scheduling, or port legality is asserted. -/
namespace ProofsLean.MNCore.Masks

open IntegerALU (Bus BusResult)

inductive Width where
  | long | double
  deriving DecidableEq, Repr

abbrev RegisterFile := Fin 15 → Fin 4 → BitVec 4

/-- Variable register index 0 denotes physical entry 1. Fixed entries cannot
be written through this interface. Cycle 0 uses the MSB of a fixed pattern. -/
def readEntry (registers : RegisterFile) (entry : Fin 32) (cycle : Fin 4) : BitVec 4 :=
  if zero : entry.val = 0 then 15
  else if writable : entry.val < 16 then
    registers ⟨entry.val - 1, by omega⟩ cycle
  else if (BitVec.ofNat 4 entry.val).getLsbD (3 - cycle.val) then 15 else 0

def writeRegister (registers : RegisterFile) (entry : Fin 15) (cycle : Fin 4)
    (newFlags selection : BitVec 4) : RegisterFile := fun other time =>
  if other = entry ∧ time = cycle then newFlags &&& selection else registers other time

theorem register_zero_mask_writes_zero (registers : RegisterFile) (entry : Fin 15)
    (cycle : Fin 4) (newFlags : BitVec 4) :
    writeRegister registers entry cycle newFlags 0 entry cycle = 0 := by
  simp [writeRegister]

theorem register_write_preserves_other_entry (registers : RegisterFile) (entry other : Fin 15)
    (cycle time : Fin 4) (newFlags selection : BitVec 4) (different : other ≠ entry) :
    writeRegister registers entry cycle newFlags selection other time = registers other time := by
  simp [writeRegister, different]

def halfMask (flags : BitVec 4) : BitVec 64 :=
  (List.range 4).foldl (fun acc bit =>
    acc ||| (if flags.getLsbD bit then (0xffff : BitVec 64) <<< (16 * bit) else 0)) 0

def wordMask (flag : Bool) : BitVec 32 := if flag then 0xffffffff else 0

def doubleMask (flags : BitVec 4) : Bus :=
  ⟨wordMask (flags.getLsbD 3) ++ wordMask (flags.getLsbD 2),
   wordMask (flags.getLsbD 1) ++ wordMask (flags.getLsbD 0)⟩

/-- The manual's general long-mask wording says the low long-word is not
affected. The reference binary skips its write if ALL four flags are zero.
These targets remain explicit; finite tests cannot establish their equivalence. -/
inductive LongWritePolicy where
  | manualReading | referenceBinary
  deriving DecidableEq, Repr

def writeEnable (policy : LongWritePolicy) (width : Width) (flags : BitVec 4) : Bus :=
  match width with
  | .double => doubleMask flags
  | .long => ⟨halfMask flags, match policy with
      | .manualReading => BitVec.allOnes 64
      | .referenceBinary => if flags = 0 then 0 else BitVec.allOnes 64⟩

def merge (old new enable : Bus) : Bus :=
  ⟨(old.high &&& ~~~enable.high) ||| (new.high &&& enable.high),
   (old.low &&& ~~~enable.low) ||| (new.low &&& enable.low)⟩

def writeBus (policy : LongWritePolicy) (width : Width) (flags : BitVec 4) (old new : Bus) : Bus :=
  merge old new (writeEnable policy width flags)

/-- For an unqualified full-width write, the ambiguous long-mask zero case
remains unknown. Narrow writes require a separate memory-access composition. -/
def partialWriteBus (width : Width) (flags : BitVec 4) (old new : Bus) : StepResult Bus :=
  if width = .long ∧ flags = 0 then .unknown
  else .ok (writeBus .referenceBinary width flags old new)

theorem unresolved_long_zero_write_unknown (old new : Bus) :
    partialWriteBus .long 0 old new = .unknown := rfl

def flushBus (width : Width) (flags : BitVec 4) (data : Bus) : Bus :=
  let enable : Bus := match width with
    | .long => ⟨halfMask flags, BitVec.allOnes 64⟩
    | .double => doubleMask flags
  ⟨data.high &&& enable.high, data.low &&& enable.low⟩

def flushResult (width : Width) (flags : BitVec 4) (result : BusResult) : BusResult :=
  ⟨flushBus width flags result.value, result.flags⟩

theorem flush_preserves_flags (width : Width) (flags : BitVec 4)
    (result : BusResult) (bit : Fin 4) :
    (flushResult width flags result).flags bit = result.flags bit := rfl

theorem long_flush_preserves_low (flags : BitVec 4) (data : Bus) :
    (flushBus .long flags data).low = data.low := by
  change data.low &&& BitVec.allOnes 64 = data.low
  exact BitVec.and_allOnes

theorem reference_long_zero_write_preserves (old new : Bus) :
    writeBus .referenceBinary .long 0 old new = old := by
  cases old
  simp [writeBus, merge, writeEnable, halfMask, List.range_succ]
  constructor <;> exact BitVec.and_allOnes

theorem manual_long_zero_write_copies_low (old new : Bus) :
    (writeBus .manualReading .long 0 old new).low = new.low := by
  simp [writeBus, merge, writeEnable]
  exact BitVec.and_allOnes

structure Selection where
  width : Width
  entry : Fin 32

/-- The caller computes hasSingleWriteMask across ALL destinations in the
step. A single-line write mask cancels the multiline directive for every target,
including destinations with no single-line mask of their own. -/
def resolveSelection (multiline : Option Selection) (hasSingleWriteMask : Bool)
    (own : Option Selection) : Option Selection :=
  if hasSingleWriteMask then own else multiline

theorem single_line_cancels_other_target_directive (multiline : Option Selection) :
    resolveSelection multiline true none = none := rfl

theorem no_single_line_uses_directive (multiline : Option Selection) :
    resolveSelection multiline false none = multiline := rfl

example : readEntry (fun _ _ => 0) 17 0 = 0 ∧ readEntry (fun _ _ => 0) 17 3 = 15 := by decide
example : readEntry (fun _ _ => 0) 0 2 = 15 ∧ readEntry (fun _ _ => 0) 31 2 = 15 := by decide

end ProofsLean.MNCore.Masks
