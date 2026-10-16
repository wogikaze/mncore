import ProofsLean.IntegerALU
import ProofsLean.ParsedIntegerStep

/- Raw L1BM-to-PE broadcast transfer, mirroring `Blocks::l1_to_pe`
(`viz/core/src/blocks.rs`). This models one L1B bank; PE destination writes,
other transfer opcodes, turnaround updates, masks, and issue timing remain
separate obligations. -/
namespace ProofsLean.MNCore.L1Transfer

open ProofsLean.MNCore.IntegerALU

def l1bmLongWords : Nat := 8192

abbrev L1Bank := Fin l1bmLongWords → BitVec 64
abbrev L1Turnaround := Fin 4 → Fin 64 → BitVec 64

inductive L1ReadSource where
  | addressed (base : Fin l1bmLongWords)
  | turnaround (values : L1Turnaround)

def addressAt (base : Fin l1bmLongWords) (offset : Nat) : Fin l1bmLongWords :=
  ⟨(base.val + offset) % l1bmLongWords, Nat.mod_lt _ (by decide)⟩

def readL1Long (memory : L1Bank) (source : L1ReadSource)
    (cycle : Fin 4) (offset : Nat) : BitVec 64 :=
  match source with
  | .addressed base => memory (addressAt base offset)
  | .turnaround values => values cycle ⟨offset % 64, Nat.mod_lt _ (by decide)⟩

/-- `pbcast` reads one long word per cycle, and a second word four positions
later only for a two-long-word (`wl == 4`) source. -/
def pbcast (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) : Bus :=
  { high := memory (addressAt base cycle.val)
    low := if twoLongWords then memory (addressAt base (cycle.val + 4)) else 0 }

/-- A turnaround-register `pbcast` reads fixed offsets in the current cycle's
64-word L1B block; unlike an addressed source, its offset does not advance. -/
def pbcastTurnaround (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) : Bus :=
  { high := turnaround cycle 0
    low := if twoLongWords then turnaround cycle 4 else 0 }

/-- `mbcast` distributes one long word per PE from its MAB block. Addressed
sources advance by eight words per cycle; turnaround reads use PE-relative
offsets, and retain the paired long word even for a one-word destination. -/
def mbcast (memory : L1Bank) (source : L1ReadSource)
    (twoLongWords : Bool) (pe cycle : Fin 4) : Bus :=
  match source with
  | .addressed _ =>
      let offset := (if twoLongWords then cycle.val * 8 else cycle.val * 4) + pe.val
      { high := readL1Long memory source cycle offset
        low := if twoLongWords then readL1Long memory source cycle (offset + 4) else 0 }
  | .turnaround _ =>
      { high := readL1Long memory source cycle pe.val
        low := readL1Long memory source cycle (4 + pe.val) }

/-- `m4bcast` reads the four-MAB block selected by the high two MAB bits.
Each cycle advances by 16 or 32 long words according to source width. -/
def m4bcast (memory : L1Bank) (source : L1ReadSource)
    (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) : Bus :=
  let groupIndex := mabGroup.val
  let base := match source with
    | .addressed _ => cycle.val * 32
    | .turnaround _ => 0
  let offset := match twoLongWords, source with
    | true, _ => base + groupIndex * 8 + pe.val
    | false, .addressed _ => cycle.val * 16 + groupIndex * 4 + pe.val
    | false, .turnaround _ => groupIndex * 4 + pe.val
  { high := readL1Long memory source cycle offset
    low := if twoLongWords then readL1Long memory source cycle (offset + 4) else 0 }

/-- Euclidean source MAB selection used by Rust `distrib`: subtract the
signed MAB difference and wrap into the 16 MABs of one L1B. -/
def distribSourceMab (mab : Fin 16) (mabDiff : Int) : Fin 16 :=
  let wrapped := (Int.ofNat mab.val - mabDiff) % 16
  ⟨wrapped.toNat, by
    have hnonneg : 0 ≤ wrapped := Int.emod_nonneg _ (by decide)
    have hlt : wrapped < 16 := Int.emod_lt_of_pos _ (by decide)
    omega⟩

/-- L1BM `distrib` selects the source MAB for the destination and reads one
long word per PE; addressed banks advance by 64 words per cycle. -/
def distrib (memory : L1Bank) (source : L1ReadSource)
    (mabDiff : Int) (mab : Fin 16) (pe cycle : Fin 4) : Bus :=
  let sourceMab := distribSourceMab mab mabDiff
  let base := match source with
    | .addressed _ => cycle.val * 64
    | .turnaround _ => 0
  let offset := base + sourceMab.val * 4 + pe.val
  { high := readL1Long memory source cycle offset, low := 0 }

theorem pbcast_high (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcast memory base twoLongWords cycle).high = memory (addressAt base cycle.val) := rfl

theorem pbcast_low (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcast memory base twoLongWords cycle).low =
      if twoLongWords then memory (addressAt base (cycle.val + 4)) else 0 := rfl

theorem pbcastTurnaround_high (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcastTurnaround turnaround twoLongWords cycle).high = turnaround cycle 0 := rfl

theorem pbcastTurnaround_low (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcastTurnaround turnaround twoLongWords cycle).low =
      if twoLongWords then turnaround cycle 4 else 0 := rfl

theorem addressAt_wraps (base : Fin l1bmLongWords) (offset : Nat) :
    (addressAt base offset).val = (base.val + offset) % l1bmLongWords := rfl

theorem mbcast_addressed_words (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (pe cycle : Fin 4) :
    (mbcast memory (.addressed base) twoLongWords pe cycle).high =
        memory (addressAt base
          ((if twoLongWords then cycle.val * 8 else cycle.val * 4) + pe.val)) ∧
      (mbcast memory (.addressed base) twoLongWords pe cycle).low =
        if twoLongWords then memory (addressAt base (cycle.val * 8 + pe.val + 4)) else 0 := by
  cases twoLongWords <;> simp [mbcast, readL1Long]

theorem mbcast_turnaround_words (memory : L1Bank) (values : L1Turnaround)
    (twoLongWords : Bool) (pe cycle : Fin 4) :
    (mbcast memory (.turnaround values) twoLongWords pe cycle).high =
        values cycle ⟨pe.val, by have h := pe.isLt; omega⟩ ∧
      (mbcast memory (.turnaround values) twoLongWords pe cycle).low =
        values cycle ⟨(4 + pe.val) % 64, Nat.mod_lt _ (by decide)⟩ := by
  have hpe : pe.val < 64 := by have h := pe.isLt; omega
  simp [mbcast, readL1Long, Nat.mod_eq_of_lt hpe]

def m4bcastGroup (mab : Fin 16) : Fin 4 :=
  ⟨mab.val / 4, by have h := mab.isLt; omega⟩

theorem m4bcastGroup_matches_rust_index (mab : Fin 16) :
    (m4bcastGroup mab).val = mab.val / 4 := rfl

theorem m4bcast_addressed_words (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) :
    (m4bcast memory (.addressed base) twoLongWords mabGroup pe cycle).high =
        memory (addressAt base
          (if twoLongWords then cycle.val * 32 + mabGroup.val * 8 + pe.val
           else cycle.val * 16 + mabGroup.val * 4 + pe.val)) ∧
      (m4bcast memory (.addressed base) twoLongWords mabGroup pe cycle).low =
        if twoLongWords then memory (addressAt base
          (cycle.val * 32 + mabGroup.val * 8 + pe.val + 4)) else 0 := by
  cases twoLongWords <;> simp [m4bcast, readL1Long, addressAt]

theorem distribSourceMab_euclidean (mab : Fin 16) (mabDiff : Int) :
    (distribSourceMab mab mabDiff).val =
      ((Int.ofNat mab.val - mabDiff) % 16).toNat := rfl

theorem distrib_addressed_words (memory : L1Bank) (base : Fin l1bmLongWords)
    (mabDiff : Int) (mab : Fin 16) (pe cycle : Fin 4) :
    (distrib memory (.addressed base) mabDiff mab pe cycle).high =
      memory (addressAt base
        (cycle.val * 64 + (distribSourceMab mab mabDiff).val * 4 + pe.val)) ∧
    (distrib memory (.addressed base) mabDiff mab pe cycle).low = 0 := by
  simp [distrib, readL1Long]

theorem distribSourceMab_wraps_down (mab : Fin 16) :
    distribSourceMab mab 1 =
      ⟨(mab.val + 15) % 16, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp [distribSourceMab]
  omega

theorem distribSourceMab_wraps_up (mab : Fin 16) :
    distribSourceMab mab (-1) =
      ⟨(mab.val + 1) % 16, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp [distribSourceMab]
  omega

/-- Pending PE-to-L1BM writes are applied in vector order, as in
`Blocks::apply`. -/
abbrev L1Write := Fin l1bmLongWords × BitVec 64

def writeL1Word (memory : L1Bank) (address : Fin l1bmLongWords)
    (value : BitVec 64) : L1Bank :=
  fun target => if target = address then value else memory target

def commitL1Writes (memory : L1Bank) (writes : List L1Write) : L1Bank :=
  writes.foldl (fun current write => writeL1Word current write.1 write.2) memory

theorem writeL1Word_readback (memory : L1Bank) (address : Fin l1bmLongWords)
    (value : BitVec 64) : writeL1Word memory address value address = value := by
  simp [writeL1Word]

theorem commitL1Writes_last_readback (memory : L1Bank) (writesBefore : List L1Write)
    (address : Fin l1bmLongWords) (value : BitVec 64) :
    commitL1Writes memory (writesBefore ++ [(address, value)]) address = value := by
  simp [commitL1Writes, List.foldl_append, writeL1Word]

def mwriteWrites (memoryBase : Fin l1bmLongWords) (twoLongWords : Bool)
    (cycle : Fin 4) (buses : Fin 4 → Bus) : List L1Write :=
  (List.finRange 4).flatMap fun pe =>
    let offset := cycle.val * (if twoLongWords then 8 else 4) + pe.val
    [(addressAt memoryBase offset, (buses pe).high)] ++
      if twoLongWords then
        [(addressAt memoryBase (offset + 4), (buses pe).low)]
      else []

def m4writeWrites (memoryBase : Fin l1bmLongWords) (twoLongWords : Bool)
    (cycle mabGroup : Fin 4) (buses : Fin 4 → Fin 4 → Fin 4 → Bus) : List L1Write :=
  (List.finRange 4).flatMap fun group =>
    (List.finRange 4).flatMap fun pe =>
      let baseOffset := cycle.val * (if twoLongWords then 32 else 16) +
        group.val * (if twoLongWords then 8 else 4) + pe.val
      let source := buses group mabGroup pe
      [(addressAt memoryBase baseOffset, source.high)] ++
        if twoLongWords then
          [(addressAt memoryBase (baseOffset + 4), source.low)]
        else []

theorem mwriteWrites_count (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) (buses : Fin 4 → Bus) :
    (mwriteWrites memoryBase twoLongWords cycle buses).length =
      if twoLongWords then 8 else 4 := by
  cases twoLongWords <;> simp [mwriteWrites, List.finRange]

theorem mwriteWrites_contains_high (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle pe : Fin 4) (buses : Fin 4 → Bus) :
    (addressAt memoryBase
        (cycle.val * (if twoLongWords then 8 else 4) + pe.val), (buses pe).high) ∈
      mwriteWrites memoryBase twoLongWords cycle buses := by
  apply List.mem_flatMap.mpr
  refine ⟨pe, List.mem_finRange pe, ?_⟩
  simp [mwriteWrites]

theorem mwriteWrites_contains_low (memoryBase : Fin l1bmLongWords)
    (cycle pe : Fin 4) (buses : Fin 4 → Bus) :
    (addressAt memoryBase (cycle.val * 8 + pe.val + 4), (buses pe).low) ∈
      mwriteWrites memoryBase true cycle buses := by
  apply List.mem_flatMap.mpr
  refine ⟨pe, List.mem_finRange pe, ?_⟩
  simp [mwriteWrites]

theorem mwriteWrites_twoLongWords_form (memoryBase : Fin l1bmLongWords)
    (cycle : Fin 4) (buses : Fin 4 → Bus) :
    mwriteWrites memoryBase true cycle buses =
      [(addressAt memoryBase (cycle.val * 8), (buses 0).high),
       (addressAt memoryBase (cycle.val * 8 + 4), (buses 0).low),
       (addressAt memoryBase (cycle.val * 8 + (1 : Fin 4).val), (buses 1).high),
       (addressAt memoryBase (cycle.val * 8 + (1 : Fin 4).val + 4), (buses 1).low),
       (addressAt memoryBase (cycle.val * 8 + (2 : Fin 4).val), (buses 2).high),
       (addressAt memoryBase (cycle.val * 8 + (2 : Fin 4).val + 4), (buses 2).low),
       (addressAt memoryBase (cycle.val * 8 + (3 : Fin 4).val), (buses 3).high),
       (addressAt memoryBase (cycle.val * 8 + (3 : Fin 4).val + 4), (buses 3).low)] := by
  simp [mwriteWrites, List.finRange]

theorem committedMwriteCycle_last_low_readback (memory : L1Bank)
    (memoryBase : Fin l1bmLongWords) (cycle : Fin 4) (buses : Fin 4 → Bus) :
    commitL1Writes memory (mwriteWrites memoryBase true cycle buses)
      (addressAt memoryBase (cycle.val * 8 + 7)) = (buses 3).low := by
  rw [mwriteWrites_twoLongWords_form]
  exact commitL1Writes_last_readback memory
    [(addressAt memoryBase (cycle.val * 8), (buses 0).high),
     (addressAt memoryBase (cycle.val * 8 + 4), (buses 0).low),
     (addressAt memoryBase (cycle.val * 8 + 1), (buses 1).high),
     (addressAt memoryBase (cycle.val * 8 + 5), (buses 1).low),
     (addressAt memoryBase (cycle.val * 8 + 2), (buses 2).high),
     (addressAt memoryBase (cycle.val * 8 + 6), (buses 2).low),
     (addressAt memoryBase (cycle.val * 8 + 3), (buses 3).high)]
    (addressAt memoryBase (cycle.val * 8 + 7)) (buses 3).low

theorem m4writeWrites_count (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle mabGroup : Fin 4)
    (buses : Fin 4 → Fin 4 → Fin 4 → Bus) :
    (m4writeWrites memoryBase twoLongWords cycle mabGroup buses).length =
      if twoLongWords then 32 else 16 := by
  cases twoLongWords <;> simp [m4writeWrites, List.length_flatMap, List.finRange]

theorem m4writeWrites_contains_high (memoryBase : Fin l1bmLongWords)
    (cycle mabGroup group pe : Fin 4) (buses : Fin 4 → Fin 4 → Fin 4 → Bus) :
    (addressAt memoryBase
        (cycle.val * 16 + group.val * 4 + pe.val),
      (buses group mabGroup pe).high) ∈
      m4writeWrites memoryBase false cycle mabGroup buses := by
  apply List.mem_flatMap.mpr
  refine ⟨group, List.mem_finRange group, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pe, List.mem_finRange pe, ?_⟩
  simp [m4writeWrites]

theorem m4writeWrites_last (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle mabGroup : Fin 4)
    (buses : Fin 4 → Fin 4 → Fin 4 → Bus) :
    (m4writeWrites memoryBase twoLongWords cycle mabGroup buses).getLast? =
      if twoLongWords then
        some (addressAt memoryBase (cycle.val * 32 + (3 : Fin 4).val * 8 +
          (3 : Fin 4).val + 4), (buses 3 mabGroup 3).low)
      else
        some (addressAt memoryBase (cycle.val * 16 + (3 : Fin 4).val * 4 +
          (3 : Fin 4).val), (buses 3 mabGroup 3).high) := by
  cases twoLongWords <;> simp [m4writeWrites, List.finRange]

theorem committedM4writeCycle_last_readback (memory : L1Bank)
    (memoryBase : Fin l1bmLongWords) (twoLongWords : Bool)
    (cycle mabGroup : Fin 4) (buses : Fin 4 → Fin 4 → Fin 4 → Bus) :
    let lastOffset := if twoLongWords
      then cycle.val * 32 + (3 : Fin 4).val * 8 + (3 : Fin 4).val + 4
      else cycle.val * 16 + (3 : Fin 4).val * 4 + (3 : Fin 4).val
    let lastValue := if twoLongWords then (buses 3 mabGroup 3).low
      else (buses 3 mabGroup 3).high
    commitL1Writes memory (m4writeWrites memoryBase twoLongWords cycle mabGroup buses)
      (addressAt memoryBase lastOffset) = lastValue := by
  cases twoLongWords <;>
    simp [m4writeWrites, commitL1Writes, writeL1Word, List.finRange]

abbrev L1TurnWrite := Fin 64 × BitVec 64

def gatherDestinationMab (mab : Fin 16) (mabDiff : Int) : Fin 16 :=
  distribSourceMab mab (-mabDiff)

def gatherL1Writes (memoryBase : Fin l1bmLongWords) (mabDiff : Int)
    (cycle : Fin 4) (buses : Fin 16 → Fin 4 → Bus) : List L1Write :=
  (List.finRange 16).flatMap fun sourceMab =>
    (List.finRange 4).map fun pe =>
      let targetMab := gatherDestinationMab sourceMab mabDiff
      let offset := cycle.val * 64 + targetMab.val * 4 + pe.val
      (addressAt memoryBase offset, (buses sourceMab pe).high)

def gatherTurnaroundWrites (mabDiff : Int) (buses : Fin 16 → Fin 4 → Bus) :
    List L1TurnWrite :=
  (List.finRange 16).flatMap fun sourceMab =>
    (List.finRange 4).map fun pe =>
      let targetMab := gatherDestinationMab sourceMab mabDiff
      let offset := sourceMab.val * 4 + pe.val
      (⟨offset, by have hm := sourceMab.isLt; have hp := pe.isLt; omega⟩,
        (buses sourceMab pe).high)

theorem gatherDestinationMab_euclidean (mab : Fin 16) (mabDiff : Int) :
    (gatherDestinationMab mab mabDiff).val =
      ((Int.ofNat mab.val + mabDiff) % 16).toNat := by
  simp [gatherDestinationMab, distribSourceMab, Int.sub_eq_add_neg]

theorem gatherL1Writes_count (memoryBase : Fin l1bmLongWords) (mabDiff : Int)
    (cycle : Fin 4) (buses : Fin 16 → Fin 4 → Bus) :
    (gatherL1Writes memoryBase mabDiff cycle buses).length = 64 := by
  simp [gatherL1Writes, List.length_flatMap, List.finRange]

theorem gatherTurnaroundWrites_count (mabDiff : Int)
    (buses : Fin 16 → Fin 4 → Bus) :
    (gatherTurnaroundWrites mabDiff buses).length = 64 := by
  simp [gatherTurnaroundWrites, List.length_flatMap, List.finRange]

theorem gatherL1Writes_contains_source (memoryBase : Fin l1bmLongWords)
    (mabDiff : Int) (cycle : Fin 4) (mab : Fin 16) (pe : Fin 4)
    (buses : Fin 16 → Fin 4 → Bus) :
    (addressAt memoryBase
      (cycle.val * 64 + (gatherDestinationMab mab mabDiff).val * 4 + pe.val),
      (buses mab pe).high) ∈ gatherL1Writes memoryBase mabDiff cycle buses := by
  simp only [gatherL1Writes, List.mem_flatMap, List.mem_map]
  exact ⟨mab, List.mem_finRange mab, pe, List.mem_finRange pe, rfl⟩

theorem gatherTurnaroundWrites_contains_source (mabDiff : Int)
    (mab : Fin 16) (pe : Fin 4) (buses : Fin 16 → Fin 4 → Bus) :
    (⟨mab.val * 4 + pe.val, by have hm := mab.isLt; have hp := pe.isLt; omega⟩,
      (buses mab pe).high) ∈ gatherTurnaroundWrites mabDiff buses := by
  simp only [gatherTurnaroundWrites, List.mem_flatMap, List.mem_map]
  exact ⟨mab, List.mem_finRange mab, pe, List.mem_finRange pe, rfl⟩

def updateBroadcastForwarding (old : ProofsLean.MNCore.Forwarding.Slots)
    (outputs : Fin 4 → Bus) (noForward : Bool) :
    ProofsLean.MNCore.Forwarding.Slots :=
  if noForward then old else fun unit cycle =>
    if unit = .l1ToPE then .known (outputs cycle) else old unit cycle

theorem pbcast_forwarding_readback
    (files : ProofsLean.MNCore.PEMemory.IntegerRegisterFiles)
    (old : ProofsLean.MNCore.Forwarding.Slots)
    (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding files
      (updateBroadcastForwarding old (fun c => pbcast memory base twoLongWords c) false)
      cycle (.forward .lbf false) = .ok (pbcast memory base twoLongWords cycle) := by
  simp [ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding,
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.forwardUnit,
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.applyRounding,
    updateBroadcastForwarding]

end ProofsLean.MNCore.L1Transfer
