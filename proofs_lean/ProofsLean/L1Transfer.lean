import ProofsLean.IntegerALU
import ProofsLean.ParsedIntegerStep
import ProofsLean.RRN

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

def mwriteFourCycleWrites (memoryBase : Fin l1bmLongWords) (twoLongWords : Bool)
    (buses : Fin 4 → Fin 4 → Bus) : List L1Write :=
  (List.finRange 4).flatMap fun cycle =>
    mwriteWrites memoryBase twoLongWords cycle (buses cycle)

def m4writeFourCycleWrites (memoryBase : Fin l1bmLongWords) (twoLongWords : Bool)
    (mabGroup : Fin 4) (buses : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bus) :
    List L1Write :=
  (List.finRange 4).flatMap fun cycle =>
    m4writeWrites memoryBase twoLongWords cycle mabGroup (buses cycle)

/-- Address routing for `l1bmr`/`l1bmr4` after the RRN has produced its
per-group, per-PE result words. The RRN arithmetic is deliberately an input
here; this definition captures the distinct output layouts and cycle strides
used by `Blocks::pe_to_l1`. -/
def reduceL1Writes (memoryBase : Fin l1bmLongWords) (fourGroups rounded twoLongWords : Bool)
    (cycle : Fin 4) (results : Fin 4 → Fin 4 → Fin 2 → BitVec 64) : List L1Write :=
  (List.finRange 4).flatMap fun group =>
    (List.finRange 4).flatMap fun pe =>
      if fourGroups || group.val == 0 then
        let stride := if rounded then (if fourGroups then 16 else 4)
          else if fourGroups then (if twoLongWords then 32 else 16)
          else if twoLongWords then 8 else 4
        let offset := if rounded then group.val * 4 + pe.val
          else group.val * (if twoLongWords then 8 else 4) + pe.val
        let first := (addressAt memoryBase (cycle.val * stride + offset),
          results group pe 0)
        if rounded then [first]
        else [first] ++ if twoLongWords then
          [(addressAt memoryBase (cycle.val * stride + offset + 4), results group pe 1)]
        else []
      else []

/-- Compute integer RRN results from the selected MAB inputs and route them
through the same `reduce`/`reduce4` output layout as the Rust block model. -/
def reduceIntegerL1Writes (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.IntegerPrecision)
    (op : RRN.IntegerOp) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) : List L1Write :=
  let results := fun group pe part =>
    RRN.reduceLongInteger op precision <|
      ((List.finRange 16).filter fun mab =>
        !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab
  reduceL1Writes memoryBase fourGroups false twoLongWords cycle results

theorem reduceL1Writes_count (memoryBase : Fin l1bmLongWords)
    (fourGroups rounded twoLongWords : Bool) (cycle : Fin 4)
    (results : Fin 4 → Fin 4 → Fin 2 → BitVec 64) :
    (reduceL1Writes memoryBase fourGroups rounded twoLongWords cycle results).length =
      if fourGroups then (if rounded then 16 else if twoLongWords then 32 else 16)
      else if rounded then 4 else if twoLongWords then 8 else 4 := by
  cases fourGroups <;> cases rounded <;> cases twoLongWords <;>
    simp [reduceL1Writes, List.length_flatMap, List.finRange]

theorem reduceIntegerL1Writes_count (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.IntegerPrecision)
    (op : RRN.IntegerOp) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) :
    (reduceIntegerL1Writes memoryBase fourGroups twoLongWords precision op cycle inputs).length =
      if fourGroups then (if twoLongWords then 32 else 16)
      else if twoLongWords then 8 else 4 := by
  simpa [reduceIntegerL1Writes, Nat.add_assoc] using
    reduceL1Writes_count memoryBase fourGroups false twoLongWords cycle
      (fun group pe part => RRN.reduceLongInteger op precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab))

theorem reduceL1Writes_contains_first (memoryBase : Fin l1bmLongWords)
    (fourGroups rounded twoLongWords : Bool) (cycle group pe : Fin 4)
    (results : Fin 4 → Fin 4 → Fin 2 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if rounded then (if fourGroups then 16 else 4)
        else if fourGroups then (if twoLongWords then 32 else 16)
        else if twoLongWords then 8 else 4) +
        (if rounded then group.val * 4 + pe.val
          else group.val * (if twoLongWords then 8 else 4) + pe.val)),
      results group pe 0) ∈
      reduceL1Writes memoryBase fourGroups rounded twoLongWords cycle results := by
  apply List.mem_flatMap.mpr
  refine ⟨group, List.mem_finRange group, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pe, List.mem_finRange pe, ?_⟩
  have hkeep : (fourGroups || group.val == 0) = true := by
    rcases hgroup with hfour | hzero
    · simp [hfour]
    · simp [hzero]
  cases rounded <;> cases twoLongWords <;> simp [reduceL1Writes, hkeep]

theorem reduceL1Writes_contains_second (memoryBase : Fin l1bmLongWords)
    (fourGroups : Bool) (cycle group pe : Fin 4)
    (results : Fin 4 → Fin 4 → Fin 2 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then 32 else 8) +
        group.val * 8 + pe.val + 4), results group pe 1) ∈
      reduceL1Writes memoryBase fourGroups false true cycle results := by
  apply List.mem_flatMap.mpr
  refine ⟨group, List.mem_finRange group, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pe, List.mem_finRange pe, ?_⟩
  have hkeep : (fourGroups || group.val == 0) = true := by
    rcases hgroup with hfour | hzero
    · simp [hfour]
    · simp [hzero]
  simp [reduceL1Writes, hkeep, Nat.add_assoc]

theorem reduceIntegerL1Writes_contains_result (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.IntegerPrecision)
    (op : RRN.IntegerOp) (cycle group pe : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then (if twoLongWords then 32 else 16)
        else if twoLongWords then 8 else 4) +
        group.val * (if twoLongWords then 8 else 4) + pe.val),
      RRN.reduceLongInteger op precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 0 mab)) ∈
      reduceIntegerL1Writes memoryBase fourGroups twoLongWords precision op cycle inputs := by
  simpa [reduceIntegerL1Writes, Nat.add_assoc] using
    reduceL1Writes_contains_first memoryBase fourGroups false twoLongWords cycle group pe
      (fun g p k => RRN.reduceLongInteger op precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == g.val).map fun mab => inputs g p k mab)) hgroup

/-- Native single/double `l1bmr` and `l1bmr4` results routed to L1BM.
This covers the non-rounded, non-extended Rust path; half aliases and explicit
output rounding have separate layouts. -/
def reduceFloatL1Writes (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.NativeFloatPrecision)
    (cycle : Fin 4) (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) :
    List L1Write :=
  let results := fun group pe part =>
    RRN.reduceLongFloatAdd precision <|
      ((List.finRange 16).filter fun mab =>
        !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab
  reduceL1Writes memoryBase fourGroups false twoLongWords cycle results

theorem reduceFloatL1Writes_count (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.NativeFloatPrecision)
    (cycle : Fin 4) (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) :
    (reduceFloatL1Writes memoryBase fourGroups twoLongWords precision cycle inputs).length =
      if fourGroups then (if twoLongWords then 32 else 16)
      else if twoLongWords then 8 else 4 := by
  simpa [reduceFloatL1Writes, Nat.add_assoc] using
    reduceL1Writes_count memoryBase fourGroups false twoLongWords cycle
      (fun group pe part => RRN.reduceLongFloatAdd precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab))

theorem reduceFloatL1Writes_contains_result (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords : Bool) (precision : RRN.NativeFloatPrecision)
    (cycle group pe : Fin 4) (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then (if twoLongWords then 32 else 16)
        else if twoLongWords then 8 else 4) +
        group.val * (if twoLongWords then 8 else 4) + pe.val),
      RRN.reduceLongFloatAdd precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 0 mab)) ∈
      reduceFloatL1Writes memoryBase fourGroups twoLongWords precision cycle inputs := by
  simpa [reduceFloatL1Writes, Nat.add_assoc] using
    reduceL1Writes_contains_first memoryBase fourGroups false twoLongWords cycle group pe
      (fun g p k => RRN.reduceLongFloatAdd precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == g.val).map fun mab => inputs g p k mab)) hgroup

theorem reduceFloatL1Writes_contains_second_result (memoryBase : Fin l1bmLongWords)
    (fourGroups : Bool) (precision : RRN.NativeFloatPrecision)
    (cycle group pe : Fin 4) (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then 32 else 8) + group.val * 8 + pe.val + 4),
      RRN.reduceLongFloatAdd precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 1 mab)) ∈
      reduceFloatL1Writes memoryBase fourGroups true precision cycle inputs := by
  simpa [reduceFloatL1Writes, Nat.add_assoc] using
    reduceL1Writes_contains_second memoryBase fourGroups cycle group pe
      (fun g p k => RRN.reduceLongFloatAdd precision
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == g.val).map fun mab => inputs g p k mab)) hgroup

/-- The `l1bmrh[f]add` alias path: read the MSB long word, extend its four
half lanes to single, perform the RRN's four-by-four stages where required,
round each lane back to half, and pack four halves into each L1BM word. -/
def reduceHalfAliasL1Writes (memoryBase : Fin l1bmLongWords)
    (fourGroups : Bool) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) : List L1Write :=
  let results := fun group pe _part =>
    RRN.reduceHalfAliasLongWord fourGroups <|
      ((List.finRange 16).filter fun mab =>
        !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 0 mab
  reduceL1Writes memoryBase fourGroups true false cycle results

theorem reduceHalfAliasL1Writes_count (memoryBase : Fin l1bmLongWords)
    (fourGroups : Bool) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) :
    (reduceHalfAliasL1Writes memoryBase fourGroups cycle inputs).length =
      if fourGroups then 16 else 4 := by
  simpa [reduceHalfAliasL1Writes, Nat.add_assoc] using
    reduceL1Writes_count memoryBase fourGroups true false cycle
      (fun group pe _part => RRN.reduceHalfAliasLongWord fourGroups
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 0 mab))

theorem reduceHalfAliasL1Writes_contains_result (memoryBase : Fin l1bmLongWords)
    (fourGroups : Bool) (cycle group pe : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then 16 else 4) + group.val * 4 + pe.val),
      RRN.reduceHalfAliasLongWord fourGroups
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe 0 mab)) ∈
      reduceHalfAliasL1Writes memoryBase fourGroups cycle inputs := by
  simpa [reduceHalfAliasL1Writes, Nat.add_assoc] using
    reduceL1Writes_contains_first memoryBase fourGroups true false cycle group pe
      (fun g p _part => RRN.reduceHalfAliasLongWord fourGroups
        (((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == g.val).map fun mab => inputs g p 0 mab)) hgroup

/-- Explicit half-output rounding for native single/double `reduce` operations.
The destination's two-word mode and the source operand width jointly decide
whether the second source word participates, matching `pe_to_l1`. -/
def reduceRoundedFloatL1Writes (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords sourceTwoWords : Bool)
    (precision : RRN.NativeFloatPrecision) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) : List L1Write :=
  let inputTwoWords := twoLongWords || sourceTwoWords
  let results := fun group pe _part =>
    RRN.reduceRoundedLongFloat fourGroups inputTwoWords precision <|
      ((List.finRange 16).filter fun mab =>
        !fourGroups || mab.val / 4 == group.val).map fun mab =>
          (inputs group pe 0 mab, inputs group pe 1 mab)
  reduceL1Writes memoryBase fourGroups true twoLongWords cycle results

theorem reduceRoundedFloatL1Writes_count (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords sourceTwoWords : Bool)
    (precision : RRN.NativeFloatPrecision) (cycle : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64) :
    (reduceRoundedFloatL1Writes memoryBase fourGroups twoLongWords sourceTwoWords
      precision cycle inputs).length = if fourGroups then 16 else 4 := by
  simpa [reduceRoundedFloatL1Writes] using
    reduceL1Writes_count memoryBase fourGroups true twoLongWords cycle
      (fun group pe _part => RRN.reduceRoundedLongFloat fourGroups
        (twoLongWords || sourceTwoWords) precision <|
        ((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab =>
            (inputs group pe 0 mab, inputs group pe 1 mab))

theorem reduceRoundedFloatL1Writes_contains_result (memoryBase : Fin l1bmLongWords)
    (fourGroups twoLongWords sourceTwoWords : Bool)
    (precision : RRN.NativeFloatPrecision) (cycle group pe : Fin 4)
    (inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64)
    (hgroup : fourGroups = true ∨ group.val = 0) :
    (addressAt memoryBase
      (cycle.val * (if fourGroups then 16 else 4) + group.val * 4 + pe.val),
      RRN.reduceRoundedLongFloat fourGroups (twoLongWords || sourceTwoWords) precision <|
        ((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == group.val).map fun mab =>
            (inputs group pe 0 mab, inputs group pe 1 mab)) ∈
      reduceRoundedFloatL1Writes memoryBase fourGroups twoLongWords sourceTwoWords
        precision cycle inputs := by
  simpa [reduceRoundedFloatL1Writes, Nat.add_assoc] using
    reduceL1Writes_contains_first memoryBase fourGroups true twoLongWords cycle group pe
      (fun g p _part => RRN.reduceRoundedLongFloat fourGroups
        (twoLongWords || sourceTwoWords) precision <|
        ((List.finRange 16).filter fun mab =>
          !fourGroups || mab.val / 4 == g.val).map fun mab =>
            (inputs g p 0 mab, inputs g p 1 mab)) hgroup

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

theorem mwriteFourCycleWrites_count (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (buses : Fin 4 → Fin 4 → Bus) :
    (mwriteFourCycleWrites memoryBase twoLongWords buses).length =
      if twoLongWords then 32 else 16 := by
  cases twoLongWords <;>
    simp [mwriteFourCycleWrites, List.length_flatMap, mwriteWrites_count,
      List.finRange]

theorem m4writeFourCycleWrites_count (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (mabGroup : Fin 4)
    (buses : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bus) :
    (m4writeFourCycleWrites memoryBase twoLongWords mabGroup buses).length =
      if twoLongWords then 128 else 64 := by
  cases twoLongWords <;>
    simp [m4writeFourCycleWrites, List.length_flatMap, m4writeWrites_count,
      List.finRange]

theorem mwriteFourCycleWrites_contains_high (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle pe : Fin 4) (buses : Fin 4 → Fin 4 → Bus) :
    (addressAt memoryBase
        (cycle.val * (if twoLongWords then 8 else 4) + pe.val),
      (buses cycle pe).high) ∈ mwriteFourCycleWrites memoryBase twoLongWords buses := by
  apply List.mem_flatMap.mpr
  refine ⟨cycle, List.mem_finRange cycle, ?_⟩
  exact mwriteWrites_contains_high memoryBase twoLongWords cycle pe (buses cycle)

theorem mwriteFourCycleWrites_contains_low (memoryBase : Fin l1bmLongWords)
    (cycle pe : Fin 4) (buses : Fin 4 → Fin 4 → Bus) :
    (addressAt memoryBase (cycle.val * 8 + pe.val + 4),
      (buses cycle pe).low) ∈ mwriteFourCycleWrites memoryBase true buses := by
  apply List.mem_flatMap.mpr
  refine ⟨cycle, List.mem_finRange cycle, ?_⟩
  exact mwriteWrites_contains_low memoryBase cycle pe (buses cycle)

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

theorem m4writeFourCycleWrites_contains_high (memoryBase : Fin l1bmLongWords)
    (twoLongWords : Bool) (mabGroup cycle group pe : Fin 4)
    (buses : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bus) :
    (addressAt memoryBase
        (cycle.val * (if twoLongWords then 32 else 16) +
          group.val * (if twoLongWords then 8 else 4) + pe.val),
      (buses cycle group mabGroup pe).high) ∈
      m4writeFourCycleWrites memoryBase twoLongWords mabGroup buses := by
  apply List.mem_flatMap.mpr
  refine ⟨cycle, List.mem_finRange cycle, ?_⟩
  cases twoLongWords
  · exact m4writeWrites_contains_high memoryBase cycle mabGroup group pe (buses cycle)
  · apply List.mem_flatMap.mpr
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

def writeL1TurnaroundWord (turnaround : L1Turnaround) (cycle : Fin 4)
    (address : Fin 64) (value : BitVec 64) : L1Turnaround :=
  fun targetCycle targetAddress =>
    if targetCycle = cycle ∧ targetAddress = address then value
    else turnaround targetCycle targetAddress

def commitL1TurnaroundWrites (turnaround : L1Turnaround) (cycle : Fin 4)
    (writes : List L1TurnWrite) : L1Turnaround :=
  writes.foldl (fun current write =>
    writeL1TurnaroundWord current cycle write.1 write.2) turnaround

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

theorem committedGatherL1_last_readback (memory : L1Bank)
    (memoryBase : Fin l1bmLongWords) (mabDiff : Int) (cycle : Fin 4)
    (buses : Fin 16 → Fin 4 → Bus) :
    commitL1Writes memory (gatherL1Writes memoryBase mabDiff cycle buses)
      (addressAt memoryBase
        (cycle.val * 64 + (gatherDestinationMab 15 mabDiff).val * 4 +
          (3 : Fin 4).val)) =
      (buses 15 3).high := by
  simp [commitL1Writes, gatherL1Writes, writeL1Word, List.finRange]

theorem committedGatherTurnaround_last_readback (turnaround : L1Turnaround)
    (mabDiff : Int) (cycle : Fin 4) (buses : Fin 16 → Fin 4 → Bus) :
    commitL1TurnaroundWrites turnaround cycle (gatherTurnaroundWrites mabDiff buses)
      cycle ⟨(15 : Fin 16).val * 4 + (3 : Fin 4).val, by decide⟩ =
      (buses 15 3).high := by
  simp [commitL1TurnaroundWrites, gatherTurnaroundWrites,
    writeL1TurnaroundWord, List.finRange]

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
