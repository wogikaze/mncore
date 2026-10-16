import ProofsLean.Issue

/- MV transfer memory semantics. The Rust executor first collects all writes
from the old memory, then commits them in order. This models that snapshot
behavior independently of the opcode-specific address enumeration. -/
namespace ProofsLean.MNCore.MVSemantics

open ProofsLean.MNCore.Issue

inductive Space where
  | pdm | dram | l2bm
  deriving DecidableEq, Repr

structure Cell where
  space : Space
  group : Fin 4
  bank : Fin 2
  address : Nat
  deriving DecidableEq, Repr

abbrev Memory := Cell → BitVec 64
abbrev CopyPair := Cell × Cell

def updateLastValue (cell : Cell) (found : Option (BitVec 64))
    (entry : Cell × BitVec 64) : Option (BitVec 64) :=
  if entry.1 = cell then some entry.2 else found

/-- The ordered pending writes produced by reading every source from the
pre-instruction memory. -/
def stageCopies (memory : Memory) : List CopyPair → List (Cell × BitVec 64)
  | [] => []
  | (source, destination) :: rest =>
      (destination, memory source) :: stageCopies memory rest

/-- Commit pending writes in Rust's order; if a destination repeats, the last
write wins, just as repeated assignments in the executor do. -/
def commitWrites (memory : Memory) (writes : List (Cell × BitVec 64)) : Memory :=
  fun cell =>
    match writes.foldl (updateLastValue cell) none with
    | some value => value
    | none => memory cell

def executeCopies (memory : Memory) (copies : List CopyPair) : Memory :=
  commitWrites memory (stageCopies memory copies)

def mvGroupFin? (group : Fin 256) : Option (Fin 4) :=
  if h : group.val < 4 then some ⟨group.val, h⟩ else none

def mvBankFin? (bank : Fin 256) : Option (Fin 2) :=
  if h : bank.val < 2 then some ⟨bank.val, h⟩ else none

def mvOperandGroups? (operand : ParsedMvOperand) : Option (List (Fin 4)) :=
  let group := match operand with
    | .pdm _ group | .dram _ group _ | .l2bm _ group _ => group
  match group with
  | none => some (List.finRange 4)
  | some selected => do
      let selected ← mvGroupFin? selected
      pure [selected]

def mvParallelGroupPairs? (source destination : ParsedMvOperand) :
    Option (List (Fin 4 × Fin 4)) := do
  let sourceGroups ← mvOperandGroups? source
  let destinationGroups ← mvOperandGroups? destination
  if sourceGroups.length == destinationGroups.length then
    pure (sourceGroups.zip destinationGroups)
  else none

def mvOperandBank? (operand : ParsedMvOperand) : Option (Fin 2) :=
  match operand with
  | .l2bm _ _ none => some 0
  | .l2bm _ _ (some bank) => mvBankFin? bank
  | _ => some 0

def cellFor (operand : ParsedMvOperand) (group : Fin 4) (bank : Fin 2)
    (offset : Nat) : Cell :=
  match operand with
  | .pdm address _ =>
      ⟨.pdm, group, 0, (address.val + offset) % (2 ^ 19)⟩
  | .dram address _ _ =>
      ⟨.dram, group, 0, (address.val + offset) % (2 ^ 29)⟩
  | .l2bm address _ _ =>
      ⟨.l2bm, group, bank, (address.val + offset) % (2 ^ 15)⟩

/-- Enumerate the byte-for-byte Rust `MvKind::P` loop as source/destination
cell pairs. `count` is the executor's `n * 64` long-word count. -/
def pCopyPlan (source destination : ParsedMvOperand)
    (sourceBank destinationBank : Fin 2)
    (groups : List (Fin 4 × Fin 4)) (count : Nat) : List CopyPair :=
  match groups with
  | [] => []
  | (sourceGroup, destinationGroup) :: rest =>
      ((List.range count).map fun offset =>
        (cellFor source sourceGroup sourceBank offset,
          cellFor destination destinationGroup destinationBank offset)) ++
        pCopyPlan source destination sourceBank destinationBank rest count

def parsedMvPCopyPlan? (transfer : ParsedMv) : Option (List CopyPair) := do
  if transfer.kind != .copy then none else
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      if (match source with | .dram _ _ indirect => indirect | _ => false) ||
          (match destination with | .dram _ _ indirect => indirect | _ => false) then none else
        let sourceBank ← mvOperandBank? source
        let destinationBank ← mvOperandBank? destination
        let groups ← mvParallelGroupPairs? source destination
        let count := (transfer.size.val / 64) * 64
        pure (pCopyPlan source destination sourceBank destinationBank groups count)

theorem pCopyPlan_length (source destination : ParsedMvOperand)
    (sourceBank destinationBank : Fin 2)
    (groups : List (Fin 4 × Fin 4)) (count : Nat) :
    (pCopyPlan source destination sourceBank destinationBank groups count).length =
      groups.length * count := by
  induction groups with
  | nil => simp [pCopyPlan]
  | cons pair rest ih =>
      simp [pCopyPlan, ih, List.length_range]
      rw [Nat.add_one, Nat.succ_mul]
      omega

def executeParsedMvPCopy? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let plan ← parsedMvPCopyPlan? transfer
  pure (executeCopies memory plan)

/-- Source value of the final staged write to a cell, if any. -/
def finalSource (copies : List CopyPair) (cell : Cell) : Option Cell :=
  match copies with
  | [] => none
  | (source, destination) :: rest =>
      match finalSource rest cell with
      | some lastSource => some lastSource
      | none => if destination = cell then some source else none

theorem stageCopies_lastValue (memory : Memory) (copies : List CopyPair)
    (cell : Cell) (seen : Option Cell) :
    (stageCopies memory copies).foldl (updateLastValue cell) (seen.map memory) =
      (match finalSource copies cell with
       | some source => some (memory source)
       | none => seen.map memory) := by
  induction copies generalizing seen with
  | nil => rfl
  | cons copy rest ih =>
      rcases copy with ⟨source, destination⟩
      simp only [stageCopies, List.foldl_cons]
      by_cases h : destination = cell
      · simp [updateLastValue, h]
        have hi := ih (some source)
        simp only [Option.map_some] at hi
        cases hrest : finalSource rest cell <;>
          simpa [finalSource, h, hrest] using hi
      · simp [updateLastValue, h]
        have hi := ih seen
        cases hrest : finalSource rest cell <;>
          simpa [finalSource, h, hrest] using hi

theorem commitWrites_read (memory : Memory) (writes : List (Cell × BitVec 64))
    (cell : Cell) :
    commitWrites memory writes cell =
      match writes.foldl (updateLastValue cell) none with
      | some value => value
      | none => memory cell := rfl

theorem executeCopies_read (memory : Memory) (copies : List CopyPair)
    (cell : Cell) :
    executeCopies memory copies cell =
      match finalSource copies cell with
      | some source => memory source
      | none => memory cell := by
  change (match (stageCopies memory copies).foldl (updateLastValue cell) none with
    | some value => value
    | none => memory cell) = _
  have hstage := stageCopies_lastValue memory copies cell none
  simp only [Option.map_none] at hstage
  rw [hstage]
  cases finalSource copies cell <;> rfl

theorem executeParsedMvPCopy_read (memory : Memory) (transfer : ParsedMv)
    (plan : List CopyPair) (cell : Cell)
    (hplan : parsedMvPCopyPlan? transfer = some plan) :
    (executeParsedMvPCopy? memory transfer).map (fun result => result cell) =
      some (match finalSource plan cell with
        | some source => memory source
        | none => memory cell) := by
  simp [executeParsedMvPCopy?, hplan, executeCopies_read]

/-- An overlapping left-to-right copy reads every source from the old state:
writing cell 1 cannot change the value subsequently copied from cell 1 to cell 2. -/
theorem executeCopies_overlap_uses_snapshot (memory : Memory) (a b c : Cell) :
    executeCopies memory [(a, b), (b, c)] c = memory b := by
  rw [executeCopies_read]
  simp [finalSource]

theorem executeCopies_preserves_unwritten (memory : Memory)
    (copies : List CopyPair) (cell : Cell)
    (h : ∀ pair ∈ copies, pair.2 ≠ cell) :
    executeCopies memory copies cell = memory cell := by
  rw [executeCopies_read]
  induction copies with
  | nil => rfl
  | cons pair rest ih =>
      have hpair : pair.2 ≠ cell := h pair (by simp)
      have hrest : ∀ item ∈ rest, item.2 ≠ cell := by
        intro item hin
        exact h item (by simp [hin])
      cases hlast : finalSource rest cell with
      | none => simp [finalSource, hpair, hlast]
      | some lastSource =>
          have hpreserved := ih hrest
          rw [hlast] at hpreserved
          simpa [finalSource, hpair, hlast] using hpreserved

end ProofsLean.MNCore.MVSemantics
