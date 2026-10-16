import ProofsLean.Issue
import ProofsLean.RRN

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
abbrev ReductionPair := List Cell × Cell

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

def b2GroupOffsetCopies (source destination : ParsedMvOperand)
    (group : Fin 4) (offset : Nat) : List CopyPair :=
  let sourceCell := cellFor source group 0 offset
  [(sourceCell, cellFor destination group 0 offset),
    (sourceCell, cellFor destination group 1 offset)]

def b2GroupCopiesAux (source destination : ParsedMvOperand)
    (group : Fin 4) : Nat → Nat → List CopyPair
  | _, 0 => []
  | offset, count + 1 =>
      b2GroupOffsetCopies source destination group offset ++
        b2GroupCopiesAux source destination group (offset + 1) count

def b2GroupCopies (source destination : ParsedMvOperand)
    (group : Fin 4) (count : Nat) : List CopyPair :=
  b2GroupCopiesAux source destination group 0 count

/-- Rust `MvKind::B2`: for each group and long-word offset, read bank 0 and
write the same old value to both L2BM banks. Explicit operand selectors are
ignored by this opcode's executor loop. -/
def b2CopyPlan (source destination : ParsedMvOperand) (count : Nat) :
    List CopyPair :=
  (List.finRange 4).flatMap fun group =>
    b2GroupCopies source destination group count

theorem b2GroupCopies_length (source destination : ParsedMvOperand)
    (group : Fin 4) (offset count : Nat) :
    (b2GroupCopiesAux source destination group offset count).length = count * 2 := by
  induction count generalizing offset with
  | zero => simp [b2GroupCopiesAux]
  | succ count ih =>
      simp [b2GroupCopiesAux, b2GroupOffsetCopies, ih, Nat.succ_mul]

theorem b2CopyPlan_length (source destination : ParsedMvOperand) (count : Nat) :
    (b2CopyPlan source destination count).length = 8 * count := by
  simp [b2CopyPlan, b2GroupCopies, b2GroupCopies_length, List.finRange]
  omega

def parsedMvB2Plan? (transfer : ParsedMv) : Option (List CopyPair) := do
  if transfer.kind != .broadcast2 then none else
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      if (match source with | .dram _ _ indirect => indirect | _ => false) ||
          (match destination with | .dram _ _ indirect => indirect | _ => false) then none else
        let count := (transfer.size.val / 64) * 64
        pure (b2CopyPlan source destination count)

def executeParsedMvB2? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let plan ← parsedMvB2Plan? transfer
  pure (executeCopies memory plan)

def bFanoutOffsetCopies (sourceCell : Cell) (destination : ParsedMvOperand)
    (destinationOffset : Nat) : List CopyPair :=
  (List.finRange 4).flatMap fun group =>
    (List.finRange 2).map fun bank =>
      (sourceCell, cellFor destination group bank destinationOffset)

def bBroadcastCopiesAux (sourceAt : Nat → Cell) (destination : ParsedMvOperand)
    (destinationOffsetAt : Nat → Nat) : Nat → Nat → List CopyPair
  | _, 0 => []
  | position, count + 1 =>
      bFanoutOffsetCopies (sourceAt position) destination
          (destinationOffsetAt position) ++
        bBroadcastCopiesAux sourceAt destination destinationOffsetAt
          (position + 1) count

def bBroadcastCopies (sourceAt : Nat → Cell) (destination : ParsedMvOperand)
    (destinationOffsetAt : Nat → Nat) (count : Nat) : List CopyPair :=
  bBroadcastCopiesAux sourceAt destination destinationOffsetAt 0 count

theorem bFanoutOffsetCopies_length (sourceCell : Cell)
    (destination : ParsedMvOperand) (offset : Nat) :
    (bFanoutOffsetCopies sourceCell destination offset).length = 8 := by
  simp [bFanoutOffsetCopies, List.finRange]

theorem bBroadcastCopiesAux_length (sourceAt : Nat → Cell)
    (destination : ParsedMvOperand) (destinationOffsetAt : Nat → Nat)
    (position count : Nat) :
    (bBroadcastCopiesAux sourceAt destination destinationOffsetAt position count).length =
      count * 8 := by
  induction count generalizing position with
  | zero => simp [bBroadcastCopiesAux]
  | succ count ih =>
      simp [bBroadcastCopiesAux, bFanoutOffsetCopies_length, ih, Nat.succ_mul]
      omega

theorem bBroadcastCopies_length (sourceAt : Nat → Cell)
    (destination : ParsedMvOperand) (destinationOffsetAt : Nat → Nat)
    (count : Nat) :
    (bBroadcastCopies sourceAt destination destinationOffsetAt count).length =
      count * 8 := by
  exact bBroadcastCopiesAux_length sourceAt destination destinationOffsetAt 0 count

def bPdmCopyPlan (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) : List CopyPair :=
  bBroadcastCopies (fun offset => cellFor source sourceGroup 0 offset)
    destination id count

def bDramSourceGroup (position : Nat) : Fin 4 :=
  ⟨(position % 64) / 16, by
    have hmod : position % 64 < 64 := Nat.mod_lt _ (by decide)
    omega⟩

def bDramSourceOffset (position : Nat) : Nat :=
  16 * (position / 64) + position % 16

theorem bDramSourceCoordinate_flatten (block : Nat) (group : Fin 4)
    (word : Fin 16) :
    bDramSourceGroup (64 * block + 16 * group.val + word.val) = group ∧
    bDramSourceOffset (64 * block + 16 * group.val + word.val) =
      16 * block + word.val := by
  have hgroup := group.isLt
  have hword := word.isLt
  constructor
  · apply Fin.ext
    simp only [bDramSourceGroup]
    omega
  · simp only [bDramSourceOffset]
    omega

def bDramCopyPlan (source destination : ParsedMvOperand)
    (count : Nat) : List CopyPair :=
  bBroadcastCopies
    (fun position => cellFor source (bDramSourceGroup position) 0
      (bDramSourceOffset position)) destination id count

theorem bPdmCopyPlan_length (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) :
    (bPdmCopyPlan source destination sourceGroup count).length = count * 8 := by
  exact bBroadcastCopies_length _ _ _ _

theorem bDramCopyPlan_length (source destination : ParsedMvOperand)
    (count : Nat) :
    (bDramCopyPlan source destination count).length = count * 8 := by
  exact bBroadcastCopies_length _ _ _ _

def indexedCopiesAux (sourceAt destinationAt : Nat → Cell) : Nat → Nat → List CopyPair
  | _, 0 => []
  | position, count + 1 =>
      (sourceAt position, destinationAt position) ::
        indexedCopiesAux sourceAt destinationAt (position + 1) count

def indexedCopies (sourceAt destinationAt : Nat → Cell) (count : Nat) : List CopyPair :=
  indexedCopiesAux sourceAt destinationAt 0 count

theorem indexedCopiesAux_length (sourceAt destinationAt : Nat → Cell)
    (position count : Nat) :
    (indexedCopiesAux sourceAt destinationAt position count).length = count := by
  induction count generalizing position with
  | zero => simp [indexedCopiesAux]
  | succ count ih => simp [indexedCopiesAux, ih]

theorem indexedCopies_length (sourceAt destinationAt : Nat → Cell) (count : Nat) :
    (indexedCopies sourceAt destinationAt count).length = count := by
  exact indexedCopiesAux_length sourceAt destinationAt 0 count

def dPdmDramCopyPlan (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) : List CopyPair :=
  indexedCopies
    (fun position => cellFor source sourceGroup 0 position)
    (fun position => cellFor destination (bDramSourceGroup position) 0
      (bDramSourceOffset position)) count

def dDramPdmCopyPlan (source destination : ParsedMvOperand)
    (destinationGroup : Fin 4) (count : Nat) : List CopyPair :=
  indexedCopies
    (fun position => cellFor source (bDramSourceGroup position) 0
      (bDramSourceOffset position))
    (fun position => cellFor destination destinationGroup 0 position) count

theorem dPdmDramCopyPlan_length (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) :
    (dPdmDramCopyPlan source destination sourceGroup count).length = count := by
  exact indexedCopies_length _ _ _

theorem dDramPdmCopyPlan_length (source destination : ParsedMvOperand)
    (destinationGroup : Fin 4) (count : Nat) :
    (dDramPdmCopyPlan source destination destinationGroup count).length = count := by
  exact indexedCopies_length _ _ _

theorem dPdmDramCoordinates_flatten (block : Nat) (group : Fin 4)
    (word : Fin 16) :
    bDramSourceGroup (64 * block + 16 * group.val + word.val) = group ∧
    bDramSourceOffset (64 * block + 16 * group.val + word.val) =
      16 * block + word.val := by
  exact bDramSourceCoordinate_flatten block group word

def dL2bmPositionGroup (position : Nat) : Fin 4 :=
  ⟨(position % 128) / 32, by
    have hmod : position % 128 < 128 := Nat.mod_lt _ (by decide)
    omega⟩

def dL2bmPositionBank (position : Nat) : Fin 2 :=
  ⟨(position % 32) / 16, by
    have hmod : position % 32 < 32 := Nat.mod_lt _ (by decide)
    omega⟩

def dL2bmPositionJ (position : Nat) : Nat := (position % 512) / 128

def dL2bmPositionWord (position : Nat) : Nat := position % 16

def dPdmL2bmSourceOffset (position : Nat) : Nat :=
  512 * (position / 512) +
    (dL2bmPositionJ position * 8 + (dL2bmPositionGroup position).val * 2 +
      (dL2bmPositionBank position).val) * 16 + dL2bmPositionWord position

def dL2bmPdmDestinationOffset (position : Nat) : Nat :=
  512 * (position / 512) +
    (dL2bmPositionJ position * 8 + (dL2bmPositionGroup position).val * 2 +
      (dL2bmPositionBank position).val) * 16 + dL2bmPositionWord position

def dL2bmDestinationOffset (position : Nat) : Nat :=
  64 * (position / 512) + dL2bmPositionJ position * 16 +
    dL2bmPositionWord position

theorem dL2bmCoordinates_flatten (block : Nat) (j : Fin 4) (group : Fin 4)
    (bank : Fin 2) (word : Fin 16) :
    dL2bmPositionJ (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) = j.val ∧
    dL2bmPositionGroup (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) = group ∧
    dL2bmPositionBank (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) = bank ∧
    dL2bmPositionWord (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) = word.val ∧
    dPdmL2bmSourceOffset (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) =
      512 * block + (j.val * 8 + group.val * 2 + bank.val) * 16 + word.val ∧
    dL2bmDestinationOffset (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) = 64 * block + j.val * 16 + word.val := by
  have hj := j.isLt
  have hg := group.isLt
  have hb := bank.isLt
  have hw := word.isLt
  have htail : 128 * j.val + 32 * group.val + 16 * bank.val + word.val < 512 := by omega
  have hmod512 :
      (512 * block + (128 * j.val + 32 * group.val + 16 * bank.val + word.val)) % 512 =
        128 * j.val + 32 * group.val + 16 * bank.val + word.val := by omega
  have hposmod512 :
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) % 512 =
        128 * j.val + 32 * group.val + 16 * bank.val + word.val := by omega
  have hdiv512 :
      (512 * block + (128 * j.val + 32 * group.val + 16 * bank.val + word.val)) / 512 =
        block := by omega
  have hposdiv512 :
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) / 512 =
        block := by omega
  have hmod128 :
      (128 * j.val + 32 * group.val + 16 * bank.val + word.val) % 128 =
        32 * group.val + 16 * bank.val + word.val := by omega
  have hposmod128 :
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) % 128 =
        32 * group.val + 16 * bank.val + word.val := by omega
  have hmod32 :
      (32 * group.val + 16 * bank.val + word.val) % 32 =
        16 * bank.val + word.val := by omega
  have hposmod32 :
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) % 32 =
        16 * bank.val + word.val := by omega
  have hmod16 : (16 * bank.val + word.val) % 16 = word.val := by omega
  have hposmod16 :
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) % 16 =
        word.val := by omega
  have hjdiv :
      (128 * j.val + 32 * group.val + 16 * bank.val + word.val) / 128 = j.val := by
    have htail128 : 32 * group.val + 16 * bank.val + word.val < 128 := by omega
    omega
  have hgdiv : (32 * group.val + 16 * bank.val + word.val) / 32 = group.val := by
    have htail32 : 16 * bank.val + word.val < 32 := by omega
    omega
  have hbdiv : (16 * bank.val + word.val) / 16 = bank.val := by omega
  have hJ : dL2bmPositionJ
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) = j.val := by
    change ((512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) % 512) / 128 = j.val
    rw [hposmod512]
    exact hjdiv
  have hG : dL2bmPositionGroup
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) = group := by
    apply Fin.ext
    change ((512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) % 128) / 32 = group.val
    rw [hposmod128]
    exact hgdiv
  have hC : dL2bmPositionBank
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) = bank := by
    apply Fin.ext
    change ((512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) % 32) / 16 = bank.val
    rw [hposmod32]
    exact hbdiv
  have hK : dL2bmPositionWord
      (512 * block + 128 * j.val + 32 * group.val + 16 * bank.val + word.val) = word.val := by
    change (512 * block + 128 * j.val + 32 * group.val +
      16 * bank.val + word.val) % 16 = word.val
    rw [hposmod16]
  constructor
  · exact hJ
  constructor
  · exact hG
  constructor
  · exact hC
  constructor
  · exact hK
  constructor
  · simp [dPdmL2bmSourceOffset, hposdiv512, hJ, hG, hC, hK]
  · simp [dL2bmDestinationOffset, hposdiv512, hJ, hK]

def dPdmL2bmCopyPlan (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) : List CopyPair :=
  indexedCopies
    (fun position => cellFor source sourceGroup 0 (dPdmL2bmSourceOffset position))
    (fun position => cellFor destination (dL2bmPositionGroup position)
      (dL2bmPositionBank position) (dL2bmDestinationOffset position)) count

def dL2bmPdmCopyPlan (source destination : ParsedMvOperand)
    (destinationGroup : Fin 4) (count : Nat) : List CopyPair :=
  indexedCopies
    (fun position => cellFor source (dL2bmPositionGroup position)
      (dL2bmPositionBank position) (dL2bmDestinationOffset position))
    (fun position => cellFor destination destinationGroup 0
      (dL2bmPdmDestinationOffset position)) count

theorem dPdmL2bmCopyPlan_length (source destination : ParsedMvOperand)
    (sourceGroup : Fin 4) (count : Nat) :
    (dPdmL2bmCopyPlan source destination sourceGroup count).length = count := by
  exact indexedCopies_length _ _ _

theorem dL2bmPdmCopyPlan_length (source destination : ParsedMvOperand)
    (destinationGroup : Fin 4) (count : Nat) :
    (dL2bmPdmCopyPlan source destination destinationGroup count).length = count := by
  exact indexedCopies_length _ _ _

def r2GroupReductions (source destination : ParsedMvOperand)
    (group : Fin 4) (count : Nat) : List ReductionPair :=
  (List.range count).map fun offset =>
    ([cellFor source group 0 offset, cellFor source group 1 offset],
      cellFor destination group 0 offset)

def r2Plan (source destination : ParsedMvOperand)
    (groups : List (Fin 4)) (count : Nat) : List ReductionPair :=
  match groups with
  | [] => []
  | group :: rest => r2GroupReductions source destination group count ++
      r2Plan source destination rest count

theorem r2GroupReductions_length (source destination : ParsedMvOperand)
    (group : Fin 4) (count : Nat) :
    (r2GroupReductions source destination group count).length = count := by
  simp [r2GroupReductions, List.length_map, List.length_range]

theorem r2Plan_length (source destination : ParsedMvOperand)
    (groups : List (Fin 4)) (count : Nat) :
    (r2Plan source destination groups count).length = groups.length * count := by
  induction groups with
  | nil => simp [r2Plan]
  | cons group rest ih =>
      simp [r2Plan, r2GroupReductions_length, ih]
      rw [Nat.add_mul, Nat.one_mul]
      omega

def mvFirstOperandGroup? (operand : ParsedMvOperand) : Option (Fin 4) := do
  let groups ← mvOperandGroups? operand
  groups.head?

def parsedMvDPlan? (transfer : ParsedMv) : Option (List CopyPair) := do
  if transfer.kind != .distribute then none else
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      if (match source with | .dram _ _ indirect => indirect | _ => false) ||
          (match destination with | .dram _ _ indirect => indirect | _ => false) then none else
      let count := (transfer.size.val / 64) * 64
      match source, destination with
      | .pdm _ _, .dram _ _ false => do
          let sourceGroup ← mvFirstOperandGroup? source
          pure (dPdmDramCopyPlan source destination sourceGroup count)
      | .dram _ _ false, .pdm _ _ => do
          let destinationGroup ← mvFirstOperandGroup? destination
          pure (dDramPdmCopyPlan source destination destinationGroup count)
      | .pdm _ _, .l2bm _ _ _ => do
          let sourceGroup ← mvFirstOperandGroup? source
          pure (dPdmL2bmCopyPlan source destination sourceGroup
            ((transfer.size.val / 64) * 512))
      | .l2bm _ _ _, .pdm _ _ => do
          let destinationGroup ← mvFirstOperandGroup? destination
          pure (dL2bmPdmCopyPlan source destination destinationGroup
            ((transfer.size.val / 64) * 512))
      | _, _ => none

def executeParsedMvD? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let plan ← parsedMvDPlan? transfer
  pure (executeCopies memory plan)

def parsedMvR2Plan? (transfer : ParsedMv) : Option (List ReductionPair) := do
  match transfer.kind with
  | .reduce2 _ => pure ()
  | _ => none
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      let groups ← mvOperandGroups? destination
      let count := (transfer.size.val / 64) * 64
      pure (r2Plan source destination groups count)

def parsedMvReducer? (rrn : ParsedRrn) :
    Option (List (BitVec 64) → BitVec 64) :=
  match rrn.precision, rrn.op with
  | 'd', .fadd => some (RRN.reduceLongFloatAddFormat .double)
  | 'f', .fadd => some (RRN.reduceLongFloatAddFormat .single)
  | 'h', .fadd => some (RRN.reduceLongFloatAddFormat .half)
  | 'd', .max => some (RRN.reduceLongInteger .maximum .long)
  | 'f', .max => some (RRN.reduceLongInteger .maximum .word)
  | 'h', .max => some (RRN.reduceLongInteger .maximum .half)
  | 'd', .min => some (RRN.reduceLongInteger .minimum .long)
  | 'f', .min => some (RRN.reduceLongInteger .minimum .word)
  | 'h', .min => some (RRN.reduceLongInteger .minimum .half)
  | 'l', .iadd => some (RRN.reduceLongInteger .add .long)
  | 'i', .iadd => some (RRN.reduceLongInteger .add .word)
  | 's', .iadd => some (RRN.reduceLongInteger .add .half)
  | 'l', .band => some (RRN.reduceLongInteger .bitAnd .long)
  | 'i', .band => some (RRN.reduceLongInteger .bitAnd .word)
  | 's', .band => some (RRN.reduceLongInteger .bitAnd .half)
  | 'l', .and => some (RRN.reduceLongInteger .allNonzero .long)
  | 'i', .and => some (RRN.reduceLongInteger .allNonzero .word)
  | 's', .and => some (RRN.reduceLongInteger .allNonzero .half)
  | 'l', .bor => some (RRN.reduceLongInteger .bitOr .long)
  | 'i', .bor => some (RRN.reduceLongInteger .bitOr .word)
  | 's', .bor => some (RRN.reduceLongInteger .bitOr .half)
  | 'l', .or => some (RRN.reduceLongInteger .anyNonzero .long)
  | 'i', .or => some (RRN.reduceLongInteger .anyNonzero .word)
  | 's', .or => some (RRN.reduceLongInteger .anyNonzero .half)
  | _, _ => none

def stageReductions (memory : Memory) (reduce : List (BitVec 64) → BitVec 64)
    : List ReductionPair → List (Cell × BitVec 64)
  | [] => []
  | (sources, destination) :: rest =>
      (destination, reduce (sources.map memory)) :: stageReductions memory reduce rest

def executeReductions (memory : Memory) (reduce : List (BitVec 64) → BitVec 64)
    (reductions : List ReductionPair) : Memory :=
  commitWrites memory (stageReductions memory reduce reductions)

def executeParsedMvR2? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let .reduce2 rrn := transfer.kind | none
  let reduce ← parsedMvReducer? rrn
  let plan ← parsedMvR2Plan? transfer
  pure (executeReductions memory reduce plan)

def parsedMvBPlan? (transfer : ParsedMv) : Option (List CopyPair) := do
  if transfer.kind != .broadcast then none else
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      if (match source with | .dram _ _ indirect => indirect | _ => false) ||
          (match destination with | .dram _ _ indirect => indirect | _ => false) then none else
      let count := (transfer.size.val / 64) * 64
      match source with
      | .pdm _ _ =>
          let sourceGroup ← mvFirstOperandGroup? source
          pure (bPdmCopyPlan source destination sourceGroup count)
      | .dram _ _ false => pure (bDramCopyPlan source destination count)
      | .dram _ _ true => none
      | .l2bm _ _ _ => none

def executeParsedMvB? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let plan ← parsedMvBPlan? transfer
  pure (executeCopies memory plan)

def b4FanoutOffsetCopies (sourceCell : Cell) (destination : ParsedMvOperand)
    (bank : Fin 2) (destinationOffset : Nat) : List CopyPair :=
  (List.finRange 4).map fun group =>
    (sourceCell, cellFor destination group bank destinationOffset)

def b4ScatterCopiesAux (sourceAt : Nat → Cell) (destination : ParsedMvOperand)
    (bankAt : Nat → Fin 2) (destinationOffsetAt : Nat → Nat) : Nat → Nat → List CopyPair
  | _, 0 => []
  | position, count + 1 =>
      b4FanoutOffsetCopies (sourceAt position) destination
          (bankAt position) (destinationOffsetAt position) ++
        b4ScatterCopiesAux sourceAt destination bankAt destinationOffsetAt
          (position + 1) count

def b4ScatterCopies (sourceAt : Nat → Cell) (destination : ParsedMvOperand)
    (bankAt : Nat → Fin 2) (destinationOffsetAt : Nat → Nat)
    (count : Nat) : List CopyPair :=
  b4ScatterCopiesAux sourceAt destination bankAt destinationOffsetAt 0 count

theorem b4FanoutOffsetCopies_length (sourceCell : Cell)
    (destination : ParsedMvOperand) (bank : Fin 2) (offset : Nat) :
    (b4FanoutOffsetCopies sourceCell destination bank offset).length = 4 := by
  simp [b4FanoutOffsetCopies, List.finRange]

theorem b4ScatterCopiesAux_length (sourceAt : Nat → Cell)
    (destination : ParsedMvOperand) (bankAt : Nat → Fin 2)
    (destinationOffsetAt : Nat → Nat)
    (position count : Nat) :
    (b4ScatterCopiesAux sourceAt destination bankAt destinationOffsetAt position count).length =
      count * 4 := by
  induction count generalizing position with
  | zero => simp [b4ScatterCopiesAux]
  | succ count ih =>
      simp [b4ScatterCopiesAux, b4FanoutOffsetCopies_length, ih, Nat.succ_mul]
      omega

theorem b4ScatterCopies_length (sourceAt : Nat → Cell)
    (destination : ParsedMvOperand) (bankAt : Nat → Fin 2)
    (destinationOffsetAt : Nat → Nat)
    (count : Nat) :
    (b4ScatterCopies sourceAt destination bankAt destinationOffsetAt count).length =
      count * 4 := by
  exact b4ScatterCopiesAux_length sourceAt destination bankAt destinationOffsetAt 0 count

def b4DestinationBank (position : Nat) : Fin 2 :=
  ⟨(position % 128) / 64, by
    have hmod : position % 128 < 128 := Nat.mod_lt _ (by decide)
    omega⟩

def b4SourceGroup (position : Nat) : Fin 4 :=
  ⟨(position % 64) / 16, by
    have hmod : position % 64 < 64 := Nat.mod_lt _ (by decide)
    omega⟩

def b4SourceOffset (position : Nat) : Nat :=
  32 * (position / 128) + 16 * (b4DestinationBank position).val + position % 16

def b4DestinationOffset (position : Nat) : Nat :=
  64 * (position / 128) + 16 * (b4SourceGroup position).val + position % 16

def b4DramCopyPlan (source destination : ParsedMvOperand) (count : Nat) :
    List CopyPair :=
  b4ScatterCopies
    (fun position => cellFor source (b4SourceGroup position)
      (b4DestinationBank position) (b4SourceOffset position))
    destination b4DestinationBank b4DestinationOffset count

theorem b4DramCoordinates_flatten (block : Nat) (bank : Fin 2)
    (group : Fin 4) (word : Fin 16) :
    b4DestinationBank (128 * block + 64 * bank.val + 16 * group.val + word.val) = bank ∧
    b4SourceGroup (128 * block + 64 * bank.val + 16 * group.val + word.val) = group ∧
    b4SourceOffset (128 * block + 64 * bank.val + 16 * group.val + word.val) =
      32 * block + 16 * bank.val + word.val ∧
    b4DestinationOffset (128 * block + 64 * bank.val + 16 * group.val + word.val) =
      64 * block + 16 * group.val + word.val := by
  have hbank := bank.isLt
  have hgroup := group.isLt
  have hword := word.isLt
  constructor
  · apply Fin.ext
    simp only [b4DestinationBank]
    omega
  constructor
  · apply Fin.ext
    simp only [b4SourceGroup]
    omega
  constructor
  · simp only [b4SourceOffset, b4DestinationBank]
    omega
  · simp only [b4DestinationOffset, b4SourceGroup]
    omega

theorem b4DramCopyPlan_length (source destination : ParsedMvOperand) (count : Nat) :
    (b4DramCopyPlan source destination count).length = count * 4 := by
  exact b4ScatterCopies_length _ _ _ _ _

theorem b4MvWriteCount (size : Fin (2 ^ 64)) :
    ((size.val / 64) * 128) * 4 = (size.val / 64) * 512 := by
  omega

def parsedMvB4Plan? (transfer : ParsedMv) : Option (List CopyPair) := do
  if transfer.kind != .broadcast4 then none else
  match transfer.source, transfer.destination with
  | none, _ | _, none => pure []
  | some source, some destination => do
      if (match source with | .dram _ _ indirect => indirect | _ => true) ||
          (match destination with | .dram _ _ indirect => indirect | _ => false) then none else
      let count := (transfer.size.val / 64) * 128
      pure (b4DramCopyPlan source destination count)

def executeParsedMvB4? (memory : Memory) (transfer : ParsedMv) : Option Memory := do
  let plan ← parsedMvB4Plan? transfer
  pure (executeCopies memory plan)

theorem b2GroupOffsetCopies_ignores_operand_selectors
    (source destination : Fin (2 ^ 64)) (sourceGroup destinationGroup : Fin 256)
    (sourceBank destinationBank : Fin 256) (group : Fin 4) (offset : Nat) :
    b2GroupOffsetCopies
      (.l2bm source (some sourceGroup) (some sourceBank))
      (.l2bm destination (some destinationGroup) (some destinationBank)) group offset =
    b2GroupOffsetCopies
      (.l2bm source none none) (.l2bm destination none none) group offset := rfl

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

theorem executeParsedMvB2_read (memory : Memory) (transfer : ParsedMv)
    (plan : List CopyPair) (cell : Cell)
    (hplan : parsedMvB2Plan? transfer = some plan) :
    (executeParsedMvB2? memory transfer).map (fun result => result cell) =
      some (match finalSource plan cell with
        | some source => memory source
        | none => memory cell) := by
  simp [executeParsedMvB2?, hplan, executeCopies_read]

theorem executeParsedMvB_read (memory : Memory) (transfer : ParsedMv)
    (plan : List CopyPair) (cell : Cell)
    (hplan : parsedMvBPlan? transfer = some plan) :
    (executeParsedMvB? memory transfer).map (fun result => result cell) =
      some (match finalSource plan cell with
        | some source => memory source
        | none => memory cell) := by
  simp [executeParsedMvB?, hplan, executeCopies_read]

theorem executeParsedMvB4_read (memory : Memory) (transfer : ParsedMv)
    (plan : List CopyPair) (cell : Cell)
    (hplan : parsedMvB4Plan? transfer = some plan) :
    (executeParsedMvB4? memory transfer).map (fun result => result cell) =
      some (match finalSource plan cell with
        | some source => memory source
        | none => memory cell) := by
  simp [executeParsedMvB4?, hplan, executeCopies_read]

theorem executeParsedMvD_read (memory : Memory) (transfer : ParsedMv)
    (plan : List CopyPair) (cell : Cell)
    (hplan : parsedMvDPlan? transfer = some plan) :
    (executeParsedMvD? memory transfer).map (fun result => result cell) =
      some (match finalSource plan cell with
        | some source => memory source
        | none => memory cell) := by
  simp [executeParsedMvD?, hplan, executeCopies_read]

theorem executeReductions_read (memory : Memory)
    (reduce : List (BitVec 64) → BitVec 64)
    (reductions : List ReductionPair) (cell : Cell) :
    executeReductions memory reduce reductions cell =
      match (stageReductions memory reduce reductions).foldl
          (updateLastValue cell) none with
      | some value => value
      | none => memory cell := rfl

theorem executeParsedMvR2_read (memory : Memory) (transfer : ParsedMv)
    (plan : List ReductionPair) (cell : Cell)
    (hplan : parsedMvR2Plan? transfer = some plan) :
    (executeParsedMvR2? memory transfer).map (fun result => result cell) =
      match transfer.kind with
      | .reduce2 rrn => (parsedMvReducer? rrn).map fun reduce =>
          executeReductions memory reduce plan cell
      | _ => none := by
  cases hk : transfer.kind with
  | reduce2 rrn =>
      cases hreduce : parsedMvReducer? rrn <;>
        simp [executeParsedMvR2?, hplan, hk, hreduce]
  | nop | copy | broadcast | broadcast2 | broadcast4 | distribute | reduce _ | reduce4 _ =>
      simp [executeParsedMvR2?, hk]

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
