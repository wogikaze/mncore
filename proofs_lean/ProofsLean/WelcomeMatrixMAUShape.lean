import ProofsLean.WelcomeMatrixMAUCommit
import ProofsLean.WelcomeHalfMAUCopy

/-! # The matrix-MAU row shape at the all-zero state

`WelcomeMatrixMAUCommit.lean` proves that the matrix-MAU/write stage *commits*
a prepared write list on the PE 0 register file it was given
(`executeParsedMatrixMAUProducer_commit`, `executeParsedMatrixMAUAndWrites_commit`).
This module proves the **shape** of the part of that list that reaches PE 0 at
the all-zero initial state, in the form consumed by the line-level assembly of
`WelcomeMAUShape.lean`: the `.lm1` part is either a set of copied `.double`
blocks (`Lm1WritesDoubleCopy`) or fits in four narrow windows
(`Lm1WritesNarrow`).

## The structure of the matrix-MAU row

A matrix-MAU row is `executeParsedMatrixMAUAtMABs` over `allMABCoordinates`.
Each coordinate's transition commits four PE register files
(`commitParsedMatrixMAUPEState`), and only the coordinate `⟨0,0,0,0⟩` has
`physicalPEId coordinate 0 = welcomePE = 0` (`physicalPEId_welcomePE_eq`).  So
the whole walk contributes exactly one coordinate's write list to PE 0, and that
coordinate's list is produced by the four cycles of
`executeParsedMatrixMAUWriteCycles`, each of which runs the destination loop
`writeParsedMatrixMAUDestinationsAtPE` at PE 0.

## What is proved

* **Destination layer (unconditional).**  The matrix-MAU destination loop is a
  commit shaped by the row's static `.lm1` destination width: every `.lm1` write
  of the list is `w`-wide and, when `w = .double`, 4-aligned; and at most
  `(destinations.filter isLm1MemoryDestination).length` of them are emitted
  (`writeParsedMatrixMAUDestinationsAtPE_widthCount`).

* **Loop layer (unconditional).**  The per-cycle four-PE loop, the four-cycle
  loop, the per-coordinate write list, the transition, the walk over the MAB and
  the producer carry that bound.  At the target PE only the target's own visit
  contributes (`executeParsedMatrixMAUPEWritesAtCycle_widthCount`), so a cycle
  contributes at most the row's `.lm1` destination count and the four cycles of
  one coordinate contribute at most four `.lm1` writes.

* **Narrow half (unconditional).**  `executeParsedMatrixMAUProducer_zeroNarrow`:
  when the row's static `.lm1` width is not `.double`, the PE 0 write list of a
  successful matrix-MAU row at the all-zero state fits in four narrow windows —
  with no datapath hypothesis at all.

* **Copy half (conditional on one named datapath statement).**  The third data
  word of a `.double` write is the high word of the low half of the flushed
  output bus, and a flush preserves a copy
  (`parsedOutputAfterFlush_word_two_isWelcomeCopy`).  The copy-fact chain
  (`writeParsedMatrixMAUDestinationsAtPE_shape` through
  `executeParsedMatrixMAUProducer_shape`) therefore proves that the PE 0 write
  list carries both the static width facts and the copy facts as soon as every
  bus of `executeParsedMatrixMAUAtMAB` at the all-zero state has a zero low
  half.  That statement is isolated as `WelcomePEMatrixMAUZeroBus`, and
  `executeParsedMatrixMAUProducer_zeroShape_of_zeroBus` (and its `_static`
  form) derives `Lm1WritesDoubleCopy ∨ Lm1WritesNarrow` from it.

* **The datapath layer (partially proved).**  §10 proves the zero-store layer
  (`parsedMatrixMAUProductRow_zero_store`, `matrixBlockFloatDot_zero_left`),
  the lane layer (`parsedMatrixMAUDecodeLanes_zero`) and the read layer
  (`readParsedMatrixMAUSourceAtMAB_zero`: at the all-zero state a successful
  source read returns `4 * count` lanes, each either `0` or the sign mask, so
  each decodes to a zero `MAUValue`).  §10.3 states exactly what is left for
  `WelcomePEMatrixMAUZeroBus`: the row computation
  `parsedMatrixMAUCalculateRows_zero_store` (zero store + zero accumulator ⇒
  zero rows) and the packing step that turns zero rows into a bus with a zero
  low half.

* **The whole stage (§12).**  The write half of the stage preserves every PE
  register file, so the same two statements hold for
  `executeParsedMatrixMAUAndWrites` (`executeParsedMatrixMAUAndWrites_zeroNarrow_static`,
  `executeParsedMatrixMAUAndWrites_zeroShape_static_of_zeroBus`).

## Remainder

The single remaining statement is `WelcomePEMatrixMAUZeroBus`: every bus of
`executeParsedMatrixMAUAtMAB` at the all-zero state has a zero low half.  §10
proves its zero-store, lane and read layers; §10.3 records the exact row
computation and packing facts still to prove and why the `do` block of
`parsedMatrixMAUCalculateRows?` needs a `cases precision` restatement.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Arithmetic helpers for the write-count bounds -/

/-- **The sum of an indicator.**  Mapping `if p item then b else 0` and summing
is the number of items satisfying `p`, times `b`. -/
theorem sum_map_indicator {α : Type} (items : List α) (p : α → Bool) (b : Nat) :
    (items.map (fun item => if p item then b else 0)).sum = (items.filter p).length * b := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      rw [List.map_cons, List.sum_cons, List.filter_cons, ih]
      cases h : p item <;> simp [h, Nat.succ_mul] <;> omega

/-- The all-zero MAB coordinate. -/
abbrev welcomeZeroCoordinate : MABCoordinate := ⟨0, 0, 0, 0⟩

/-- **The indicator bound over the MAB walk.**  Only the coordinate
`⟨0,0,0,0⟩` can carry a positive budget, and it occurs at most once. -/
theorem allMABCoordinates_indicator_sum (b : Nat) :
    (allMABCoordinates.map (fun coordinate =>
      if coordinate == welcomeZeroCoordinate then b else 0)).sum ≤ b := by
  rw [sum_map_indicator]
  have count : (allMABCoordinates.filter
      (fun coordinate => coordinate == welcomeZeroCoordinate)).length ≤ 1 := by decide
  calc (allMABCoordinates.filter
        (fun coordinate => coordinate == welcomeZeroCoordinate)).length * b
      ≤ 1 * b := Nat.mul_le_mul_right b count
    _ = b := Nat.one_mul b

/-- **The target occurs at most once in the four-PE loop.** -/
theorem finRange_four_filter_count (target : Fin 4) :
    ((List.finRange 4).filter (fun pe => pe == target)).length ≤ 1 := by
  have hval := target.isLt
  have hcases : target.val = 0 ∨ target.val = 1 ∨ target.val = 2 ∨ target.val = 3 := by
    omega
  rcases hcases with h | h | h | h
  · have same : target = ⟨0, by decide⟩ := Fin.ext h
    subst same
    decide
  · have same : target = ⟨1, by decide⟩ := Fin.ext h
    subst same
    decide
  · have same : target = ⟨2, by decide⟩ := Fin.ext h
    subst same
    decide
  · have same : target = ⟨3, by decide⟩ := Fin.ext h
    subst same
    decide

/-- The indicator bound over the four-PE loop of one cycle. -/
theorem finRange_four_indicator_sum (target : Fin 4) (b : Nat) :
    ((List.finRange 4).map (fun pe => if pe == target then b else 0)).sum ≤ b := by
  rw [sum_map_indicator]
  calc ((List.finRange 4).filter (fun pe => pe == target)).length * b
      ≤ 1 * b := Nat.mul_le_mul_right b (finRange_four_filter_count target)
    _ = b := Nat.one_mul b

/-! ## 2. The destination loop of one PE

`writeParsedMatrixMAUDestinationsAtPE` either fails, skips a masked destination
(`parsedMatrixMAUDestinationEnabled? = some false`, no write), or appends the
write list of the shared single-destination writer `writeParsedMslMsrDestination?`.
Every appended list is shaped by the destination's static width and contributes
at most one `.lm1` write. -/

/-- **The matrix-MAU destination loop is a shaped commit.** -/
theorem writeParsedMatrixMAUDestinationsAtPE_widthCount
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool) (output : IntegerALU.Bus)
    (flags : BitVec 4) (w : PEMemory.Width) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      Lm1DestWidths w destinations →
      Lm1DestCount destinations →
      writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
        hasSingleLineMask output flags destinations files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 _ _ executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 widths countOk executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_2] at executed
      cases destination
      case omr entry mask =>
        simp only [Id.run] at executed
        split at executed
        · simp at executed
        · simp only [parsedMatrixMAUDestinationDataPoisonApplies] at executed
          simp only [Bool.false_eq_true, ite_false] at executed
          split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headWidth, headCount⟩ :=
              writeParsedMslMsrDestination?_widthCount files (.omr entry mask) _ output flags
                cycle currentState.maskDirective hasSingleLineMask write w h
                (fun v hv => widths (.omr entry mask) (by simp) v hv)
                (fun bank width hv bankEq =>
                  countOk (.omr entry mask) (by simp) bank width hv bankEq)
            obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ :=
              ih write.files _ _ nextFiles _ _ (fun d mem => widths d (List.mem_cons_of_mem _ mem))
                (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
            refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
            · rw [tailCommit, head, commitParsedMaskedWrites_append]
            · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
            · rw [List.filter_append, List.length_append, filter_length_cons_add]
              have h1 := headCount
              have h2 := tailCount
              omega
      all_goals
        simp only [Id.run] at executed
        split at executed
        · split at executed
          · simp at executed
          · simp at executed
          · have tail := executed
            obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ :=
              ih files bar0 bar1 nextFiles nextBar0 nextBar1
                (fun d mem => widths d (List.mem_cons_of_mem _ mem))
                (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
            refine ⟨tailWrites, tailCommit, tailWidth, ?_⟩
            rw [filter_length_cons_add]
            omega
        · split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headWidth, headCount⟩ :=
              writeParsedMslMsrDestination?_widthCount files _ _ output flags cycle
                currentState.maskDirective hasSingleLineMask write w h
                (fun v hv => widths _ (by simp) v hv)
                (fun bank width hv bankEq => countOk _ (by simp) bank width hv bankEq)
            obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ :=
              ih write.files _ _ nextFiles _ _ (fun d mem => widths d (List.mem_cons_of_mem _ mem))
                (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
            refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
            · rw [tailCommit, head, commitParsedMaskedWrites_append]
            · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
            · rw [List.filter_append, List.length_append, filter_length_cons_add]
              have h1 := headCount
              have h2 := tailCount
              omega

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 3. The four-PE loop of one cycle

At a fixed target PE only that PE's own visit contributes prepared writes: a
visit of another PE commits the target's file with the empty list.  So one cycle
contributes at most the row's `.lm1` destination count to the target. -/

/-- **The four-PE loop of one cycle is a shaped commit at any target PE.** -/
theorem executeParsedMatrixMAUPEWritesAtCycle_widthCount
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations) :
    ∀ (pes : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate hasSingleLineMask
        cycle buses flags poison pes accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (pes.map (fun pe => if pe == target then
            (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length
            else 0)).sum := by
  intro pes
  induction pes with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons pe rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (accum.files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe
              cycle poison hasSingleLineMask (parsedOutputAfterFlush flushSelection (buses pe))
              (flags pe) expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
          | failure =>
              rw [wrote] at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              simp at executed
          | ok result =>
              obtain ⟨nextFiles, nextBar0, nextBar1⟩ := result
              rw [wrote] at executed
              have tail := executed
              obtain ⟨headWrites, head, headWidth, headCount⟩ :=
                writeParsedMatrixMAUDestinationsAtPE_widthCount currentState expression coordinate
                  pe cycle poison hasSingleLineMask
                  (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe) w
                  expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe)
                  nextFiles nextBar0 nextBar1 widths countOk wrote
              obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ := ih _ next tail
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
                · rw [tailCommit]
                  simp only [beq_self_eq_true, ite_true]
                  rw [head, commitParsedMaskedWrites_append]
                · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
                · rw [List.filter_append, List.length_append, List.map_cons, List.sum_cons,
                    beq_self_eq_true, if_pos rfl]
                  have h1 := headCount
                  have h2 := tailCount
                  omega
              · refine ⟨tailWrites, ?_, tailWidth, ?_⟩
                · rw [tailCommit]
                  have different : (target == pe) = false := by
                    simp [same]
                  simp [different]
                · rw [List.map_cons, List.sum_cons]
                  have different : (pe == target) = false := by
                    have notEq : pe ≠ target := fun h => same h.symm
                    simp [notEq]
                  rw [different]
                  simp only [Bool.false_eq_true, if_false, Nat.zero_add]
                  exact tailCount

/-! ## 4. The four-cycle loop of one coordinate -/

/-- **The four-cycle loop of one coordinate is a shaped commit at any target
PE**, with at most one destination count per cycle. -/
theorem executeParsedMatrixMAUWriteCycles_widthCount
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations) :
    ∀ (cycles : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
        hasSingleLineMask cycles accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          cycles.length *
            (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro cycles
  induction cycles with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons cycle rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_2] at executed
      cases calculation : executeParsedMatrixMAUAtMAB readState coordinate expression cycle with
      | failure =>
          rw [calculation] at executed
          simp at executed
      | unknown =>
          rw [calculation] at executed
          simp at executed
      | ok result =>
          rw [calculation] at executed
          dsimp only at executed
          cases writes : executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
              hasSingleLineMask cycle result.1 result.2.1 result.2.2 (List.finRange 4) accum with
          | failure =>
              rw [writes] at executed
              simp at executed
          | unknown =>
              rw [writes] at executed
              simp at executed
          | ok nextAccum =>
              rw [writes] at executed
              have tail := executed
              obtain ⟨headWrites, head, headWidth, headCount⟩ :=
                executeParsedMatrixMAUPEWritesAtCycle_widthCount currentState expression coordinate
                  hasSingleLineMask cycle result.1 result.2.1 result.2.2 target w widths countOk
                  (List.finRange 4) accum nextAccum writes
              obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ := ih nextAccum next tail
              refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
              · rw [tailCommit, head, commitParsedMaskedWrites_append]
              · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
              · rw [List.filter_append, List.length_append, List.length_cons, Nat.succ_mul]
                have h1 := headCount
                have h2 := tailCount
                have bound := finRange_four_indicator_sum target
                  (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length
                omega

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 5. The per-coordinate write list and the transition -/

/-- **The repackaged per-coordinate files are shaped commits.** -/
theorem executeParsedMatrixMAUPEWritesAtMAB_files_widthCount
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (executed : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask = .ok (files, bar0, bar1, outputs, poisoned)) :
    ∃ writes, files target =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1WidthFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        4 * (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  rw [executeParsedMatrixMAUPEWritesAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
      hasSingleLineMask (List.finRange 4)
      { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
        bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
        bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
        outputs := fun _ _ => ⟨0, 0⟩
        poisoned := fun _ => false } with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok accum =>
      rw [ran] at executed
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
        executeParsedMatrixMAUWriteCycles_widthCount readState currentState expression coordinate
          hasSingleLineMask target w widths countOk (List.finRange 4)
          { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
            bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
            bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
            outputs := fun _ _ => ⟨0, 0⟩
            poisoned := fun _ => false } accum ran
      refine ⟨writes, committed, wsWidth, ?_⟩
      simpa using wsCount

/-- **The per-coordinate transition is a shaped commit at each of its four PEs.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_pe_widthCount
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1WidthFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        4 * (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  rw [executeParsedMatrixMAUTransitionAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok result =>
      rw [ran] at executed
      obtain ⟨files, bar0, bar1, outputs, poisoned⟩ := result
      simp only [StepResult.ok.injEq] at executed
      subst executed
      obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
        executeParsedMatrixMAUPEWritesAtMAB_files_widthCount readState currentState expression
          coordinate hasSingleLineMask files bar0 bar1 outputs poisoned target w widths countOk ran
      refine ⟨writes, ?_, wsWidth, wsCount⟩
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      rw [commitParsedMatrixMAUPEState_foldl_peRegisters_target coordinate noForward files bar0 bar1
        outputs poisoned target (List.finRange 4) currentState (List.nodup_finRange 4)
        (List.mem_finRange target)]
      exact committed

/-! ## 6. The walk over the MAB coordinates and the producer -/

/-- **The walk over the MAB coordinates is a shaped commit at a fixed PE**, with
the per-coordinate budget summed over the walk. -/
theorem executeParsedMatrixMAUAtMABs_widthCount
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) (w : PEMemory.Width) (budget : MABCoordinate → Nat)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedMatrixMAUAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes ∧
          Lm1WidthFacts w writes ∧
          (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ budget coordinate) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (coordinates.map budget).sum := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      rw [executeParsedMatrixMAUAtMABs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons coordinate rest ih =>
      intro state next executed stepCommit
      rw [executeParsedMatrixMAUAtMABs.eq_2] at executed
      cases ran : executeParsedMatrixMAUTransitionAtMAB readState state expression coordinate
          noForward hasSingleLineMask with
      | failure =>
          rw [ran] at executed
          simp at executed
      | unknown =>
          rw [ran] at executed
          simp at executed
      | ok middle =>
          rw [ran] at executed
          obtain ⟨headWrites, head, headWidth, headCount⟩ :=
            stepCommit coordinate state middle (by simp) ran
          obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ := ih middle next executed
            (fun coordinate' state' next' member ran' =>
              stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, head, commitParsedMaskedWrites_append]
          · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
          · rw [List.filter_append, List.length_append, List.map_cons, List.sum_cons]
            omega

/-- **The matrix-MAU producer is a shaped PE 0 commit.**  At PE 0 only the
coordinate `⟨0,0,0,0⟩` reaches the file, so the whole row contributes at most
four `.lm1` writes there. -/
theorem executeParsedMatrixMAUProducer_widthCount
    (readState currentState next : State) (expressions : List ParsedExpr)
    (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) (w : PEMemory.Width)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (budgetOk : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (executed : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WidthFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  rw [executeParsedMatrixMAUProducer.eq_1, filterResult] at executed
  dsimp only at executed
  cases ran : executeParsedMatrixMAUAtMABs readState currentState expression allMABCoordinates
      noForward hasSingleLineMask with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok afterMAU =>
      rw [ran] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      have stepCommit : ∀ (coordinate : MABCoordinate) (state' next' : State),
          coordinate ∈ allMABCoordinates →
          executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
            hasSingleLineMask = .ok next' →
          ∃ writes, next'.peRegisters welcomePE =
            commitParsedMaskedWrites (state'.peRegisters welcomePE) writes ∧
            Lm1WidthFacts w writes ∧
            (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
              (if coordinate == welcomeZeroCoordinate then
                4 * (expression.destinations.filter
                  ParsedOperand.isLm1MemoryDestination).length else 0) := by
        intro coordinate state' next' _ ran'
        by_cases zero : coordinate = welcomeZeroCoordinate
        · subst zero
          obtain ⟨ws, committed, wsWidth, wsCount⟩ :=
            executeParsedMatrixMAUTransitionAtMAB_pe_widthCount readState state' next' expression
              welcomeZeroCoordinate noForward hasSingleLineMask 0 w widths countOk ran'
          refine ⟨ws, ?_, wsWidth, ?_⟩
          · simpa [welcomeZeroCoordinate, physicalPEId, welcomePE] using committed
          · have value : (welcomeZeroCoordinate == welcomeZeroCoordinate) = true := by simp
            rw [value, if_pos rfl]
            exact wsCount
        · refine ⟨[], ?_, lm1WidthFacts_nil w, ?_⟩
          · rw [executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame readState state' next'
              expression coordinate noForward hasSingleLineMask welcomePE
              (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) ran']
            rfl
          · have value : (coordinate == welcomeZeroCoordinate) = false := by
              have notEq : coordinate ≠ welcomeZeroCoordinate := zero
              simp [notEq]
            rw [value]
            simp
      obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
        executeParsedMatrixMAUAtMABs_widthCount readState expression noForward hasSingleLineMask
          welcomePE w (fun coordinate =>
            if coordinate == welcomeZeroCoordinate then
              4 * (expression.destinations.filter
                ParsedOperand.isLm1MemoryDestination).length else 0)
          widths countOk allMABCoordinates currentState afterMAU ran stepCommit
      refine ⟨writes, ?_, wsWidth, ?_⟩
      · rw [propagateParsedMatrixMAUPoison_preserves_peRegisters]
        exact committed
      · have bound := allMABCoordinates_indicator_sum
          (4 * (expression.destinations.filter
            ParsedOperand.isLm1MemoryDestination).length)
        omega

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 7. The narrow half at the all-zero state

The width and count facts are unconditional, so the narrow half needs no
datapath input at all: when the row's static `.lm1` width is not `.double`, the
four (at most one per cycle) writes fit in four narrow windows. -/

/-- The all-zero initial state's PE 0 register file is `welcomeZeroFiles`. -/
theorem welcomeZeroInitial_peRegisters :
    (welcomeInitialState welcomeZeroWords).peRegisters welcomePE = welcomeZeroFiles := rfl

/-- **The matrix-MAU producer: narrow shape at the all-zero state.** -/
theorem executeParsedMatrixMAUProducer_zeroNarrow
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool) (w : PEMemory.Width)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (budgetOk : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (notDouble : w ≠ PEMemory.Width.double)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WritesNarrow writes := by
  obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
    executeParsedMatrixMAUProducer_widthCount (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) next expressions expression noForward hasSingleLineMask
      w filterResult widths countOk budgetOk executed
  exact ⟨writes, committed, lm1WidthFacts_narrow writes w wsWidth notDouble wsCount⟩

/-- **The narrow half with the row's static width instantiated.**  The width is
the unique `.lm1` destination width `lm1StaticWidth expression`; the only
remaining hypotheses are the row's own no-duplicate-write condition and that this
width is not `.double`. -/
theorem executeParsedMatrixMAUProducer_zeroNarrow_static
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : (lm1StaticWidth expression).getD PEMemory.Width.word ≠
      PEMemory.Width.double)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WritesNarrow writes :=
  executeParsedMatrixMAUProducer_zeroNarrow expressions expression next noForward hasSingleLineMask
    ((lm1StaticWidth expression).getD PEMemory.Width.word) filterResult
    (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
    (lm1Destinations_count_le_one expression 0 nodup) notDouble executed

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 8. The copy half: the datapath hypothesis

The second half of `Lm1WriteFacts` is that the third data word of every `.lm1`
write is a copy.  A prepared write's data is `unpackALUBus` of the *flushed*
output bus, whose third word is the high word of the bus's low half; a flush only
ANDs the bus, so a copied third word stays copied
(`parsedOutputAfterFlush_word_two_isWelcomeCopy`).  It therefore suffices that
every bus produced by a matrix-MAU cycle at the all-zero state has a zero low
half.  That datapath statement is isolated as `WelcomePEMatrixMAUZeroBus` and
proved in §12.

The chain below produces, for one row, a single write list carrying both the
static width facts (as in §2–§6) and the copy facts. -/

/-- **The matrix-MAU datapath statement.**  At the all-zero state every bus
produced by `executeParsedMatrixMAUAtMAB` has a zero low half (hence a copied
third data word). -/
def WelcomePEMatrixMAUZeroBus : Prop :=
  ∀ (coordinate : MABCoordinate) (expression : ParsedExpr) (cycle : Fin 4)
    (buses : Fin 4 → IntegerALU.Bus) (flags : Fin 4 → BitVec 4) (poison : Bool),
    executeParsedMatrixMAUAtMAB (welcomeInitialState welcomeZeroWords) coordinate expression
      cycle = .ok (buses, flags, poison) →
    ∀ pe : Fin 4, (buses pe).low = 0

/-- A zero low half makes the third unpacked data word a copy. -/
theorem unpackALUBus_copy_of_low_zero (bus : IntegerALU.Bus) (lowZero : bus.low = 0) :
    ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus bus) ⟨2, bound⟩) := by
  intro bound
  rw [unpackALUBus_word_two, lowZero]
  exact isWelcomeCopy_extractLsb_zero

/-- **The flushed bus of a zero-low bus keeps a copied third data word.** -/
theorem parsedOutputAfterFlush_copy_of_low_zero (selection : Option PEWordSelection)
    (bus : IntegerALU.Bus) (lowZero : bus.low = 0) :
    ∀ bound : 2 < 4,
      IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush selection bus)) ⟨2, bound⟩) := by
  intro bound
  rw [unpackALUBus_word_two]
  exact parsedOutputAfterFlush_word_two_isWelcomeCopy selection bus
    (by rw [lowZero]; exact isWelcomeCopy_extractLsb_zero)

/-- **The matrix-MAU destination loop is a shaped copy-fact commit.** -/
theorem writeParsedMatrixMAUDestinationsAtPE_shape
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool) (output : IntegerALU.Bus)
    (flags : BitVec 4) (w : PEMemory.Width)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      Lm1DestWidths w destinations →
      Lm1DestCount destinations →
      writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
        hasSingleLineMask output flags destinations files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 _ _ executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 widths countOk executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_2] at executed
      cases destination
      case omr entry mask =>
        simp only [Id.run] at executed
        split at executed
        · simp at executed
        · simp only [parsedMatrixMAUDestinationDataPoisonApplies] at executed
          simp only [Bool.false_eq_true, ite_false] at executed
          split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headWidth, headCopy, _⟩ :=
              floatMAU_writeParsedMslMsrDestination_facts files (.omr entry mask) _ output flags
                cycle currentState.maskDirective hasSingleLineMask write w h
                (fun v hv => widths (.omr entry mask) (by simp) v hv) copies
                (fun bank width hv bankEq =>
                  countOk (.omr entry mask) (by simp) bank width hv bankEq)
            obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy⟩ :=
              ih write.files _ _ nextFiles _ _ (fun d mem => widths d (List.mem_cons_of_mem _ mem))
                (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
            exact ⟨headWrites ++ tailWrites, by
                rw [tailCommit, head, commitParsedMaskedWrites_append],
              lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth,
              lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩
      all_goals
        simp only [Id.run] at executed
        split at executed
        · split at executed
          · simp at executed
          · simp at executed
          · have tail := executed
            exact ih files bar0 bar1 nextFiles nextBar0 nextBar1
              (fun d mem => widths d (List.mem_cons_of_mem _ mem))
              (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
        · split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headWidth, headCopy, _⟩ :=
              floatMAU_writeParsedMslMsrDestination_facts files _ _ output flags cycle
                currentState.maskDirective hasSingleLineMask write w h
                (fun v hv => widths _ (by simp) v hv) copies
                (fun bank width hv bankEq => countOk _ (by simp) bank width hv bankEq)
            obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy⟩ :=
              ih write.files _ _ nextFiles _ _ (fun d mem => widths d (List.mem_cons_of_mem _ mem))
                (fun d mem => countOk d (List.mem_cons_of_mem _ mem)) tail
            exact ⟨headWrites ++ tailWrites, by
                rw [tailCommit, head, commitParsedMaskedWrites_append],
              lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth,
              lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩

/-- **The four-PE loop of one cycle is a shaped copy-fact commit at any target
PE.** -/
theorem executeParsedMatrixMAUPEWritesAtCycle_shape
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (busZero : ∀ pe, (buses pe).low = 0) :
    ∀ (pes : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate hasSingleLineMask
        cycle buses flags poison pes accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  intro pes
  induction pes with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil⟩
  | cons pe rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (accum.files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe
              cycle poison hasSingleLineMask (parsedOutputAfterFlush flushSelection (buses pe))
              (flags pe) expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
          | failure =>
              rw [wrote] at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              simp at executed
          | ok result =>
              obtain ⟨nextFiles, nextBar0, nextBar1⟩ := result
              rw [wrote] at executed
              have tail := executed
              obtain ⟨headWrites, head, headWidth, headCopy⟩ :=
                writeParsedMatrixMAUDestinationsAtPE_shape currentState expression coordinate
                  pe cycle poison hasSingleLineMask
                  (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe) w
                  (parsedOutputAfterFlush_copy_of_low_zero flushSelection (buses pe) (busZero pe))
                  expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe)
                  nextFiles nextBar0 nextBar1 widths countOk wrote
              obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy⟩ := ih _ next tail
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_,
                  lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth,
                  lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩
                rw [tailCommit]
                simp only [beq_self_eq_true, ite_true]
                rw [head, commitParsedMaskedWrites_append]
              · refine ⟨tailWrites, ?_, tailWidth, tailCopy⟩
                rw [tailCommit]
                have different : (target == pe) = false := by
                  simp [same]
                simp [different]

/-- **The four-cycle loop of one coordinate is a shaped copy-fact commit at any
target PE.** -/
theorem executeParsedMatrixMAUWriteCycles_shape
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (readZero : readState = welcomeInitialState welcomeZeroWords)
    (zeroBus : WelcomePEMatrixMAUZeroBus) :
    ∀ (cycles : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
        hasSingleLineMask cycles accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  subst readZero
  intro cycles
  induction cycles with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil⟩
  | cons cycle rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_2] at executed
      cases calculation : executeParsedMatrixMAUAtMAB (welcomeInitialState welcomeZeroWords)
          coordinate expression cycle with
      | failure =>
          rw [calculation] at executed
          simp at executed
      | unknown =>
          rw [calculation] at executed
          simp at executed
      | ok result =>
          rw [calculation] at executed
          dsimp only at executed
          cases writes : executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
              hasSingleLineMask cycle result.1 result.2.1 result.2.2 (List.finRange 4) accum with
          | failure =>
              rw [writes] at executed
              simp at executed
          | unknown =>
              rw [writes] at executed
              simp at executed
          | ok nextAccum =>
              rw [writes] at executed
              have tail := executed
              obtain ⟨headWrites, head, headWidth, headCopy⟩ :=
                executeParsedMatrixMAUPEWritesAtCycle_shape currentState expression coordinate
                  hasSingleLineMask cycle result.1 result.2.1 result.2.2 target w widths countOk
                  (zeroBus coordinate expression cycle result.1 result.2.1 result.2.2 calculation)
                  (List.finRange 4) accum nextAccum writes
              obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy⟩ := ih nextAccum next tail
              exact ⟨headWrites ++ tailWrites, by
                  rw [tailCommit, head, commitParsedMaskedWrites_append],
                lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth,
                lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- **The repackaged per-coordinate files are shaped copy-fact commits.** -/
theorem executeParsedMatrixMAUPEWritesAtMAB_files_shape
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (readZero : readState = welcomeInitialState welcomeZeroWords)
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (executed : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask = .ok (files, bar0, bar1, outputs, poisoned)) :
    ∃ writes, files target =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  rw [executeParsedMatrixMAUPEWritesAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
      hasSingleLineMask (List.finRange 4)
      { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
        bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
        bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
        outputs := fun _ _ => ⟨0, 0⟩
        poisoned := fun _ => false } with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok accum =>
      rw [ran] at executed
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact executeParsedMatrixMAUWriteCycles_shape readState currentState expression coordinate
        hasSingleLineMask target w widths countOk readZero zeroBus (List.finRange 4)
        { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
          bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
          bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
          outputs := fun _ _ => ⟨0, 0⟩
          poisoned := fun _ => false } accum ran

/-- **The per-coordinate transition is a shaped copy-fact commit at each of its
four PEs.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_pe_shape
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (target : Fin 4) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (readZero : readState = welcomeInitialState welcomeZeroWords)
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  rw [executeParsedMatrixMAUTransitionAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok result =>
      rw [ran] at executed
      obtain ⟨files, bar0, bar1, outputs, poisoned⟩ := result
      simp only [StepResult.ok.injEq] at executed
      subst executed
      obtain ⟨writes, committed, wsWidth, wsCopy⟩ :=
        executeParsedMatrixMAUPEWritesAtMAB_files_shape readState currentState expression
          coordinate hasSingleLineMask files bar0 bar1 outputs poisoned target w widths countOk
          readZero zeroBus ran
      refine ⟨writes, ?_, wsWidth, wsCopy⟩
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      rw [commitParsedMatrixMAUPEState_foldl_peRegisters_target coordinate noForward files bar0 bar1
        outputs poisoned target (List.finRange 4) currentState (List.nodup_finRange 4)
        (List.mem_finRange target)]
      exact committed

/-- **The walk over the MAB coordinates is a shaped copy-fact commit at a fixed
PE.** -/
theorem executeParsedMatrixMAUAtMABs_shape
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedMatrixMAUAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes ∧
          Lm1WidthFacts w writes ∧ Lm1CopyFacts writes) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      rw [executeParsedMatrixMAUAtMABs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil⟩
  | cons coordinate rest ih =>
      intro state next executed stepCommit
      rw [executeParsedMatrixMAUAtMABs.eq_2] at executed
      cases ran : executeParsedMatrixMAUTransitionAtMAB readState state expression coordinate
          noForward hasSingleLineMask with
      | failure =>
          rw [ran] at executed
          simp at executed
      | unknown =>
          rw [ran] at executed
          simp at executed
      | ok middle =>
          rw [ran] at executed
          obtain ⟨headWrites, head, headWidth, headCopy⟩ :=
            stepCommit coordinate state middle (by simp) ran
          obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy⟩ := ih middle next executed
            (fun coordinate' state' next' member ran' =>
              stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
          exact ⟨headWrites ++ tailWrites, by
              rw [tailCommit, head, commitParsedMaskedWrites_append],
            lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth,
            lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩

/-- **The matrix-MAU producer is a shaped copy-fact PE 0 commit.** -/
theorem executeParsedMatrixMAUProducer_shape
    (currentState next : State) (expressions : List ParsedExpr)
    (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) (w : PEMemory.Width)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
  rw [executeParsedMatrixMAUProducer.eq_1, filterResult] at executed
  dsimp only at executed
  cases ran : executeParsedMatrixMAUAtMABs (welcomeInitialState welcomeZeroWords) currentState
      expression allMABCoordinates noForward hasSingleLineMask with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok afterMAU =>
      rw [ran] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      have stepCommit : ∀ (coordinate : MABCoordinate) (state' next' : State),
          coordinate ∈ allMABCoordinates →
          executeParsedMatrixMAUTransitionAtMAB (welcomeInitialState welcomeZeroWords) state'
            expression coordinate noForward hasSingleLineMask = .ok next' →
          ∃ writes, next'.peRegisters welcomePE =
            commitParsedMaskedWrites (state'.peRegisters welcomePE) writes ∧
            Lm1WidthFacts w writes ∧ Lm1CopyFacts writes := by
        intro coordinate state' next' _ ran'
        by_cases zero : coordinate = welcomeZeroCoordinate
        · subst zero
          obtain ⟨ws, committed, wsWidth, wsCopy⟩ :=
            executeParsedMatrixMAUTransitionAtMAB_pe_shape
              (welcomeInitialState welcomeZeroWords) state' next' expression welcomeZeroCoordinate
              noForward hasSingleLineMask 0 w widths countOk rfl zeroBus ran'
          exact ⟨ws, by
            simpa [welcomeZeroCoordinate, physicalPEId, welcomePE] using committed, wsWidth, wsCopy⟩
        · refine ⟨[], ?_, lm1WidthFacts_nil w, lm1CopyFacts_nil⟩
          rw [executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame
            (welcomeInitialState welcomeZeroWords) state' next' expression coordinate noForward
            hasSingleLineMask welcomePE
            (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) ran']
          rfl
      obtain ⟨writes, committed, wsWidth, wsCopy⟩ :=
        executeParsedMatrixMAUAtMABs_shape (welcomeInitialState welcomeZeroWords) expression
          noForward hasSingleLineMask welcomePE w widths countOk allMABCoordinates
          currentState afterMAU ran stepCommit
      refine ⟨writes, ?_, wsWidth, wsCopy⟩
      rw [propagateParsedMatrixMAUPoison_preserves_peRegisters]
      exact committed

/-! ## 9. The matrix-MAU row shape at the all-zero state -/

/-- **The matrix-MAU row shape at the all-zero state**, conditional on the
datapath statement `WelcomePEMatrixMAUZeroBus`.  The PE 0 prepared write list of
one matrix-MAU row is committed at `welcomeZeroFiles` and is either all copied
`.double` blocks or fits in four narrow windows. -/
theorem executeParsedMatrixMAUProducer_zeroShape_of_zeroBus
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool) (w : PEMemory.Width)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (widths : Lm1DestWidths w expression.destinations)
    (countOk : Lm1DestCount expression.destinations)
    (budgetOk : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  by_cases isDouble : w = PEMemory.Width.double
  · subst isDouble
    obtain ⟨writes, committed, wsWidth, wsCopy⟩ :=
      executeParsedMatrixMAUProducer_shape (welcomeInitialState welcomeZeroWords) next expressions
        expression noForward hasSingleLineMask PEMemory.Width.double filterResult widths countOk
        zeroBus executed
    refine ⟨writes, ?_, Or.inl ?_⟩
    · rw [← welcomeZeroInitial_peRegisters]
      exact committed
    · exact lm1WriteFacts_doubleCopy writes
        (lm1WriteFacts_of_parts PEMemory.Width.double writes wsWidth wsCopy)
  · obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
      executeParsedMatrixMAUProducer_widthCount (welcomeInitialState welcomeZeroWords)
        (welcomeInitialState welcomeZeroWords) next expressions expression noForward hasSingleLineMask
        w filterResult widths countOk budgetOk executed
    refine ⟨writes, ?_, Or.inr (lm1WidthFacts_narrow writes w wsWidth isDouble wsCount)⟩
    rw [← welcomeZeroInitial_peRegisters]
    exact committed

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 10. The datapath statement `WelcomePEMatrixMAUZeroBus`

At the all-zero state the matrix registers, the PE files and the forwarding
slots all read zero, so every matrix-MAU cycle produces the zero bus.  The proof
has four layers: the zero block-float store, the lane decoding of a zero source
read, the row computation, and the packing of the per-PE buses. -/

/-! ### 10.1 The zero block-float store -/

/-- The maximum exponent of a list of zeros is zero. -/
theorem matrixMAU_foldl_max_replicate (n : Nat) :
    List.foldl Nat.max 0 (List.replicate n (0 : Nat)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; simpa using ih

theorem maxFloatExponent_replicate_zero (precision : RRN.FloatPrecision) (n : Nat) :
    RRN.maxFloatExponent precision (List.replicate n 0) = 0 := by
  rw [RRN.maxFloatExponent, List.map_replicate, RRN.floatExponent]
  simpa using matrixMAU_foldl_max_replicate n

theorem encodeMAUValue_zero (precision : RRN.FloatPrecision) (negative : Bool) :
    RRN.encodeMAUValue precision (RRN.MAUValue.zero negative) = 0 := rfl

theorem decodeMAUValue_zero (precision : RRN.FloatPrecision) :
    RRN.decodeMAUValue precision 0 = RRN.MAUValue.zero false := by
  simp [RRN.decodeMAUValue, RRN.floatExponent, RRN.floatIsNegative]

theorem decodeMAUValue_signMask (precision : RRN.FloatPrecision) :
    RRN.decodeMAUValue precision (2 ^ (precision.width - 1)) = RRN.MAUValue.zero true := by
  cases precision <;> decide

theorem addMAUValues_zero (a b : Bool) :
    RRN.addMAUValues (RRN.MAUValue.zero a) (RRN.MAUValue.zero b) =
      RRN.MAUValue.zero (a && b) := rfl

theorem alignMAUAccumulator_zero (negative : Bool) (grid : Int) :
    RRN.alignMAUAccumulator (RRN.MAUValue.zero negative) grid =
      RRN.MAUValue.zero negative := rfl

/-- **The block-float dot of a zero left block is the zero value.** -/
theorem matrixBlockFloatDot_zero_left (precision : RRN.FloatPrecision) (keptBits n : Nat)
    (right : List Nat) :
    RRN.matrixBlockFloatDot precision keptBits (List.replicate n 0) right =
      (RRN.MAUValue.zero false, none) := by
  rw [RRN.matrixBlockFloatDot, maxFloatExponent_replicate_zero]
  simp

/-- **A matrix element of the all-zero store is zero.** -/
theorem parsedMatrixMAUElement_zero_store (mab : Fin 16) (sideY : Bool)
    (precision : ParsedPrecision) (row column : Nat)
    (float : parsedMatrixMAUFloatFormat precision ≠ none) :
    PEMemory.parsedMatrixMAUElement (fun _ _ _ _ => 0) mab sideY precision row column = some 0 := by
  cases precision with
  | d => simp [PEMemory.parsedMatrixMAUElement, doubleMatrixFaceFromPhysicalWords]
  | f => simp [PEMemory.parsedMatrixMAUElement]
  | g => simp [PEMemory.parsedMatrixMAUElement]
  | h => simp [PEMemory.parsedMatrixMAUElement, halfMatrixPhysicalElement]
  | l => simp [parsedMatrixMAUFloatFormat] at float
  | i => simp [parsedMatrixMAUFloatFormat] at float
  | s => simp [parsedMatrixMAUFloatFormat] at float

theorem replicate_append_singleton {α : Type} (n : Nat) (a : α) :
    List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- `List.mapM` over a range with a constant value. -/
theorem list_mapM_range_replicate {α : Type} (n : Nat) (f : Nat → Option α) (c : α)
    (step : ∀ i, i < n → f i = some c) :
    (List.range n).mapM f = some (List.replicate n c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.mapM_append]
      rw [ih (fun i hi => step i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
      have hn : f n = some c := step n (Nat.lt_succ_self n)
      simp [hn, List.replicate_succ, List.mapM_cons, replicate_append_singleton]

/-- **A product row of the all-zero store is a zero row.** -/
theorem parsedMatrixMAUProductRow_zero_store (mab : Fin 16) (sideY : Bool)
    (precision : ParsedPrecision) (row : Nat)
    (float : parsedMatrixMAUFloatFormat precision ≠ none) :
    PEMemory.parsedMatrixMAUProductRow? (fun _ _ _ _ => 0) mab sideY precision row =
      some (List.replicate (PEMemory.parsedMatrixMAUDotWidth precision) 0) := by
  unfold PEMemory.parsedMatrixMAUProductRow?
  exact list_mapM_range_replicate (PEMemory.parsedMatrixMAUDotWidth precision) _ 0
    (fun index _ => parsedMatrixMAUElement_zero_store mab sideY precision row _ float)

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ### 10.2 The source layer: zero reads at the all-zero state -/

theorem welcomeZero_forwarding (pe : PEId) :
    (welcomeInitialState welcomeZeroWords).forwarding pe
      = fun _ _ => Forwarding.Value.known ⟨0, 0⟩ := by
  funext unit cycle
  cases unit <;> rfl

/-- One decoded lane of the zero bus is zero or the sign mask. -/
theorem parsedMatrixMAUDecodeLane_zero (format rawFormat : RRN.FloatPrecision) (index : Nat)
    (negate : Bool) :
    (let rawWidth := rawFormat.width
     let shift := 128 - rawWidth * (index + 1)
     let raw := (((⟨0, 0⟩ : IntegerALU.Bus).high ++ (⟨0, 0⟩ : IntegerALU.Bus).low).extractLsb'
       shift rawWidth).toNat
     let converted := RRN.encodeMAUValue format (RRN.decodeMAUValue rawFormat raw)
     if negate then
       (BitVec.ofNat format.width converted ^^^
         BitVec.ofNat format.width (2 ^ (format.width - 1))).toNat
     else converted) = (if negate then 2 ^ (format.width - 1) else 0) := by
  cases format <;> cases rawFormat <;> cases negate <;>
    simp [RRN.decodeMAUValue, RRN.encodeMAUValue, RRN.floatExponent, RRN.floatIsNegative,
      RRN.FloatPrecision.width, RRN.FloatPrecision.exponentBits, RRN.FloatPrecision.mantissaBits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt]

/-- **The decoded lanes of the zero bus are zero or the sign mask.** -/
theorem parsedMatrixMAUDecodeLanes_zero (format : RRN.FloatPrecision) (count : Nat)
    (negate extend round : Bool) (lanes : List Nat)
    (decoded : parsedMatrixMAUDecodeLanes? format count (⟨0, 0⟩ : IntegerALU.Bus) negate extend round
      = some lanes) :
    lanes = List.replicate count (if negate then 2 ^ (format.width - 1) else 0) := by
  cases format <;> cases extend <;> cases round <;> cases negate <;>
    simp [parsedMatrixMAUDecodeLanes?, parsedMatrixMAULowerFormat, parsedMatrixMAUHigherFormat,
      RRN.decodeMAUValue, RRN.encodeMAUValue, RRN.floatExponent, RRN.floatIsNegative,
      RRN.FloatPrecision.width, RRN.FloatPrecision.exponentBits, RRN.FloatPrecision.mantissaBits,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt] at decoded ⊢ <;> exact decoded.symm

/-- **A successful matrix-MAU source read at the all-zero state is constant.**
Its lanes are all zero, or all the sign mask. -/
theorem readParsedMatrixMAUSourcePE_zero (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (pe cycle : Fin 4) (lanes : List Nat)
    (read : readParsedMatrixMAUSourcePE (welcomeInitialState welcomeZeroWords) coordinate operand
      precision count pe cycle = .ok lanes) :
    ∃ negative : Bool, lanes = List.replicate count
      (if negative then 2 ^ (precision.width - 1) else 0) := by
  unfold readParsedMatrixMAUSourcePE at read
  simp only [Id.run] at read
  cases attrs : parsedFloatMAUSourceAttrs? operand
      { ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
        cycle := cycle
        bar0 := ((welcomeInitialState welcomeZeroWords).peContext (physicalPEId coordinate pe)).bar0
        bar1 := ((welcomeInitialState welcomeZeroWords).peContext (physicalPEId coordinate pe)).bar1
        tWord := ((welcomeInitialState welcomeZeroWords).peContext (physicalPEId coordinate pe)).tWord } with
  | none => simp [attrs] at read
  | some p =>
    obtain ⟨input, neg, ext, rnd⟩ := p
    cases input with
    | memory access rounded =>
      rw [attrs] at read
      dsimp only at read
      rw [show ParsedIntegerInput.readWithForwarding
          ((welcomeInitialState welcomeZeroWords).peRegisters (physicalPEId coordinate pe))
          ((welcomeInitialState welcomeZeroWords).forwarding (physicalPEId coordinate pe)) cycle
          (.memory access rounded) =
          .ok (ParsedIntegerInput.applyRounding rounded
            (pack (readDirectAccess welcomeZeroFiles access))) from rfl] at read
      rw [welcomeZero_pack_readDirectAccess_zero] at read
      rw [welcomeHalfMAU_applyRounding_zero] at read
      dsimp only at read
      split at read
      · have contra : (StepResult.failure : StepResult (List Nat)) = StepResult.ok lanes := read
        cases contra
      · rename_i chosen hchosen
        have okEq : StepResult.ok chosen = StepResult.ok lanes := read
        obtain rfl := StepResult.ok.inj okEq
        exact ⟨neg, parsedMatrixMAUDecodeLanes_zero precision count neg ext rnd chosen hchosen⟩
    | fixed value =>
      cases operand <;>
        simp [parsedFloatMAUSourceAttrs?, ParsedOperand.toParsedIntegerInput?] at attrs
    | forward kind rounded =>
      rw [attrs] at read
      dsimp only at read
      rw [welcomeZero_forwarding (physicalPEId coordinate pe)] at read
      split at read
      · have contra : (StepResult.failure : StepResult (List Nat)) = StepResult.ok lanes := read
        cases contra
      · rename_i hvalid
        have invalid : (welcomeInitialState welcomeZeroWords).forwardingValid
            (physicalPEId coordinate pe) (ParsedIntegerInput.forwardUnit kind) cycle = false := rfl
        rw [invalid] at hvalid
        simp at hvalid

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- **The four-PE source read at the all-zero state.**  Every lane is zero or
the sign mask, and the result has `4 * count` entries. -/
theorem readParsedMatrixMAUSourcePEsAux_zero (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4) :
    ∀ (pes : List (Fin 4)) (initial values : List Nat),
      readParsedMatrixMAUSourcePEsAux (welcomeInitialState welcomeZeroWords) coordinate operand
        format count cycle pes initial = .ok values →
      values.length = initial.length + pes.length * count ∧
      (∀ value ∈ values, value ∈ initial ∨
        value = 0 ∨ value = 2 ^ (format.width - 1)) := by
  intro pes
  induction pes with
  | nil =>
      intro initial values executed
      rw [readParsedMatrixMAUSourcePEsAux.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨by simp, by intro value hvalue; exact Or.inl hvalue⟩
  | cons pe rest ih =>
      intro initial values executed
      rw [readParsedMatrixMAUSourcePEsAux.eq_2] at executed
      cases read : readParsedMatrixMAUSourcePE (welcomeInitialState welcomeZeroWords) coordinate
          operand format count pe cycle with
      | failure =>
          rw [read] at executed
          simp at executed
      | unknown =>
          rw [read] at executed
          simp at executed
      | ok lanes =>
          rw [read] at executed
          obtain ⟨negative, lanesEq⟩ :=
            readParsedMatrixMAUSourcePE_zero coordinate operand format count pe cycle lanes read
          obtain ⟨lengthEq, valuesMem⟩ := ih (initial ++ lanes) values executed
          subst lanesEq
          refine ⟨?_, ?_⟩
          · rw [List.length_append, List.length_replicate] at lengthEq
            rw [List.length_cons, Nat.succ_mul]
            omega
          · intro value hvalue
            rcases valuesMem value hvalue with hinit | hzero | hsign
            · rcases List.mem_append.mp hinit with earlier | later
              · exact Or.inl earlier
              · rw [List.mem_replicate] at later
                cases negative with
                | false => exact Or.inr (Or.inl (by simpa using later.2))
                | true => exact Or.inr (Or.inr (by simpa using later.2))
            · exact Or.inr (Or.inl hzero)
            · exact Or.inr (Or.inr hsign)

/-- **The MAB source read at the all-zero state.**  The lanes are zero or the
sign mask (hence decode to a zero `MAUValue`), and there are `4 * count` of
them. -/
theorem readParsedMatrixMAUSourceAtMAB_zero (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (values : List Nat)
    (read : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      operand format count cycle = .ok values) :
    values.length = 4 * count ∧
      (∀ value ∈ values, ∃ negative : Bool,
        RRN.decodeMAUValue format value = RRN.MAUValue.zero negative) := by
  unfold readParsedMatrixMAUSourceAtMAB readParsedMatrixMAUSourcePEs at read
  obtain ⟨lengthEq, valuesMem⟩ := readParsedMatrixMAUSourcePEsAux_zero coordinate operand format
    count cycle (List.finRange 4) [] values read
  refine ⟨by simpa using lengthEq, ?_⟩
  intro value hvalue
  rcases valuesMem value hvalue with hempty | hzero | hsign
  · simp at hempty
  · subst hzero
    exact ⟨false, decodeMAUValue_zero format⟩
  · subst hsign
    exact ⟨true, decodeMAUValue_signMask format⟩

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ### 10.3 The row computation at the all-zero store: what remains

With a zero store and a zero (or negative-zero) accumulator every logical output
row of `parsedMatrixMAUCalculateRows?` is `0`; then `parsedMatrixMAUPackPEBus?`
packs zero lanes into a bus with a zero low half (`.d`/`.f`/`.g` always return
`⟨_, 0⟩`, and `.h` returns `⟨0, 0⟩` on zero lanes), which is
`WelcomePEMatrixMAUZeroBus`.

The remaining statement is

```
theorem parsedMatrixMAUCalculateRows_zero_store
    (coordinate : MABCoordinate) (sideY : Bool) (precision : ParsedPrecision)
    (kind : CalcKind) (half : Option Char) (round : Bool) (vector accumulator : List Nat)
    (float : parsedMatrixMAUFloatFormat precision ≠ none)
    (out : parsedMatrixMAUOutputFormat precision round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat precision) value =
        RRN.MAUValue.zero negative)
    (accLength : accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE precision) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY precision kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount precision) 0)
```

Its proof is the `cases precision` restructure of the `do` block (the row step is
already proved as `parsedMatrixMAUCalculateRow_zero` below, and the needed
count bound as `parsedMatrixMAURowCount_le_accumulator`): after `cases precision`
the accumulator format, the input format and the store rows are concrete, so the
`do` block reduces, and the two binds (`parsedMatrixMAUProductRow_zero_store` and
the accumulator slot) can be discharged. -/

theorem parsedMatrixMAURowCount_le_accumulator (precision : ParsedPrecision) :
    parsedMatrixMAURowCount precision ≤ 4 * parsedMatrixMAUAccumulatorLanesPerPE precision := by
  cases precision <;> decide

/-- **One output row of the all-zero store is zero.**  With a zero block-float
left operand, any vector lanes and a zero/negative-zero accumulator the row
value is `0`. -/
theorem parsedMatrixMAUCalculateRow_zero (inputFormat outputFormat accFormat : RRN.FloatPrecision)
    (keptBits : Nat) (n : Nat) (vector : List Nat) (accumulatorBits : Nat) (negative : Bool)
    (accDecoded : RRN.decodeMAUValue accFormat accumulatorBits = RRN.MAUValue.zero negative) :
    RRN.encodeMAUValue outputFormat
      (RRN.addMAUValues
        (RRN.matrixBlockFloatDot inputFormat keptBits (List.replicate n 0) vector).1
        (match (RRN.matrixBlockFloatDot inputFormat keptBits (List.replicate n 0) vector).2 with
         | some value =>
             RRN.alignMAUAccumulator (RRN.decodeMAUValue accFormat accumulatorBits) value
         | none => RRN.decodeMAUValue accFormat accumulatorBits)) = 0 := by
  rw [matrixBlockFloatDot_zero_left, accDecoded]
  rfl

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 11. The row shape with the static width instantiated -/

/-- **The matrix-MAU row shape at the all-zero state, with the row's static
width instantiated.**  As `executeParsedMatrixMAUProducer_zeroShape_of_zeroBus`,
but with `w = lm1StaticWidth expression` and the destination-count side
conditions discharged from the row's own no-duplicate-write hypothesis. -/
theorem executeParsedMatrixMAUProducer_zeroShape_static_of_zeroBus
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedMatrixMAUProducer_zeroShape_of_zeroBus zeroBus expressions expression next
    noForward hasSingleLineMask ((lm1StaticWidth expression).getD PEMemory.Width.word)
    filterResult (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
    (lm1Destinations_count_le_one expression 0 nodup) executed

end ProofsLean.MNCore

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 12. The whole matrix-MAU/write stage at the all-zero state

The write half of the stage (`executeParsedMatrixWritesAtMABs`) preserves every
PE register file (`executeParsedMatrixWritesAtMABs_preserves_pe_state`), so the
PE 0 write list of the whole stage is the producer's.  The row shapes of §7 and
§11 therefore hold for `executeParsedMatrixMAUAndWrites` as well. -/

/-- **The matrix-MAU/write stage: narrow shape at the all-zero state.** -/
theorem executeParsedMatrixMAUAndWrites_zeroNarrow_static
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : (lm1StaticWidth expression).getD PEMemory.Width.word ≠
      PEMemory.Width.double)
    (executed : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WritesNarrow writes := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask with
  | failure =>
      rw [producer] at executed
      simp at executed
  | unknown =>
      rw [producer] at executed
      simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      obtain ⟨writes, committed, narrow⟩ :=
        executeParsedMatrixMAUProducer_zeroNarrow_static expressions expression afterMAU
          noForward hasSingleLineMask filterResult nodup notDouble producer
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state
        (welcomeInitialState welcomeZeroWords) afterMAU next allMABCoordinates expressions executed
      exact ⟨writes, by rw [frame.1]; exact committed, narrow⟩

/-- **The matrix-MAU/write stage shape at the all-zero state**, conditional on
the datapath statement `WelcomePEMatrixMAUZeroBus`. -/
theorem executeParsedMatrixMAUAndWrites_zeroShape_static_of_zeroBus
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask with
  | failure =>
      rw [producer] at executed
      simp at executed
  | unknown =>
      rw [producer] at executed
      simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      obtain ⟨writes, committed, shape⟩ :=
        executeParsedMatrixMAUProducer_zeroShape_static_of_zeroBus zeroBus expressions expression
          afterMAU noForward hasSingleLineMask filterResult nodup producer
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state
        (welcomeInitialState welcomeZeroWords) afterMAU next allMABCoordinates expressions executed
      exact ⟨writes, by rw [frame.1]; exact committed, shape⟩

end ProofsLean.MNCore
