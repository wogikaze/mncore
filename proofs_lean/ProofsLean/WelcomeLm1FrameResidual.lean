import ProofsLean.WelcomeFrameFix
import ProofsLean.WelcomeMatrixMAUCommit

/-! # The last two `.lm1` stage frames

`WelcomeFrameFix.lean` (round 38) reduced `WelcomePEStageLm1Frame` to two named
residuals, `WelcomePEMatrixMAUStageLm1Frame` and `WelcomePEL1ToPEStageLm1Frame`.
This module discharges both.

Both stages write PE 0's register file only through prepared masked writes, and
both are already known to be commits at PE 0 (`WelcomeStageCommit.lean` §4 and
`WelcomeMatrixMAUCommit.lean` §6).  What the frames still need is the *negative
provenance* half: every write in those lists comes from a destination operand
whose static bank is not `.lm1`.  Rather than materialise the provenance list,
the argument below is carried out directly on the loops, which is the same
proof as "commit of a `.lm1`-free list preserves the bank"
(`commitParsedMaskedWrites_lm1_of_no_lm1`) fused with the commit induction: a
single write into a bank other than `.lm1` leaves the bank alone, and every loop
that threads the writes preserves it step by step.

* §1 proves the per-destination half for the L1BM-to-PE writer
  `writeParsedL1ToPEDestination?` (which the stage owns, unlike the shared
  single-destination writer used by the other stages), then lifts it through the
  destination loop, the four-cycle loop, the PE walk and the family filter.
* §2 does the same for the matrix-MAU/write stage: the destination loop of
  `writeParsedMatrixMAUDestinationsAtPE`, the four-PE loop of one cycle, the
  four-cycle loop, the `commitParsedMatrixMAUPEState` installation fold and the
  walk over the 1024 MAB coordinates.
* §3 instantiates the two residual `Prop`s and combines them with
  `welcomePEStageLm1Frame_of_residuals`, so `WelcomePEStageLm1Frame` holds
  unconditionally.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The L1BM-to-PE stage

The stage's destination writer is `writeParsedL1ToPEDestination?`, which either
stores the broadcast bus into a `.mem` destination, records a `.bar` update, or
does nothing.  Only the first case touches a register file, and it writes the
bank the destination operand resolves to. -/

/-- **The L1BM-to-PE destination writer leaves `.lm1` alone.** -/
theorem writeParsedL1ToPEDestination?_lm1_of_ne
    (files : IntegerRegisterFiles) (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (nextFiles : IntegerRegisterFiles) (barUpdate : Option (Bool × BitVec 12))
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination context output
      cycle directive hasSingleLineMask = some (nextFiles, barUpdate)) :
    nextFiles.lm1 = files.lm1 := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
          (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
          context.bar0 context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
              (ParsedOperand.mem access negated extended rounded mask) found.bank
              maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              obtain ⟨rfl, rfl⟩ := lowered
              have static := ParsedOperand.toDirectMemoryDestination?_bankWidth
                (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
                context.bar0 context.bar1 context.tWord
              rw [h] at static
              exact writeDirectAccessMasked_lm1_of_ne files found _ _
                (noLm1 found.bank found.width static.symm)
  | bar lm1 width mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
        (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) maskRegisters
        cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          obtain ⟨rfl, rfl⟩ := lowered
          rfl
  | nowrite =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      obtain ⟨rfl, rfl⟩ := Option.some.inj lowered
      rfl
  | omr entry mask => simp [writeParsedL1ToPEDestination?] at lowered
  | forward kind neg ext rnd => simp [writeParsedL1ToPEDestination?] at lowered
  | fixed value => simp [writeParsedL1ToPEDestination?] at lowered
  | matrix side width row => simp [writeParsedL1ToPEDestination?] at lowered
  | l1bm width address => simp [writeParsedL1ToPEDestination?] at lowered
  | l2bm address l2b => simp [writeParsedL1ToPEDestination?] at lowered
  | dar value => simp [writeParsedL1ToPEDestination?] at lowered

/-- **The L1BM-to-PE destination loop preserves `.lm1`.** -/
theorem executeParsedL1ToPE_writeDestinations_lm1_frame
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      rfl
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      cases lowered : writeParsedL1ToPEDestination? files maskRegisters destination
          { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
          hasSingleLineMask with
      | none =>
          rw [executeParsedL1ToPE_writeDestinations_cons_none currentState hasSingleLineMask
            maskRegisters cycle context output destination rest files bar0 bar1 lowered] at executed
          simp at executed
      | some pair =>
          obtain ⟨writeFiles, barUpdate⟩ := pair
          cases barUpdate with
          | none =>
              rw [executeParsedL1ToPE_writeDestinations_cons_some_none currentState
                hasSingleLineMask maskRegisters cycle context output destination rest files bar0
                bar1 writeFiles lowered] at executed
              rw [ih writeFiles bar0 bar1 nextFiles nextBar0 nextBar1
                (fun item member bank width pair bankEq =>
                  noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq) executed]
              exact writeParsedL1ToPEDestination?_lm1_of_ne files maskRegisters destination
                { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
                hasSingleLineMask
                (fun bank width pair bankEq =>
                  noLm1 destination (by simp) bank width pair bankEq) writeFiles none lowered
          | some update =>
              obtain ⟨barFlag, value⟩ := update
              cases barFlag with
              | false =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  rw [ih writeFiles value bar1 nextFiles nextBar0 nextBar1
                    (fun item member bank width pair bankEq =>
                      noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq) executed]
                  exact writeParsedL1ToPEDestination?_lm1_of_ne files maskRegisters destination
                    { context with bar0 := bar0, bar1 := bar1 } output cycle
                    currentState.maskDirective hasSingleLineMask
                    (fun bank width pair bankEq =>
                      noLm1 destination (by simp) bank width pair bankEq) writeFiles
                    (some (false, value)) lowered
              | true =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  rw [ih writeFiles bar0 value nextFiles nextBar0 nextBar1
                    (fun item member bank width pair bankEq =>
                      noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq) executed]
                  exact writeParsedL1ToPEDestination?_lm1_of_ne files maskRegisters destination
                    { context with bar0 := bar0, bar1 := bar1 } output cycle
                    currentState.maskDirective hasSingleLineMask
                    (fun bank width pair bankEq =>
                      noLm1 destination (by simp) bank width pair bankEq) writeFiles
                    (some (true, value)) lowered

/-- **The L1BM-to-PE four-cycle loop preserves `.lm1`.** -/
theorem executeParsedL1ToPE_writeCycles_lm1_frame
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ access.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters cycles files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons cycle rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush maskRegisters cycle with
      | none =>
          rw [flush] at executed
          dsimp only at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          split at executed
          · simp at executed
          · rename_i middleFiles middleBar0 middleBar1 wrote
            rw [ih middleFiles middleBar0 middleBar1 nextFiles nextBar0 nextBar1 noLm1 executed]
            exact executeParsedL1ToPE_writeDestinations_lm1_frame currentState hasSingleLineMask
              maskRegisters cycle _ _ access.destinations files bar0 bar1 middleFiles
              middleBar0 middleBar1 noLm1 wrote

/-- **The L1BM-to-PE walk preserves `.lm1` at every PE.** -/
theorem executeParsedL1ToPEAtPEs_lm1_frame (readState : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      (∀ destination ∈ access.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedL1ToPEAtPEs readState state expression access pes noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      (next.peRegisters p).lm1 = (state.peRegisters p).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro state p next noLm1 executed
      simp only [executeParsedL1ToPEAtPEs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state p next noLm1 executed
      rw [executeParsedL1ToPEAtPEs.eq_2] at executed
      split at executed
      · simp at executed
      · simp only [] at executed
        split at executed
        · simp at executed
        · simp at executed
        · rename_i files bar0 bar1 ran
          have tail := ih _ p next noLm1 executed
          by_cases same : p = pe
          · rw [same] at tail ⊢
            rw [tail]
            dsimp only
            simp only [ite_true]
            exact executeParsedL1ToPE_writeCycles_lm1_frame readState state expression access
              hasSingleLineMask pe _ _ _ [0, 1, 2, 3] (state.peRegisters pe) _ _ files
              bar0 bar1 noLm1 ran
          · rw [tail]
            dsimp only
            simp [same]

/-- **A successful lowering exposes the row's destination list.** -/
theorem lowerParsedL1ToPE?_destinations (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (lowered : lowerParsedL1ToPE? expression = some access) :
    access.destinations = expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [lowerParsedL1ToPE?] at lowered
  split at lowered <;>
    (try split at lowered) <;>
    (try split at lowered) <;>
    (try simp at lowered) <;>
    (try (rw [Option.bind_eq_some_iff] at lowered
          obtain ⟨u, -, hsome⟩ := lowered
          simp only [Option.some.injEq] at hsome
          rw [← hsome]))

/-- **The L1BM-to-PE producer preserves PE 0's `.lm1`.** -/
theorem executeParsedL1ToPEProducer_lm1_frame
    (readState currentState next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  cases lowered : lowerParsedL1ToPE? expression with
  | none =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      simp at executed
  | some access =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      exact executeParsedL1ToPEAtPEs_lm1_frame readState expression access noForward
        hasSingleLineMask usePreIssueMask (List.finRange 4096) currentState welcomePE next
        (fun destination member bank width pair bankEq =>
          noLm1 destination
            (lowerParsedL1ToPE?_destinations expression access lowered ▸ member)
            bank width pair bankEq)
        executed

/-- **The L1BM-to-PE family filter preserves PE 0's `.lm1`.** -/
theorem executeParsedL1ToPEProducers_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  cases filtered : expressions.filter parsedExprIsL1ToPEProducer with
  | nil =>
      rw [executeParsedL1ToPEProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          exact executeParsedL1ToPEProducer_lm1_frame readState currentState next expression
            noForward hasSingleLineMask usePreIssueMask
            (noLm1 expression (List.mem_filter.mp (by rw [filtered]; simp)).1) executed
      | cons second remaining =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          simp at executed

/-! ## 2. The matrix-MAU/write stage

The stage is the matrix-MAU producer (a family filter over the 1024 MAB
coordinates, each installing four PE files with `commitParsedMatrixMAUPEState`)
followed by `executeParsedMatrixWritesAtMABs`, which preserves every PE
register file.  Only the coordinate `⟨0,0,0,0⟩` at lane `0` reaches PE 0, so the
walk's frame at PE 0 needs the per-coordinate transition only there; every other
coordinate is covered by the fold's "untouched PE" projection. -/

/-- **The matrix-MAU destination loop preserves `.lm1`.** -/
theorem writeParsedMatrixMAUDestinationsAtPE_lm1_frame
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool)
    (output : IntegerALU.Bus) (flags : BitVec 4) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
        hasSingleLineMask output flags destinations files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      have headHyp : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1 :=
        fun bank width pair => noLm1 destination (by simp) bank width pair
      have tailHyp : ∀ item ∈ rest,
          ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
            ParsedOperand.directDestinationBankWidth? item = some (bank, width) →
              bank ≠ PEMemory.Bank.lm1 :=
        fun item member bank width pair =>
          noLm1 item (List.mem_cons_of_mem _ member) bank width pair
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
            rw [ih write.files _ _ nextFiles _ _ tailHyp tail]
            exact writeParsedMslMsrDestination?_lm1_of_ne files _ _ _ flags cycle
              currentState.maskDirective hasSingleLineMask headHyp write h
      all_goals
        simp only [Id.run] at executed
        split at executed
        · split at executed
          · simp at executed
          · simp at executed
          · rename_i h
            exact ih files bar0 bar1 nextFiles nextBar0 nextBar1 tailHyp executed
        · split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            rw [ih write.files _ _ nextFiles _ _ tailHyp tail]
            exact writeParsedMslMsrDestination?_lm1_of_ne files _ _ _ flags cycle
              currentState.maskDirective hasSingleLineMask headHyp write h

/-- **The four-PE loop of one cycle preserves `.lm1` at any target PE.** -/
theorem executeParsedMatrixMAUPEWritesAtCycle_lm1_frame
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (target : Fin 4)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (pes : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate hasSingleLineMask
        cycle buses flags poison pes accum = .ok next →
      (next.files target).lm1 = (accum.files target).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      rfl
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
              cycle poison hasSingleLineMask
              (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe)
              expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
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
              by_cases same : target = pe
              · subst target
                rw [ih _ next tail]
                simp only [beq_self_eq_true, ite_true]
                exact writeParsedMatrixMAUDestinationsAtPE_lm1_frame currentState expression
                  coordinate pe cycle poison hasSingleLineMask
                  (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe)
                  expression.destinations (accum.files pe) (accum.bar0 pe)
                  (accum.bar1 pe) nextFiles nextBar0 nextBar1 noLm1 wrote
              · have different : (target == pe) = false := by simp [same]
                rw [ih _ next tail]
                simp [different]

/-- **The four-cycle loop of one coordinate preserves `.lm1` at any target PE.** -/
theorem executeParsedMatrixMAUWriteCycles_lm1_frame
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (cycles : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
        hasSingleLineMask cycles accum = .ok next →
      (next.files target).lm1 = (accum.files target).lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      rfl
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
              rw [ih nextAccum next executed]
              exact executeParsedMatrixMAUPEWritesAtCycle_lm1_frame currentState expression
                coordinate hasSingleLineMask cycle result.1 result.2.1 result.2.2 target noLm1
                (List.finRange 4) accum nextAccum writes

/-- **The repackaged per-coordinate files preserve `.lm1`.** -/
theorem executeParsedMatrixMAUPEWritesAtMAB_files_lm1
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1)
    (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool)
    (executed : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask = .ok (files, bar0, bar1, outputs, poisoned)) :
    (files target).lm1 = (currentState.peRegisters (physicalPEId coordinate target)).lm1 := by
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
      exact executeParsedMatrixMAUWriteCycles_lm1_frame readState currentState expression
        coordinate hasSingleLineMask target noLm1 (List.finRange 4)
        { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
          bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
          bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
          outputs := fun _ _ => ⟨0, 0⟩
          poisoned := fun _ => false } accum ran

/-- **The per-coordinate transition preserves `.lm1` at each of its four PEs.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_pe_lm1_frame
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (target : Fin 4)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    (next.peRegisters (physicalPEId coordinate target)).lm1 =
      (currentState.peRegisters (physicalPEId coordinate target)).lm1 := by
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
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      rw [commitParsedMatrixMAUPEState_foldl_peRegisters_target coordinate noForward files bar0
        bar1 outputs poisoned target (List.finRange 4) currentState (List.nodup_finRange 4)
        (List.mem_finRange target)]
      exact executeParsedMatrixMAUPEWritesAtMAB_files_lm1 readState currentState expression
        coordinate hasSingleLineMask target noLm1 files bar0 bar1 outputs poisoned ran

/-- **The walk over the MAB coordinates preserves `.lm1` at a fixed PE.** -/
theorem executeParsedMatrixMAUAtMABs_lm1_frame
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedMatrixMAUAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        (next'.peRegisters p).lm1 = (state'.peRegisters p).lm1) →
      (next.peRegisters p).lm1 = (state.peRegisters p).lm1 := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      rw [executeParsedMatrixMAUAtMABs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      rfl
  | cons coordinate rest ih =>
      intro state next executed stepFrame
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
          have head := stepFrame coordinate state middle (by simp) ran
          rw [ih middle next executed
            (fun coordinate' state' next' member ran' =>
              stepFrame coordinate' state' next' (List.mem_cons_of_mem _ member) ran')]
          exact head

/-- **The matrix-MAU producer preserves PE 0's `.lm1`.** -/
theorem executeParsedMatrixMAUProducer_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  cases filtered : expressions.filter parsedExprIsMatrixMAUProducer with
  | nil =>
      rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
      dsimp only at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
          dsimp only at executed
          cases ran : executeParsedMatrixMAUAtMABs readState currentState expression
              allMABCoordinates noForward hasSingleLineMask with
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
              have rowNoLm1 : WelcomeRowHasNoLm1Destination expression :=
                noLm1 expression (List.mem_filter.mp (by rw [filtered]; simp)).1
              have stepFrame : ∀ (coordinate : MABCoordinate) (state' next' : State),
                  coordinate ∈ allMABCoordinates →
                  executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate
                    noForward hasSingleLineMask = .ok next' →
                  (next'.peRegisters welcomePE).lm1 =
                    (state'.peRegisters welcomePE).lm1 := by
                intro coordinate state' next' _ ran'
                by_cases zero : coordinate = ⟨0, 0, 0, 0⟩
                · subst zero
                  have committed := executeParsedMatrixMAUTransitionAtMAB_pe_lm1_frame
                    readState state' next' expression ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask
                    0 rowNoLm1 ran'
                  simpa [physicalPEId, welcomePE] using committed
                · rw [executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame readState state'
                    next' expression coordinate noForward hasSingleLineMask welcomePE
                    (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) ran']
              have walked := executeParsedMatrixMAUAtMABs_lm1_frame readState expression
                noForward hasSingleLineMask welcomePE allMABCoordinates currentState
                afterMAU ran stepFrame
              rw [propagateParsedMatrixMAUPoison_preserves_peRegisters]
              exact walked
      | cons second remaining =>
          rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
          dsimp only at executed
          simp at executed

/-- **The matrix-MAU/write stage preserves PE 0's `.lm1`.** -/
theorem executeParsedMatrixMAUAndWrites_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask with
  | failure =>
      rw [producer] at executed
      simp at executed
  | unknown =>
      rw [producer] at executed
      simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      have committed := executeParsedMatrixMAUProducer_lm1_frame readState currentState afterMAU
        expressions noForward hasSingleLineMask noLm1 producer
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state readState afterMAU next
        allMABCoordinates expressions executed
      rw [frame.1]
      exact committed

/-! ## 3. The two residuals, and the unconditional stage frame -/

/-- **`WelcomePEMatrixMAUStageLm1Frame` is discharged.** -/
theorem welcomePEMatrixMAUStageLm1Frame : WelcomePEMatrixMAUStageLm1Frame :=
  fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedMatrixMAUAndWrites_lm1_frame readState currentState next expressions noForward
      hasSingleLineMask noLm1 executed

/-- **`WelcomePEL1ToPEStageLm1Frame` is discharged.** -/
theorem welcomePEL1ToPEStageLm1Frame : WelcomePEL1ToPEStageLm1Frame :=
  fun readState currentState next expressions noForward hasSingleLineMask usePreIssueMask noLm1
    executed =>
    executeParsedL1ToPEProducers_lm1_frame readState currentState next expressions noForward
      hasSingleLineMask usePreIssueMask noLm1 executed

/-- **The line-level `.lm1` stage frame, unconditionally.** -/
theorem welcomePEStageLm1Frame : WelcomePEStageLm1Frame :=
  welcomePEStageLm1Frame_of_residuals welcomePEMatrixMAUStageLm1Frame
    welcomePEL1ToPEStageLm1Frame

end ProofsLean.MNCore
