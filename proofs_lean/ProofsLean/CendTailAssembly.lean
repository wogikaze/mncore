import ProofsLean.CendTailWalk

set_option maxHeartbeats 400000

/-! # `12.convert-endian`: the final assembly of the line-2/line-3 tail

`CendTailWalk.lean` proves all the mathematical pieces of the tail: the
line-2 and line-3 per-PE core steps, their 4096-PE walks, the line-1 BAR
residual, the line-2 post-slot residual, and the line-3 LM1 commit fold.
This file only wires them together into `CendTailComputationForward`.

`CendLine2AllPEReadyResidual` (after line 2, *every* PE is ready for line 3)
is proved below as the done-PE invariant of the line-2 walk, so `Correct` is
unconditional.  `CendLine2SlotsResidual` is its PE-0 instance. -/

namespace ProofsLean.MNCore

open Issue PEMemory

/-- **The exact residual**: after line 2, every PE satisfies `CendSbslReady`.
`CendLine2SlotsResidual` is the PE-0 instance; this is the invariant of the
line-2 4096-PE walk (`CendLine1SlotsInvariant` is the line-1 analogue). -/
def CendLine2AllPEReadyResidual : Prop :=
  ∀ (input : BitVec 64) (s1 afterTwo : State),
    executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
    executeNormalizedLine (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 =
      .ok afterTwo →
    ∀ pe : PEId, CendSbslReady afterTwo pe

/-- The fields of `afterTwo` that the tail consumes, read off the PE-0 head
step of the line-2 walk and the line-2 residual A. -/
theorem cendAfterTwoFields (input : BitVec 64) (s1 afterTwoPEs : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok s1)
    (walk : executeIntegerProducerLineAtPEs
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      (List.finRange 4096) s1 = .ok afterTwoPEs) :
    (afterTwoPEs.peContext cendPE).bar0 = (s1.peContext cendPE).bar0 ∧
    (afterTwoPEs.peContext cendPE).bar1 = (s1.peContext cendPE).bar1 ∧
    (afterTwoPEs.peRegisters cendPE).lm0 = (s1.peRegisters cendPE).lm0 ∧
    (∀ c : Fin 4, stateForwardingSlots afterTwoPEs cendPE .alu c =
      .known (cendIbslResultBus
        (cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 c))) ∧
    (∀ c : Fin 4, stateForwardingSlots afterTwoPEs cendPE .mau c =
      .known cendMauForwardBus) := by
  obtain ⟨headNext, headPE, hRegs, hCtx, hSlots⟩ :=
    cendLine2_walk_head input s1 afterTwoPEs executed walk
  have filesEq : s1.peRegisters cendPE = cendLine1Files input :=
    cendLine1Files_of_execution input s1 executed
  have slotsEq : ∀ c : Fin 4,
      stateForwardingSlots s1 cendPE .alu c = .known cendImmediateBus := by
    obtain ⟨next1, exec1, _, slotsAll⟩ := cendLine1_next_allPE input
    rw [exec1] at executed
    have same : next1 = s1 := StepResult.ok.inj executed
    rw [← same]
    exact slotsAll cendPE
  obtain ⟨headNext', headCore, headCtx, headLm0, headAlu, headMau⟩ :=
    cendLine2SlotsResidual_proved s1 cendPE (cendLine1Files input) filesEq slotsEq
  have headPE' : executeIntegerProducerLineAtPE
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] s1 cendPE =
      .ok headNext' := by
    simpa [executeIntegerProducerLineAtPE, cendParallel_barWriter,
      cendIbsl_notBARWriter, cendFma_notBARWriter, Bool.false_eq_true, false_or]
      using headCore
  have headEq : headNext = headNext' := StepResult.ok.inj (headPE.symm.trans headPE')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hCtx, headEq, headCtx]
  · rw [hCtx, headEq, headCtx]
  · rw [hRegs, headEq, headLm0, ← filesEq]
  · intro c
    simpa [hSlots, headEq, ← filesEq] using headAlu c
  · intro c
    simpa [hSlots, headEq] using headMau c



/-- **The tail computation from the all-PE readiness residual.** -/
noncomputable def cendTailComputationForward_of_allPEReady
    (readyAll : CendLine2AllPEReadyResidual) :
    ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      CendTailComputationForward input s1 := by
  classical
  intro input s1 executed
  have bar := cendLine1BarResidual_proved input s1 executed
  have line1 : CendLine1Facts input s1 :=
    cendLine1Facts_of_execution input s1 executed bar.1 bar.2
  let afterTwoPEs : State := Classical.choose (cendLine2_walk input s1 executed)
  have walk2 : executeIntegerProducerLineAtPEs
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      (List.finRange 4096) s1 = .ok afterTwoPEs :=
    Classical.choose_spec (cendLine2_walk input s1 executed)
  obtain ⟨hBar0, hBar1, hLm0, hAlu, hMau⟩ :=
    cendAfterTwoFields input s1 afterTwoPEs executed walk2
  let afterTwo : State :=
    { afterTwoPEs with
      hazardClock := afterTwoPEs.hazardClock +
        InstructionLine.cost (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]),
      l1bmTurnaroundValid := false }
  have line2 : executeNormalizedLine
      (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 = .ok afterTwo :=
    cendParallel_lineStep s1 afterTwoPEs walk2
  have aluSlots : ∀ c : Fin 4,
      stateForwardingSlots afterTwo cendPE .alu c =
        .known (cendIbslResultBus
          (cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 c)) := by
    intro c
    exact hAlu c
  have mauSlots : ∀ c : Fin 4,
      stateForwardingSlots afterTwo cendPE .mau c = .known cendMauForwardBus := by
    intro c
    exact hMau c
  have afterTwoBar0 : (afterTwo.peContext cendPE).bar0 = (s1.peContext cendPE).bar0 := by
    simpa [afterTwo] using hBar0
  have afterTwoBar1 : (afterTwo.peContext cendPE).bar1 = (s1.peContext cendPE).bar1 := by
    simpa [afterTwo] using hBar1
  have afterTwoLm0 : (afterTwo.peRegisters cendPE).lm0 = (s1.peRegisters cendPE).lm0 := by
    simpa [afterTwo] using hLm0
  have ready : ∀ pe : PEId, CendSbslReady afterTwo pe :=
    readyAll input s1 afterTwo executed line2
  let afterThreePEs : State := Classical.choose (cendLine3_walk afterTwo ready)
  have walk3 : executeIntegerProducerLineAtPEs
      [cendSbslExpr.normalize.toParsed] (List.finRange 4096) afterTwo = .ok afterThreePEs :=
    Classical.choose_spec (cendLine3_walk afterTwo ready)
  let afterThree : State :=
    { afterThreePEs with
      hazardClock := afterThreePEs.hazardClock +
        InstructionLine.cost (.pe [cendSbslExpr.normalize]),
      l1bmTurnaroundValid := false }
  have line3 : executeNormalizedLine (.pe [cendSbslExpr.normalize]) afterTwo =
      .ok afterThree :=
    cendSbsl_lineStep afterTwo afterThreePEs walk3
  have directiveEq : afterTwo.maskDirective =
      rustSimulatorInitialState.maskDirective := by
    have h2 := (executeIntegerProducerLineAtPEs_maskDirective_hazardClock
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      (List.finRange 4096) s1 afterTwoPEs walk2).1
    have h1 : s1.maskDirective = (cendInitialState input).maskDirective := by
      obtain ⟨next1, exec1, _, _, _, _, hmask, _, _⟩ := cendLine1_next input
      have executed' := executed
      rw [exec1] at executed'
      have same : next1 = s1 := StepResult.ok.inj executed'
      rw [← same]
      exact hmask
    simpa [afterTwo, h2, h1, cendInitialState_maskDirective]
  have afterThreeLm1 : (afterThree.peRegisters cendPE).lm1 =
      cendSbslLm1 (afterTwo.peRegisters cendPE).lm1
        (fun c => byteSwap32
          (cendLm0Word (afterTwo.peRegisters cendPE).lm0
            (afterTwo.peContext cendPE).bar0 c)) := by
    have bar1zero : (afterTwo.peContext cendPE).bar1 = 0 := by
      rw [afterTwoBar1, bar.2]
    obtain ⟨headThree, _headPE3, hRegs3, hLm1⟩ :=
      cendLine3_walk_head afterTwo afterThreePEs walk3 directiveEq bar1zero
        (ready cendPE)
    rw [show (afterThree.peRegisters cendPE) = (afterThreePEs.peRegisters cendPE) from rfl,
      hRegs3]
    exact hLm1
  exact ⟨line1, afterTwo, line2, aluSlots, mauSlots, afterTwoBar0, afterTwoBar1,
    afterTwoLm0, afterThree, line3, afterThreeLm1⟩

/-- **`CendTailForwardResidual` from the all-PE readiness residual.** -/
theorem cendTailForwardResidual_of_allPEReady
    (readyAll : CendLine2AllPEReadyResidual) : CendTailForwardResidual :=
  fun input s1 line1 => ⟨cendTailComputationForward_of_allPEReady readyAll input s1 line1⟩

/-- **`Correct cendSealedMachine cendSpec cendAnswer`**, conditional on the
all-PE readiness of line 2. -/
theorem cendAnswerCorrect_of_allPEReady
    (readyAll : CendLine2AllPEReadyResidual) :
    ProofsLean.Correct cendSealedMachine cendSpec cendAnswer :=
  cendAnswerCorrect_of_forwardResidual (cendTailForwardResidual_of_allPEReady readyAll)

#print axioms cendAfterTwoFields
#print axioms cendTailComputationForward_of_allPEReady
#print axioms cendTailForwardResidual_of_allPEReady
#print axioms cendAnswerCorrect_of_allPEReady


/-! ## The all-PE readiness invariant of the line-2 walk -/

/-- Frame the forwarded slots across a step at another PE. -/
theorem cendSlots_frame {state next : State} {q : PEId} {unit : Forwarding.Unit}
    {cycle : Fin 4}
    (fwd : next.forwarding q = state.forwarding q)
    (valid : next.forwardingValid q = state.forwardingValid q) :
    stateForwardingSlots next q unit cycle = stateForwardingSlots state q unit cycle := by
  simp only [stateForwardingSlots]
  rw [valid, fwd]

/-- Frame `CendSbslReady` across a step at another PE. -/
theorem cendSbslReady_frame {state next : State} {q : PEId}
    (regs : next.peRegisters q = state.peRegisters q)
    (fwd : next.forwarding q = state.forwarding q)
    (valid : next.forwardingValid q = state.forwardingValid q)
    (ctx : next.peContext q = state.peContext q)
    (ready : CendSbslReady state q) : CendSbslReady next q := by
  refine ⟨?_, ?_⟩
  · intro cycle
    rw [cendSlots_frame fwd valid, regs, ctx]
    exact ready.1 cycle
  · intro cycle
    rw [cendSlots_frame fwd valid]
    exact ready.2 cycle

/-- During line 2's walk, pending PEs still have the line-1 committed file and
the immediate `.alu` bus; done PEs satisfy `CendSbslReady`. -/
structure CendLine2ReadyInvariant (input : BitVec 64) (pending : List PEId)
    (state : State) : Prop where
  filesPending : ∀ pe : PEId, pe ∈ pending → state.peRegisters pe = cendLine1Files input
  slotsPending : ∀ pe : PEId, pe ∈ pending → ∀ cycle : Fin 4,
    stateForwardingSlots state pe .alu cycle = .known cendImmediateBus
  readyDone : ∀ pe : PEId, pe ∉ pending → CendSbslReady state pe

theorem cendLine2ReadyInvariant_initial (input : BitVec 64) (s1 : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok s1) :
    CendLine2ReadyInvariant input (List.finRange 4096) s1 := by
  obtain ⟨next1, exec1, filesAll, slotsAll⟩ := cendLine1_next_allPE input
  have same : next1 = s1 := by
    have executed' := executed
    rw [exec1] at executed'
    exact StepResult.ok.inj executed'
  refine ⟨?_, ?_, ?_⟩
  · intro pe _mem
    rw [← same]
    exact filesAll pe
  · intro pe _mem cycle
    rw [← same]
    exact slotsAll pe cycle
  · intro pe absent
    exact absurd (List.mem_finRange pe) absent

theorem cendLine2Ready_head (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendLine1Files input)
    (slotsEq : ∀ cycle : Fin 4,
      stateForwardingSlots state pe .alu cycle = .known cendImmediateBus) :
    ∃ next : State,
      executeIntegerProducerLineAtPE
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] state pe =
        .ok next ∧
      CendSbslReady next pe := by
  obtain ⟨next, headCore, headCtx, headLm0, headAlu, headMau⟩ :=
    cendLine2SlotsResidual_proved state pe (cendLine1Files input) filesEq slotsEq
  have headPE : executeIntegerProducerLineAtPE
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] state pe =
      .ok next := by
    simpa [executeIntegerProducerLineAtPE, cendParallel_barWriter,
      cendIbsl_notBARWriter, cendFma_notBARWriter, Bool.false_eq_true, false_or]
      using headCore
  refine ⟨next, headPE, ?_, ?_⟩
  · intro cycle
    rw [headLm0, headCtx]
    exact headAlu cycle
  · intro cycle
    exact headMau cycle

theorem executeIntegerProducerLineAtPEs_cendLine2_walk_ready
    (input : BitVec 64) (pending : List PEId) (state : State)
    (nodup : pending.Nodup)
    (inv : CendLine2ReadyInvariant input pending state) :
    ∃ next : State,
      executeIntegerProducerLineAtPEs
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
        pending state = .ok next ∧
      CendLine2ReadyInvariant input [] next := by
  induction pending generalizing state with
  | nil =>
      exact ⟨state, by simp [executeIntegerProducerLineAtPEs], by
        refine ⟨?_, ?_, ?_⟩
        · intro pe mem; simp at mem
        · intro pe mem; simp at mem
        · intro pe _; exact inv.readyDone pe (by simp)⟩
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      have peMem : pe ∈ pe :: rest := by simp
      obtain ⟨middle, headExecuted, headReady⟩ :=
        cendLine2Ready_head input state pe
          (inv.filesPending pe peMem) (inv.slotsPending pe peMem)
      have middleInv : CendLine2ReadyInvariant input rest middle := by
        refine ⟨?_, ?_, ?_⟩
        · intro q mem
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
            state middle pe q different headExecuted
          rw [frame.1]
          exact inv.filesPending q (List.mem_cons_of_mem pe mem)
        · intro q mem cycle
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
            state middle pe q different headExecuted
          rw [cendSlots_frame frame.2.1 frame.2.2.1]
          exact inv.slotsPending q (List.mem_cons_of_mem pe mem) cycle
        · intro q notMemRest
          by_cases same : q = pe
          · subst same
            exact headReady
          · have notMemCons : q ∉ pe :: rest := by
              intro member
              rcases List.mem_cons.mp member with head | tail
              · exact same head
              · exact notMemRest tail
            have stateReady := inv.readyDone q notMemCons
            have frame := executeIntegerProducerLineAtPE_peFields_other
              [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
              state middle pe q same headExecuted
            exact cendSbslReady_frame frame.1 frame.2.1 frame.2.2.1 frame.2.2.2 stateReady
      obtain ⟨next, tailExecuted, tailInv⟩ := ih middle restNodup middleInv
      refine ⟨next, ?_, tailInv⟩
      have unfoldEq : executeIntegerProducerLineAtPEs
          [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
          (pe :: rest) state =
          executeIntegerProducerLineAtPEs
            [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
            rest middle := by
        conv_lhs => unfold executeIntegerProducerLineAtPEs
        rw [headExecuted]
      rw [unfoldEq]
      exact tailExecuted

/-- **`CendLine2AllPEReadyResidual`, unconditionally.** -/
theorem cendLine2AllPEReadyResidual_proved : CendLine2AllPEReadyResidual := by
  intro input s1 afterTwo executed line2
  obtain ⟨afterTwoPEs, walk2⟩ := cendLine2_walk input s1 executed
  have lineStep := cendParallel_lineStep s1 afterTwoPEs walk2
  have afterTwoEq : afterTwo = { afterTwoPEs with
      hazardClock := afterTwoPEs.hazardClock +
        InstructionLine.cost (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]),
      l1bmTurnaroundValid := false } :=
    StepResult.ok.inj (line2.symm.trans lineStep)
  obtain ⟨afterTwoPEs', walk2', inv⟩ :=
    executeIntegerProducerLineAtPEs_cendLine2_walk_ready input (List.finRange 4096) s1
      (List.nodup_finRange 4096) (cendLine2ReadyInvariant_initial input s1 executed)
  have same : afterTwoPEs = afterTwoPEs' := StepResult.ok.inj (walk2.symm.trans walk2')
  intro pe
  rw [afterTwoEq, same]
  exact inv.readyDone pe (by simp)

/-- **`Correct cendSealedMachine cendSpec cendAnswer`, unconditionally.** -/
theorem cendAnswerCorrect : ProofsLean.Correct cendSealedMachine cendSpec cendAnswer :=
  cendAnswerCorrect_of_allPEReady cendLine2AllPEReadyResidual_proved

#print axioms cendLine2AllPEReadyResidual_proved
#print axioms cendAnswerCorrect

end ProofsLean.MNCore
