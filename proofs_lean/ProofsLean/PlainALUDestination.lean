import ProofsLean.WelcomePlainShape

/-! # State-general destination analysis of the plain integer-ALU cycle

The plain integer-ALU executor (`prepareParsedIntegerALUExprCycle` and
`prepareParsedIntegerALUCycles`) reads memory *data* and *forwarding* slots, so
its prepared writes differ between two register files.  What does **not**
depend on the data is the **destination** of every prepared write: the branch
selection of the cycle takes only

* the parsed expression,
* `files.maskRegisters` (for the mask / OMR / BAR / constant lowerings),
* the execution control, the mask directive and the four boolean flags,

and each branch's prepared write takes its destination from the lowering result
(`some accesses.destination`, `some accesses.memory`) or has no destination at
all (OMR, no-write, BAR, mask-input and the constant-producer write).

This module proves that fact in the exact form needed to *transfer* a write
shape from one initial state to another:

* `prepareParsedIntegerALUExprCycle_destination_state_general` — two successful
  cycle runs on any two register files with the **same mask registers** produce
  the **same list of destinations**;
* `prepareParsedIntegerALUCycles_destination_state_general` — the same for the
  four-cycle accumulation `prepareParsedIntegerALUCycles` (the write lists are
  appended, so the accumulated destinations are equal whenever the initial
  accumulators have equal destinations).

Neither statement mentions a particular machine, initial state, problem or
input, so they apply to every problem whose one-line argument needs the write
destinations at a non-zero input (the Welcome chain only provides the write
shapes at the all-zero initial state).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Destination projections of the prepared-write constructors -/

/-- The destinations of the replicated writes of a multiple-destination
lowering: exactly the lowered accesses' destinations, in order. -/
theorem replicatePreparedIntegerResult_destination_map
    (accesses : List ParsedMaskedIntegerAccesses) (result : PreparedParsedMaskedWrite) :
    (replicatePreparedIntegerResult accesses result).map (fun w => w.destination) =
      accesses.map (fun access => some access.destination) := by
  induction accesses with
  | nil => rfl
  | cons access rest ih => simp [replicatePreparedIntegerResult, ih]

/-- The destination a constant-destination operand contributes (none for OMR
mask-register writes and no-writes). -/
def ParsedConstantDestination.destinationOption :
    ParsedConstantDestination → Option DirectMemoryAccess
  | .memory accesses => some accesses.destination
  | .maskRegister _ => none
  | .noWrite => none

/-- The prepared writes of a constant-destination list have exactly the
destinations of that list. -/
theorem prepareParsedMaskedConstantWrites_destination_map
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (writes : List PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets = .ok writes) :
    writes.map (fun w => w.destination) =
      targets.map ParsedConstantDestination.destinationOption := by
  induction targets generalizing writes with
  | nil =>
      simp [prepareParsedMaskedConstantWrites] at prepared
      subst prepared
      rfl
  | cons target rest ih =>
      cases head : prepareParsedConstantTarget files cycle target with
      | failure => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | unknown => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | ok headWrite =>
          cases tail : prepareParsedMaskedConstantWrites files cycle rest with
          | failure => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | unknown => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | ok writes' =>
              simp only [prepareParsedMaskedConstantWrites, head, tail, StepResult.ok.injEq]
                at prepared
              subst prepared
              have tailDestinations := ih writes' tail
              cases target with
              | memory accesses =>
                  have destination : headWrite.destination = some accesses.destination :=
                    prepareParsedMaskedWrite_destination files accesses false headWrite head
                  simp only [List.map_cons, destination, tailDestinations,
                    ParsedConstantDestination.destinationOption]
              | maskRegister entry =>
                  have destination : headWrite.destination = none := by
                    simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at head
                    subst headWrite
                    rfl
                  simp only [List.map_cons, destination, tailDestinations,
                    ParsedConstantDestination.destinationOption]
              | noWrite =>
                  have destination : headWrite.destination = none := by
                    simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at head
                    subst headWrite
                    rfl
                  simp only [List.map_cons, destination, tailDestinations,
                    ParsedConstantDestination.destinationOption]

/-! ## 2. The forwarding update never fails -/

/-- `updateParsedIntegerALUForwardingCycle` succeeds on every prepared write: it
either keeps the old slots (`noForward`) or installs the write's bus. -/
theorem updateParsedIntegerALUForwardingCycle_ok_exists
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (write : PreparedParsedMaskedWrite) (noForward : Bool) :
    ∃ slots, updateParsedIntegerALUForwardingCycle old cycle (.ok write) noForward = .ok slots := by
  rw [updateParsedIntegerALUForwardingCycle_semantics]
  by_cases same : noForward
  · exact ⟨old, by rw [if_pos same]⟩
  · exact ⟨_, by rw [if_neg same]⟩

/-! ## 3. The constant-producer tail

The `.zero` / `.immediate` branch appends a destination-free producer write to
the constant-target writes.  This tail never reads any register file, so its
destination list is `destinationWrites ++ [none]` for every request and flush
selection. -/

theorem constantWritesTail_destination
    (destinationWrites : List PreparedParsedMaskedWrite) (cycle : Fin 4)
    (request : ParsedExecutionRequest) (flushResult : Option (Option PEWordSelection))
    (reduced noForward : Bool) (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (h : (match flushResult with
          | none => (StepResult.unknown : StepResult
              (List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots))
          | some flushSelection =>
              let output := evaluateParsedExecutionRequest request ⟨0, 0⟩ ⟨0, 0⟩ reduced
              let outputBus := parsedOutputAfterFlush flushSelection output.value
              let producerWrite : PreparedParsedMaskedWrite :=
                ⟨none, none, unpackALUBus outputBus, ⟨BitVec.allOnes 4, true⟩⟩
              match updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok producerWrite)
                  noForward with
              | .failure => StepResult.failure
              | .unknown => StepResult.unknown
              | .ok updatedSlots => .ok (destinationWrites ++ [producerWrite], updatedSlots))
        = .ok (writes, slots)) :
    writes.map (fun w => w.destination) =
      destinationWrites.map (fun w => w.destination) ++ [none] := by
  cases hf : flushResult with
  | none => simp [hf] at h
  | some flushSelection =>
      simp only [hf] at h
      obtain ⟨slots', hupd⟩ :=
        updateParsedIntegerALUForwardingCycle_ok_exists nextSlots cycle
          ⟨none, none,
            unpackALUBus (parsedOutputAfterFlush flushSelection
              (evaluateParsedExecutionRequest request ⟨0, 0⟩ ⟨0, 0⟩ reduced).value),
            ⟨BitVec.allOnes 4, true⟩⟩ noForward
      rw [hupd] at h
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simp

/-- **The `.zero` / `.immediate` branch.**  Both constant ops produce the same
destination list at any two register files with the same mask registers. -/
theorem prepareParsedIntegerALUExprCycle_constant_destination
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (hA : prepareParsedIntegerALUExprCycle filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (hB : prepareParsedIntegerALUExprCycle filesB oldSlotsB nextSlotsB expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  unfold prepareParsedIntegerALUExprCycle at hA hB
  rw [← maskEq] at hB
  rcases constant with hz | ⟨payload, sparse, hi⟩
  · simp only [hz, ParsedOp.executionRequest] at hA hB
    cases dc : ParsedExpr.toDirectMaskedConstantWrites? expression filesA.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord with
    | none => simp_all
    | some targets =>
        simp only [dc] at hA hB
        cases cA : prepareParsedMaskedConstantWrites filesA cycle targets with
        | failure => simp_all
        | unknown => simp_all
        | ok destinationWritesA =>
            cases cB : prepareParsedMaskedConstantWrites filesB cycle targets with
            | failure => simp_all
            | unknown => simp_all
            | ok destinationWritesB =>
                simp only [cA, cB] at hA hB
                generalize fr : resolveFlushSelection? expression.flush filesA.maskRegisters
                  cycle = flushResult at hA hB
                have eqA := constantWritesTail_destination destinationWritesA cycle _ flushResult
                  reduced noForward nextSlotsA writesA slotsA hA
                have eqB := constantWritesTail_destination destinationWritesB cycle _ flushResult
                  reduced noForward nextSlotsB writesB slotsB hB
                rw [eqA, eqB,
                  prepareParsedMaskedConstantWrites_destination_map filesA cycle targets
                    destinationWritesA cA,
                  prepareParsedMaskedConstantWrites_destination_map filesB cycle targets
                    destinationWritesB cB]
  · simp only [hi, ParsedOp.executionRequest] at hA hB
    cases dc : ParsedExpr.toDirectMaskedConstantWrites? expression filesA.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord with
    | none => simp_all
    | some targets =>
        simp only [dc] at hA hB
        cases cA : prepareParsedMaskedConstantWrites filesA cycle targets with
        | failure => simp_all
        | unknown => simp_all
        | ok destinationWritesA =>
            cases cB : prepareParsedMaskedConstantWrites filesB cycle targets with
            | failure => simp_all
            | unknown => simp_all
            | ok destinationWritesB =>
                simp only [cA, cB] at hA hB
                generalize fr : resolveFlushSelection? expression.flush filesA.maskRegisters
                  cycle = flushResult at hA hB
                have eqA := constantWritesTail_destination destinationWritesA cycle _ flushResult
                  reduced noForward nextSlotsA writesA slotsA hA
                have eqB := constantWritesTail_destination destinationWritesB cycle _ flushResult
                  reduced noForward nextSlotsB writesB slotsB hB
                rw [eqA, eqB,
                  prepareParsedMaskedConstantWrites_destination_map filesA cycle targets
                    destinationWritesA cA,
                  prepareParsedMaskedConstantWrites_destination_map filesB cycle targets
                    destinationWritesB cB]


/-! ## 4. The state-general destination congruence of one cycle -/

/-- **State-general destination congruence of one plain integer-ALU cycle.**
Two successful cycle runs on any two register files with the same mask registers
prepare the same list of destinations.  The data (and the forwarding slots) may
differ arbitrarily; only `maskRegisters` matters, because the branch selection
and the lowerings read `files.maskRegisters` and nothing else.

Every branch is closed by the destination provenance of the prepared-write
constructor it uses (`prepareParsedMaskedWriteWithForwarding_destination`, the
`..._destination_none` lemmas for the OMR / no-write / BAR / mask-input
branches, the two mixed memory/OMR shape lemmas, and the constant-target map
lemma). -/
theorem prepareParsedIntegerALUExprCycle_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (hA : prepareParsedIntegerALUExprCycle filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (hB : prepareParsedIntegerALUExprCycle filesB oldSlotsB nextSlotsB expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  unfold prepareParsedIntegerALUExprCycle at hA hB
  cases hop : expression.op with
  | «alu» name precision unsigned arg =>
      simp only [hop] at hA hB
      rw [← maskEq] at hB
      cases d1 : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression filesA.maskRegisters
          control.directive hasSingleLineMask control.context.group control.context.l2b
          control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
          control.context.bar1 control.context.tWord with
      | some accesses =>
          simp only [d1] at hA hB
          cases pA : prepareParsedMaskedWriteWithForwarding filesA oldSlotsA cycle accesses reduced with
          | failure => simp_all
          | unknown => simp_all
          | ok writeA =>
              cases pB : prepareParsedMaskedWriteWithForwarding filesB oldSlotsB cycle accesses reduced with
              | failure => simp_all
              | unknown => simp_all
              | ok writeB =>
                  obtain ⟨slotsA', hupdA⟩ :=
                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeA noForward
                  obtain ⟨slotsB', hupdB⟩ :=
                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB cycle writeB noForward
                  simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
                  rw [← hA.1, ← hB.1]
                  simp only [List.map_cons, List.map_nil]
                  rw [prepareParsedMaskedWriteWithForwarding_destination filesA oldSlotsA cycle
                        accesses reduced writeA pA,
                      prepareParsedMaskedWriteWithForwarding_destination filesB oldSlotsB cycle
                        accesses reduced writeB pB]
      | none =>
          simp only [d1] at hA hB
          cases d2 : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression filesA.maskRegisters
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | some accesses =>
              rcases accesses with _ | ⟨access, rest⟩
              · simp_all
              · simp only [d2] at hA hB
                cases pA : prepareParsedMaskedWriteWithForwarding filesA oldSlotsA cycle access reduced with
                | failure => simp_all
                | unknown => simp_all
                | ok writeA =>
                    cases pB : prepareParsedMaskedWriteWithForwarding filesB oldSlotsB cycle access reduced with
                    | failure => simp_all
                    | unknown => simp_all
                    | ok writeB =>
                        obtain ⟨slotsA', hupdA⟩ :=
                          updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeA
                            noForward
                        obtain ⟨slotsB', hupdB⟩ :=
                          updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB cycle writeB
                            noForward
                        simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
                        rw [← hA.1, ← hB.1]
                        simp only [List.map_cons]
                        rw [replicatePreparedIntegerResult_destination_map,
                            replicatePreparedIntegerResult_destination_map,
                            prepareParsedMaskedWriteWithForwarding_destination filesA oldSlotsA
                              cycle access reduced writeA pA,
                            prepareParsedMaskedWriteWithForwarding_destination filesB oldSlotsB
                              cycle access reduced writeB pB]
          | none =>
              simp only [d2] at hA hB
              cases d3 : parsedIntegerMaskExprAccessesInLine? expression filesA.maskRegisters
                  control.directive hasSingleLineMask control.context.pe cycle
                  control.context.bar0 control.context.bar1 control.context.tWord with
              | some accesses =>
                  simp only [d3] at hA hB
                  cases rf : resolveFlushSelection? expression.flush filesA.maskRegisters cycle with
                  | none => simp_all
                  | some flushSelection =>
                      simp only [rf] at hA hB
                      cases pA : prepareParsedIntegerMaskALUWriteWithForwarding filesA oldSlotsA
                          cycle accesses flushSelection reduced with
                      | failure => simp_all
                      | unknown => simp_all
                      | ok writeA =>
                          cases pB : prepareParsedIntegerMaskALUWriteWithForwarding filesB oldSlotsB
                              cycle accesses flushSelection reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeB =>
                              obtain ⟨slotsA', hupdA⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeA noForward
                              obtain ⟨slotsB', hupdB⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB cycle
                                  writeB noForward
                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq]
                                at hA hB
                              rw [← hA.1, ← hB.1]
                              simp only [List.map_cons, List.map_nil]
                              rw [prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
                                    filesA oldSlotsA cycle accesses flushSelection reduced writeA pA,
                                  prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
                                    filesB oldSlotsB cycle accesses flushSelection reduced writeB pB]
              | none =>
                  simp only [d3] at hA hB
                  cases d4 : parsedIntegerNoWriteExprAccessesInLine? expression filesA.maskRegisters
                      control.context.pe cycle control.context.group control.context.l2b
                      control.context.l1b control.context.mab control.context.bar0
                      control.context.bar1 control.context.tWord with
                  | some accesses =>
                      simp only [d4] at hA hB
                      cases pA : prepareParsedIntegerNoWriteALUWithForwarding filesA oldSlotsA
                          cycle accesses reduced with
                      | failure => simp_all
                      | unknown => simp_all
                      | ok writeA =>
                          cases pB : prepareParsedIntegerNoWriteALUWithForwarding filesB oldSlotsB
                              cycle accesses reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeB =>
                              obtain ⟨slotsA', hupdA⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeA noForward
                              obtain ⟨slotsB', hupdB⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB cycle
                                  writeB noForward
                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq]
                                at hA hB
                              rw [← hA.1, ← hB.1]
                              simp only [List.map_cons, List.map_nil]
                              rw [prepareParsedIntegerNoWriteALUWithForwarding_destination_none
                                    filesA oldSlotsA cycle accesses reduced writeA pA,
                                  prepareParsedIntegerNoWriteALUWithForwarding_destination_none
                                    filesB oldSlotsB cycle accesses reduced writeB pB]
                  | none =>
                      simp only [d4] at hA hB
                      cases d5 : parsedIntegerBarExprAccessesInLine? expression filesA.maskRegisters
                          control.directive hasSingleLineMask control.context.group
                          control.context.l2b control.context.l1b control.context.mab
                          control.context.pe cycle control.context.bar0 control.context.bar1
                          control.context.tWord with
                      | some accesses =>
                          simp only [d5] at hA hB
                          cases pA : prepareParsedIntegerBarALUWithForwarding filesA oldSlotsA
                              cycle accesses reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeA =>
                              cases pB : prepareParsedIntegerBarALUWithForwarding filesB oldSlotsB
                                  cycle accesses reduced with
                              | failure => simp_all
                              | unknown => simp_all
                              | ok writeB =>
                                  obtain ⟨slotsA', hupdA⟩ :=
                                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                      writeA noForward
                                  obtain ⟨slotsB', hupdB⟩ :=
                                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB cycle
                                      writeB noForward
                                  simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                    Prod.mk.injEq] at hA hB
                                  rw [← hA.1, ← hB.1]
                                  simp only [List.map_cons, List.map_nil]
                                  rw [prepareParsedIntegerBarALUWithForwarding_destination_none
                                        filesA oldSlotsA cycle accesses reduced writeA pA,
                                      prepareParsedIntegerBarALUWithForwarding_destination_none
                                        filesB oldSlotsB cycle accesses reduced writeB pB]
                      | none =>
                          simp only [d5] at hA hB
                          cases d6 : parsedIntegerMaskInputExprAccessesInLine? expression
                              filesA.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord with
                          | some accesses =>
                              simp only [d6] at hA hB
                              cases rf : resolveFlushSelection? expression.flush filesA.maskRegisters
                                  cycle with
                              | none => simp_all
                              | some flushSelection =>
                                  simp only [rf] at hA hB
                                  cases pA : prepareParsedIntegerMaskInputALUWriteWithForwarding
                                      filesA oldSlotsA cycle accesses flushSelection reduced with
                                  | failure => simp_all
                                  | unknown => simp_all
                                  | ok writeA =>
                                      cases pB : prepareParsedIntegerMaskInputALUWriteWithForwarding
                                          filesB oldSlotsB cycle accesses flushSelection reduced with
                                      | failure => simp_all
                                      | unknown => simp_all
                                      | ok writeB =>
                                          obtain ⟨slotsA', hupdA⟩ :=
                                            updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA
                                              cycle writeA noForward
                                          obtain ⟨slotsB', hupdB⟩ :=
                                            updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsB
                                              cycle writeB noForward
                                          simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                            Prod.mk.injEq] at hA hB
                                          rw [← hA.1, ← hB.1]
                                          simp only [List.map_cons, List.map_nil]
                                          rw [prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none
                                                filesA oldSlotsA cycle accesses flushSelection reduced
                                                writeA pA,
                                              prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none
                                                filesB oldSlotsB cycle accesses flushSelection reduced
                                                writeB pB]
                          | none =>
                              simp only [d6] at hA hB
                              cases d7 : parsedIntegerMaskMemoryThenInputExprAccessesInLine?
                                  expression filesA.maskRegisters control.directive
                                  hasSingleLineMask control.context.group control.context.l2b
                                  control.context.l1b control.context.mab control.context.pe cycle
                                  control.context.bar0 control.context.bar1 control.context.tWord with
                              | some accesses =>
                                  simp only [d7] at hA hB
                                  cases rf : resolveFlushSelection? expression.flush
                                      filesA.maskRegisters cycle with
                                  | none => simp_all
                                  | some flushSelection =>
                                      simp only [rf] at hA hB
                                      cases pA : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                          filesA oldSlotsA cycle accesses flushSelection reduced with
                                      | failure => simp_all
                                      | unknown => simp_all
                                      | ok resultA =>
                                          obtain ⟨memoryWritesA, omrWriteA⟩ := resultA
                                          cases pB : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                              filesB oldSlotsB cycle accesses flushSelection reduced with
                                          | failure => simp_all
                                          | unknown => simp_all
                                          | ok resultB =>
                                              obtain ⟨memoryWritesB, omrWriteB⟩ := resultB
                                              obtain ⟨slotsA', hupdA⟩ :=
                                                updateParsedIntegerALUForwardingCycle_ok_exists
                                                  nextSlotsA cycle omrWriteA noForward
                                              obtain ⟨slotsB', hupdB⟩ :=
                                                updateParsedIntegerALUForwardingCycle_ok_exists
                                                  nextSlotsB cycle omrWriteB noForward
                                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                                Prod.mk.injEq] at hA hB
                                              rw [← hA.1, ← hB.1]
                                              obtain ⟨busA, flagsA, memWritesA, omrEqA⟩ :=
                                                prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape
                                                  filesA oldSlotsA cycle accesses flushSelection
                                                  reduced memoryWritesA omrWriteA pA
                                              obtain ⟨busB, flagsB, memWritesB, omrEqB⟩ :=
                                                prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape
                                                  filesB oldSlotsB cycle accesses flushSelection
                                                  reduced memoryWritesB omrWriteB pB
                                              rw [memWritesA, omrEqA, memWritesB, omrEqB]
                                              simp
                              | none =>
                                  simp only [d7] at hA hB
                                  cases d8 : parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                      expression filesA.maskRegisters control.directive
                                      hasSingleLineMask control.context.group control.context.l2b
                                      control.context.l1b control.context.mab control.context.pe
                                      cycle control.context.bar0 control.context.bar1
                                      control.context.tWord with
                                  | some accesses =>
                                      simp only [d8] at hA hB
                                      cases rf : resolveFlushSelection? expression.flush
                                          filesA.maskRegisters cycle with
                                      | none => simp_all
                                      | some flushSelection =>
                                          simp only [rf] at hA hB
                                          cases pA : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                              filesA oldSlotsA cycle accesses control.directive
                                              hasSingleLineMask flushSelection reduced with
                                          | failure => simp_all
                                          | unknown => simp_all
                                          | ok resultA =>
                                              obtain ⟨writesA', producerA⟩ := resultA
                                              cases pB : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                                  filesB oldSlotsB cycle accesses control.directive
                                                  hasSingleLineMask flushSelection reduced with
                                              | failure => simp_all
                                              | unknown => simp_all
                                              | ok resultB =>
                                                  obtain ⟨writesB', producerB⟩ := resultB
                                                  obtain ⟨slotsA', hupdA⟩ :=
                                                    updateParsedIntegerALUForwardingCycle_ok_exists
                                                      nextSlotsA cycle producerA noForward
                                                  obtain ⟨slotsB', hupdB⟩ :=
                                                    updateParsedIntegerALUForwardingCycle_ok_exists
                                                      nextSlotsB cycle producerB noForward
                                                  simp only [pA, pB, hupdA, hupdB,
                                                    StepResult.ok.injEq, Prod.mk.injEq] at hA hB
                                                  rw [← hA.1, ← hB.1]
                                                  obtain ⟨busA, flagsA, selectionA, memWritesA, omrEqA⟩ :=
                                                    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape
                                                      filesA oldSlotsA cycle accesses
                                                      control.directive hasSingleLineMask
                                                      flushSelection reduced writesA' producerA pA
                                                  obtain ⟨busB, flagsB, selectionB, memWritesB, omrEqB⟩ :=
                                                    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape
                                                      filesB oldSlotsB cycle accesses
                                                      control.directive hasSingleLineMask
                                                      flushSelection reduced writesB' producerB pB
                                                  rw [memWritesA, memWritesB]
                                                  simp [omrEqA, omrEqB]
                                  | none =>
                                      simp only [d8] at hA hB
                                      split at hA <;> simp_all
  | zero =>
      exact prepareParsedIntegerALUExprCycle_constant_destination filesA filesB oldSlotsA oldSlotsB
        nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced cycle
        writesA slotsA writesB slotsB maskEq (Or.inl hop) hA hB
  | immediate value unsigned =>
      exact prepareParsedIntegerALUExprCycle_constant_destination filesA filesB oldSlotsA oldSlotsB
        nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced cycle
        writesA slotsA writesB slotsB maskEq (Or.inr ⟨value, unsigned, hop⟩) hA hB
  | mau precision matrix kind half round => simp only [hop] at hA; simp at hA
  | matrixWrite precision => simp only [hop] at hA; simp at hA
  | matrixRead precision => simp only [hop] at hA; simp at hA
  | wait tag => simp only [hop] at hA; simp at hA
  | noforward => simp only [hop] at hA; simp at hA
  | l1bm op => simp only [hop] at hA; simp at hA
  | l2bm op => simp only [hop] at hA; simp at hA


/-! ## 5. The four-cycle accumulation -/

/-- **State-general destination congruence of the four-cycle accumulation.**
If the two accumulators start with the same destinations and both runs succeed,
the resulting write lists have the same destinations: each cycle is covered by
`prepareParsedIntegerALUExprCycle_destination_state_general`, and the write
lists are appended. -/
theorem prepareParsedIntegerALUCycles_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    ∀ (cycles : List (Fin 4))
      (writesA : List PreparedParsedMaskedWrite)
      (startSlotsA : ProofsLean.MNCore.Forwarding.Slots)
      (writesB : List PreparedParsedMaskedWrite)
      (startSlotsB : ProofsLean.MNCore.Forwarding.Slots)
      (resultA resultB : List PreparedParsedMaskedWrite ×
        ProofsLean.MNCore.Forwarding.Slots),
      writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) →
      prepareParsedIntegerALUCycles filesA oldSlotsA expression control hasSingleLineMask
        noForward reduced cycles writesA startSlotsA = .ok resultA →
      prepareParsedIntegerALUCycles filesB oldSlotsB expression control hasSingleLineMask
        noForward reduced cycles writesB startSlotsB = .ok resultB →
      resultA.1.map (fun w => w.destination) =
        resultB.1.map (fun w => w.destination) := by
  intro cycles
  induction cycles with
  | nil =>
      intro writesA startSlotsA writesB startSlotsB resultA resultB writesEq hA hB
      simp only [prepareParsedIntegerALUCycles, StepResult.ok.injEq] at hA hB
      rw [← hA, ← hB]
      exact writesEq
  | cons c rest ih =>
      intro writesA startSlotsA writesB startSlotsB resultA resultB writesEq hA hB
      simp only [prepareParsedIntegerALUCycles] at hA hB
      cases cA : prepareParsedIntegerALUExprCycle filesA oldSlotsA startSlotsA expression control
          hasSingleLineMask noForward reduced c with
      | failure => simp only [cA] at hA; simp at hA
      | unknown => simp only [cA] at hA; simp at hA
      | ok cycleResultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := cycleResultA
          cases cB : prepareParsedIntegerALUExprCycle filesB oldSlotsB startSlotsB expression control
              hasSingleLineMask noForward reduced c with
          | failure => simp only [cB] at hB; simp at hB
          | unknown => simp only [cB] at hB; simp at hB
          | ok cycleResultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := cycleResultB
              simp only [cA] at hA
              simp only [cB] at hB
              refine ih (writesA ++ cycleWritesA) cycleSlotsA (writesB ++ cycleWritesB)
                cycleSlotsB resultA resultB ?_ hA hB
              rw [List.map_append, List.map_append,
                prepareParsedIntegerALUExprCycle_destination_state_general filesA filesB
                  oldSlotsA oldSlotsB startSlotsA startSlotsB expression control
                  hasSingleLineMask noForward reduced c cycleWritesA cycleSlotsA cycleWritesB
                  cycleSlotsB maskEq cA cB,
                writesEq]

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
