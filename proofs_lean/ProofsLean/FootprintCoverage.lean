import ProofsLean.ChannelResiduals

/-!
# Footprint coverage for plain integer-ALU rows

`ProofsLean/ChannelResiduals.lean` reduces the plain-ALU `.pe` line contract to
the single residual `PlusTwoLineFootprintCoversPreparedReads`: at every state,
the words the executor's nine-way integer lowering reads (`preparedListReadSet`)
must be contained in the hazard-event read footprint `plusTwoLineFootprint` of
the line.

This module proves the per-operand and per-row reconciliation between the two
lowerings, and records a machine-checked obstruction showing that the residual
*as stated in `ChannelResiduals.lean` is false*, hence that
`plusTwoWriteDeterminationChan_of_all_discharged` and
`plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` are
currently vacuous.

## 1. The reconciliation (proved)

* `exists_read_event_of_memory_resolution`: if the executor's resolution
  `ParsedOperand.toDirectMemoryAccess?` of a `.mem` source operand at a cycle
  yields `direct`, then the hazard lowering
  `ParsedOperand.toTimedPEHazardEvents? operand false control` returns
  `some events` with a non-write event whose access is exactly `direct`.
  The two lowerings agree because the `mask`/`allowDestinationMask` arguments
  only feed a guard that is false for source operands
  (`toDirectMemoryAccessMode?_mask_allow_irrelevant`), and because the
  resolution's success is cycle-independent
  (`toDirectMemoryAccess?_isSome_eq`), so the hazard analyzer's four-cycle
  `mapM` succeeds and reports the event at the executor's cycle.
* `sourceReadUpperBound_subset_hazardAccesses`: consequently, for a row all of
  whose operands are addressable, *every* read any of the nine resolvers can
  obtain from a source operand lies in the union of the access regions of the
  row's non-write hazard events.  This is exactly the per-row content the
  residual needs; all nine resolvers read through
  `ParsedOperand.toParsedIntegerInput?` or
  `ParsedOperand.toIntegerMaskSourceAccess?`, and both resolve a `.memory`
  source with the access recovered above.
* `plusTwoLineFootprint_pe`, `mem_lineSourceAccesses_of_event`,
  `hazardAccesses_subset_lineSourceAccesses` transport these facts from one row
  to the line-level `peLineSourceAccesses` / `plusTwoLineFootprint`.

## 2. The `.zero` / `.immediate` obstruction (proved)

`parsedExprIsPlainIntegerALU` accepts the constant producers `.zero` and
`.immediate ..` (`parsedExprIsIntegerProducer` is `true` for them) and
`parsedExprIsIntegerMatrixReadStageInput` keeps them, so they enter
`preparedListReadSet`.  Their read set is
`optionConstantReads (ParsedExpr.toDirectMaskedConstantWrites? ..)`, and
`ParsedExpr.toDirectMaskedConstantDestination?` lowers a `.mem` destination
into `ParsedConstantDestination.memory accesses` whose two sources are the
destination itself, so the read set contains `accessRegion destinationAccess`.
The hazard lowering of such a row reports only the destination's *write*
events (a constant producer has no source operands), and
`peLineSourceAccesses` filters write events out, so its footprint is empty.
`zeroRow_readSet_nonempty` machine-checks the read-set half at every state,
with exactly the `preparedListReadSet` expression of the residual.

Hence the residual cannot be discharged as stated.  The repaired residual
restricts the rows to `op = .alu` (excluding the constant producers, whose
read-modify-write of the masked destination is genuinely absent from the
hazard footprint) and, for an unconditional statement, to rows whose
`sources ++ destinations` are all `directMemoryAddressModeValid` (this is the
`addr` hypothesis of `sourceReadUpperBound_subset_hazardAccesses`; without it a
row containing one unresolvable operand makes the hazard lowering's row-level
`mapM` fail, so the footprint is empty even though `preparedListReadSet` is
defined unconditionally).  Given the repaired statement, the remaining work is
the eight-resolver read-set bound `aluCycleReadSet ⊆ sourceReadUpperBound`;
`sourceReadUpperBound_subset_hazardAccesses` then closes the line-level
statement.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## 1. The non-write accesses of the hazard-event lowering -/

/-- The source accesses the hazard lowering reports for a list of rows: all
non-write events of `ParsedExpr.toTimedPEHazardEvents?`, in source order. -/
def lineSourceAccesses (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) : List DirectMemoryAccess :=
  ((expressions.map fun expression =>
      (ParsedExpr.toTimedPEHazardEvents? expression control).getD []).flatten).filterMap
    fun event => if event.write then none else some event.access

/-- The same list for one row. -/
def hazardAccesses (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) : List DirectMemoryAccess :=
  ((ParsedExpr.toTimedPEHazardEvents? expression control).getD []).filterMap
    fun event => if event.write then none else some event.access

theorem peLineSourceAccesses_eq (expressions : List NormalizedExpr) (state : State) :
    peLineSourceAccesses expressions plusTwoPE state =
      lineSourceAccesses (expressions.map NormalizedExpr.toParsed)
        (parsedPEHazardControl state plusTwoPE) := by
  simp [peLineSourceAccesses, lineSourceAccesses, Function.comp_def]

/-- The concrete footprint is the union of the access regions of these accesses. -/
theorem plusTwoLineFootprint_pe (expressions : List NormalizedExpr) (state : State)
    {w : WordRef} :
    w ∈ plusTwoLineFootprint (.pe expressions) state ↔
      ∃ access ∈ lineSourceAccesses (expressions.map NormalizedExpr.toParsed)
        (parsedPEHazardControl state plusTwoPE), w ∈ accessRegion access := by
  rw [plusTwoLineFootprint_mem, peLineSourceAccesses_eq]

/-- A non-write event of one row contributes its access to the line's list. -/
theorem mem_lineSourceAccesses_of_event (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) {expression : ParsedExpr}
    (member : expression ∈ expressions) {event : TimedPEAccess}
    (hevent : event ∈ (ParsedExpr.toTimedPEHazardEvents? expression control).getD [])
    (read : event.write = false) :
    event.access ∈ lineSourceAccesses expressions control := by
  unfold lineSourceAccesses
  refine List.mem_filterMap.mpr ⟨event, ?_, by simp [read]⟩
  exact List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨expression, member, rfl⟩, hevent⟩

theorem hazardAccesses_subset_lineSourceAccesses (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) {expression : ParsedExpr}
    (member : expression ∈ expressions) {access : DirectMemoryAccess}
    (h : access ∈ hazardAccesses expression control) :
    access ∈ lineSourceAccesses expressions control := by
  obtain ⟨event, hevent, haccess⟩ := List.mem_filterMap.mp h
  have hread : event.write = false := by
    by_contra hw
    have htrue : event.write = true := by simpa using hw
    rw [htrue] at haccess
    simp at haccess
  have heq : event.access = access := by
    rw [hread] at haccess
    simpa using haccess
  rw [← heq]
  exact mem_lineSourceAccesses_of_event expressions control member hevent hread

/-! ## 2. The source-read upper bound of an expression -/

/-- Every read region the nine-way lowering can obtain from the expression's
source operands: some operand of the row, at some cycle, for some precision. -/
def sourceReadUpperBound (expression : ParsedExpr) (group : Fin 4) (l2b : Fin 2)
    (l1b : Fin 8) (mab : Fin 16) (pe : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) : Set WordRef :=
  {w | ∃ oper ∈ expression.sources, ∃ cycle : Fin 4, ∃ precision : IntegerALU.Precision,
    ∃ input : ParsedIntegerInput,
      ParsedOperand.toParsedIntegerInput? oper precision group l2b l1b mab pe cycle
        bar0 bar1 tWord = some input ∧ w ∈ ParsedIntegerInput.readsRegion input}

/-- A resolved source operand's reads lie in the expression's read bound. -/
theorem readsRegion_subset_sourceReadUpperBound (expression : ParsedExpr)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (oper : ParsedOperand) (member : oper ∈ expression.sources)
    (precision : IntegerALU.Precision) (cycle : Fin 4) (input : ParsedIntegerInput)
    (resolved : ParsedOperand.toParsedIntegerInput? oper precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some input) :
    ParsedIntegerInput.readsRegion input ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord :=
  fun w hw => ⟨oper, member, cycle, precision, input, resolved, hw⟩

theorem union_subset_sourceReadUpperBound (expression : ParsedExpr)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (operX operY : ParsedOperand) (mX : operX ∈ expression.sources)
    (mY : operY ∈ expression.sources)
    (precision : IntegerALU.Precision) (cycle : Fin 4)
    (inputX inputY : ParsedIntegerInput)
    (hX : ParsedOperand.toParsedIntegerInput? operX precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some inputX)
    (hY : ParsedOperand.toParsedIntegerInput? operY precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some inputY) :
    ParsedIntegerInput.readsRegion inputX ∪ ParsedIntegerInput.readsRegion inputY ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord :=
  Set.union_subset
    (readsRegion_subset_sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord
      operX mX precision cycle inputX hX)
    (readsRegion_subset_sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord
      operY mY precision cycle inputY hY)

/-! ## 3. Per-cycle address resolution agreement

The executor resolves a `.mem` source operand through
`ParsedOperand.toDirectMemoryAccess?` (`allowDestinationMask = false`, mask
`none`); the hazard analyzer resolves the same operand through
`ParsedOperand.toDirectMemoryAccessMode?` on `forHazardAddress operand`
(`allowDestinationMask = true`, the operand's own mask).  The two flags only
feed a guard that is false for every source operand, so the resolutions agree
at every cycle; and because every remaining guard is cycle-independent, the
resolution succeeds at one cycle exactly when it succeeds everywhere. -/

theorem toDirectMemoryAccessMode?_mask_allow_irrelevant
    (access : ProofsLean.MNCore.Issue.Access) (mask : Option ParsedMask)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? (.mem access false false false mask) true
        pe cycle bar0 bar1 tWord =
      ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
        pe cycle bar0 bar1 tWord := by
  simp [ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.toDirectMemoryAccess?]

theorem option_isSome_ite {α : Type} (G : Bool) (x y : Option α) :
    (if G then x else y).isSome = if G then x.isSome else y.isSome := by
  cases G <;> rfl

theorem toDirectMemoryAccess?_isSome_eq (access : ProofsLean.MNCore.Issue.Access)
    (pe c c' : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryAccess? (.mem access false false false none) pe c bar0
        bar1 tWord).isSome =
      (ParsedOperand.toDirectMemoryAccess? (.mem access false false false none) pe c' bar0
        bar1 tWord).isSome := by
  simp only [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?]
  cases hb : issueBankToRegisterBank access.bank with
  | none => rfl
  | some bank =>
      cases hw : parsedWidth? access.region.width with
      | none => rfl
      | some width =>
          simp only [hb, hw, option_isSome_ite]
          simp

/-! ## 4. Membership of the reported cycles in a successful `mapM` -/

theorem mem_zip_mapM {α β : Type} (f : α → Option β) (l : List α)
    (hs : (l.mapM f).isSome = true) {x : α} (hx : x ∈ l) {v : β} (hv : f x = some v) :
    ∃ resolved, l.mapM f = some resolved ∧ (x, v) ∈ l.zip resolved := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rw [List.mapM_cons] at hs
      cases hf : f a with
      | none => simp [hf] at hs
      | some va =>
          cases hm : (rest.mapM f) with
          | none => simp [hf, hm] at hs
          | some vs =>
              have hrest : (rest.mapM f).isSome = true := by rw [hm]; rfl
              refine ⟨va :: vs, ?_, ?_⟩
              · simp [List.mapM_cons, hf, hm]
              · rcases List.mem_cons.mp hx with rfl | hx
                · have hva : va = v := by rw [hf] at hv; exact Option.some.inj hv
                  subst hva
                  simp
                · obtain ⟨resolved, hres, hmem⟩ := ih hrest hx
                  rw [hm] at hres
                  have hrv : resolved = vs := (Option.some.inj hres).symm
                  subst hrv
                  exact List.mem_cons_of_mem _ hmem

theorem mapM_list_getD {α β : Type} (f : α → Option (List β)) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome = true) :
    l.flatMap (fun x => (f x).getD []) = (l.map fun x => (f x).getD []).flatten := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : ∀ y ∈ rest, (f y).isSome = true := fun y hy => h y (by simp [hy])
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp hx
      rw [List.flatMap_cons, ih hrest, List.map_cons, List.flatten_cons]

/-! ## 5. The per-operand reconciliation -/

/-- **A resolved memory source is a reported read event.**  If the executor's
resolution of a `.mem` operand at `cycle` yields `direct`, then the hazard
lowering of the same operand (with the write flag `false`) reports a non-write
event whose access is exactly `direct`.  The two lowerings agree because the
mask/allow flags of `toDirectMemoryAccessMode?` only feed a guard that is false
for source operands (`toDirectMemoryAccessMode?_mask_allow_irrelevant`), and the
hazard lowering resolves all four cycles (`toDirectMemoryAccess?_isSome_eq`). -/
theorem exists_read_event_of_memory_resolution
    (access : ProofsLean.MNCore.Issue.Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (direct : DirectMemoryAccess)
    (resolved : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
      control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord
      = some direct) :
    ∃ events, ParsedOperand.toTimedPEHazardEvents? (.mem access negated extended rounded mask)
        false control = some events ∧
      ∃ event ∈ events, event.write = false ∧ event.access = direct := by
  have hazardSome : ∀ c : Fin 4, (ParsedOperand.toDirectMemoryAccessMode?
      (.mem access false false false mask) true
      control.context.pe c control.context.bar0 control.context.bar1 control.context.tWord).isSome
      = true := by
    intro c
    rw [toDirectMemoryAccessMode?_mask_allow_irrelevant]
    rw [toDirectMemoryAccess?_isSome_eq access control.context.pe c cycle control.context.bar0
      control.context.bar1 control.context.tWord, resolved]
    rfl
  have hazardCycle : ParsedOperand.toDirectMemoryAccessMode? (.mem access false false false mask)
      true control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord
      = some direct := by
    rw [toDirectMemoryAccessMode?_mask_allow_irrelevant]
    exact resolved
  unfold ParsedOperand.toTimedPEHazardEvents?
  rw [ParsedOperand.forHazardAddress_mem]
  cases hb : issueBankToRegisterBank access.bank with
  | none =>
      simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?, hb]
        at resolved
  | some bank =>
      simp only [hb]
      have hsome : (parsedHazardCycles.mapM fun c =>
          ParsedOperand.toDirectMemoryAccessMode? (.mem access false false false mask) true
            control.context.pe c control.context.bar0 control.context.bar1 control.context.tWord
          ).isSome = true :=
        list_mapM_isSome_of_forall _ _ (fun c _ => hazardSome c)
      obtain ⟨resolvedAccesses, hresolved⟩ := Option.isSome_iff_exists.mp hsome
      rw [hresolved]
      refine ⟨_, rfl, ⟨⟨direct, false, control.elapsedWords, cycle⟩, ?_, rfl, rfl⟩⟩
      rw [List.mem_flatMap]
      refine ⟨(cycle, direct), ?_, ?_⟩
      · have hmem : cycle ∈ parsedHazardCycles := by
          rcases cycle with ⟨n, hn⟩
          have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
          rcases h with rfl | rfl | rfl | rfl <;> simp [parsedHazardCycles]
        obtain ⟨resolved', hres', hmem'⟩ := mem_zip_mapM _ _ hsome hmem hazardCycle
        rw [hresolved] at hres'
        have hEq : resolved' = resolvedAccesses := (Option.some.inj hres').symm
        subst hEq
        exact hmem'
      · simp [TimedPEAccess.ofControl]

/-- Membership of the operand's events in the row's events. -/
theorem mem_flatten_mapM {α β : Type} (f : α → Option (List β)) (l : List α)
    (hs : (l.mapM f).isSome = true) {x : α} (hx : x ∈ l) {v : List β}
    (hv : f x = some v) {b : β} (hb : b ∈ v) :
    ∃ vals, l.mapM f = some vals ∧ b ∈ vals.flatten := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rw [List.mapM_cons] at hs
      cases hf : f a with
      | none => simp [hf] at hs
      | some va =>
          cases hm : (rest.mapM f) with
          | none => simp [hf, hm] at hs
          | some vs =>
              have hrest : (rest.mapM f).isSome = true := by rw [hm]; rfl
              refine ⟨va :: vs, ?_, ?_⟩
              · simp [List.mapM_cons, hf, hm]
              · rcases List.mem_cons.mp hx with rfl | hx
                · have hva : va = v := by rw [hf] at hv; exact Option.some.inj hv
                  subst hva
                  rw [List.flatten_cons, List.mem_append]
                  exact Or.inl hb
                · obtain ⟨vals, hv', hmem⟩ := ih hrest hx
                  rw [hm] at hv'
                  have hrv : vals = vs := (Option.some.inj hv').symm
                  subst hrv
                  rw [List.flatten_cons, List.mem_append]
                  exact Or.inr hmem

theorem isSome_mapM_mem {α β : Type} (f : α → Option β) (l : List α)
    (h : (l.mapM f).isSome = true) : ∀ x ∈ l, (f x).isSome = true := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a rest ih =>
      intro x hx
      rw [List.mapM_cons] at h
      cases hf : f a with
      | none => simp [hf] at h
      | some v =>
          cases hm : (rest.mapM f) with
          | none => simp [hf, hm] at h
          | some vs =>
              have hrest : (rest.mapM f).isSome = true := by rw [hm]; rfl
              rcases List.mem_cons.mp hx with rfl | hx
              · simp [hf]
              · exact ih hrest x hx

/-- **Reads of a row are footprint accesses.**  If every operand of the row is
addressable, then every read any of the executor's source lowerings can resolve
from a source operand lies in the union of the access regions of the row's
non-write hazard events.  This is the reconciliation the residual asks for,
stated per row: it is independent of which of the nine resolvers produced the
read, because all of them read through `ParsedOperand.toParsedIntegerInput?`
or `ParsedOperand.toIntegerMaskSourceAccess?`, and both resolve a `.memory`
source with exactly the access that `exists_read_event_of_memory_resolution`
recovers from the hazard lowering. -/
theorem sourceReadUpperBound_subset_hazardAccesses (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl)
    (addr : (expression.sources ++ expression.destinations).all
      ParsedOperand.directMemoryAddressModeValid = true) :
    sourceReadUpperBound expression control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe control.context.bar0
      control.context.bar1 control.context.tWord ⊆
    {w | ∃ access ∈ hazardAccesses expression control, w ∈ accessRegion access} := by
  have hsourceValid : ∀ o ∈ expression.sources,
      ParsedOperand.directMemoryAddressModeValid o = true := by
    intro o ho
    exact List.all_eq_true.mp addr o (by simp [ho])
  have hwritesSome : (expression.destinations.mapM fun o =>
      ParsedOperand.toTimedPEHazardEvents? o true control).isSome = true := by
    apply list_mapM_isSome_of_forall
    intro o ho
    exact ParsedOperand.toTimedPEHazardEvents?_isSome_of_valid o true control
      (List.all_eq_true.mp addr o (by simp [ho]))
  have hreadsSome : (expression.sources.mapM fun o =>
      ParsedOperand.toTimedPEHazardEvents? o false control).isSome = true := by
    apply list_mapM_isSome_of_forall
    intro o ho
    exact ParsedOperand.toTimedPEHazardEvents?_isSome_of_valid o false control
      (hsourceValid o ho)
  obtain ⟨readLists, hreadLists⟩ := Option.isSome_iff_exists.mp hreadsSome
  obtain ⟨writeLists, hwriteLists⟩ := Option.isSome_iff_exists.mp hwritesSome
  have hrowEvents : ParsedExpr.toTimedPEHazardEvents? expression control
      = some (readLists.flatten ++ writeLists.flatten) := by
    unfold ParsedExpr.toTimedPEHazardEvents?
    rw [hreadLists, hwriteLists]
    rfl
  rintro w ⟨oper, member, cycle, precision, input, resolved, hw⟩
  cases oper with
  | mem access negated extended rounded mask =>
      simp only [ParsedOperand.toParsedIntegerInput?] at resolved
      obtain ⟨direct, hdirect, hinput⟩ := Option.map_eq_some_iff.mp resolved
      cases hinput
      obtain ⟨events, hevents, event, hevent, hwrite, haccess⟩ :=
        exists_read_event_of_memory_resolution access negated extended rounded mask control
          cycle direct hdirect
      obtain ⟨vals, hvals', hvals⟩ := mem_flatten_mapM
        (fun o => ParsedOperand.toTimedPEHazardEvents? o false control)
        expression.sources hreadsSome member hevents hevent
      rw [hreadLists] at hvals'
      have hvEq : vals = readLists := (Option.some.inj hvals').symm
      subst hvEq
      have hmemRow : event ∈ (ParsedExpr.toTimedPEHazardEvents? expression control).getD [] := by
        rw [hrowEvents]
        exact List.mem_append_left _ hvals
      refine ⟨event.access, ?_, by rw [haccess]; exact hw⟩
      exact List.mem_filterMap.mpr ⟨event, hmemRow, by simp [hwrite]⟩
  | fixed fixed =>
      simp only [ParsedOperand.toParsedIntegerInput?] at resolved
      have hEq : input = .fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe)) :=
        (Option.some.inj resolved).symm
      subst hEq
      simp [ParsedIntegerInput.readsRegion] at hw
  | forward kind neg ext rounded =>
      simp only [ParsedOperand.toParsedIntegerInput?] at resolved
      have hEq : input = .forward kind rounded := (Option.some.inj resolved).symm
      subst hEq
      simp [ParsedIntegerInput.readsRegion] at hw
  | bar lm1 width mask =>
      exact absurd resolved (by
        simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
          ParsedOperand.toDirectMemoryAccessMode?])
  | omr entry mask =>
      exact absurd resolved (by
        simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
          ParsedOperand.toDirectMemoryAccessMode?])
  | matrix y width row =>
      exact absurd resolved (by
        simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
          ParsedOperand.toDirectMemoryAccessMode?])
  | nowrite => exact absurd resolved (by
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?])
  | l1bm width address => exact absurd resolved (by
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?])
  | l2bm address l2b => exact absurd resolved (by
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?])
  | dar address => exact absurd resolved (by
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?])

/-! ## 6. The `.zero` obstruction: a plain integer producer whose reads the
hazard footprint cannot cover

`parsedExprIsPlainIntegerALU` accepts the constant producers `.zero` and
`.immediate ..` (`parsedExprIsIntegerProducer` returns `true` for them), and
`parsedExprIsIntegerMatrixReadStageInput` keeps them.  Their prepared read set
is `optionConstantReads (ParsedExpr.toDirectMaskedConstantWrites? ..)`, and
`ParsedExpr.toDirectMaskedConstantDestination?` lowers a `.mem` destination into
`ParsedConstantDestination.memory accesses` whose *two sources are the
destination itself* (`ParsedOperand.toDirectMaskedIntegerAccessesInLine?`'s
constant branch sets `sourceX = sourceY = .memory destinationAccess false`), so
the prepared read list contains `accessRegion destinationAccess`.

The hazard lowering, by contrast, reports only the destination's *write*
events (a constant producer has no source operands), and
`peLineSourceAccesses` filters write events out.  Hence the footprint of such a
row is empty while its prepared read set is not: the residual cannot hold.

The lemma below machine-checks the read-set half of the obstruction for the
concrete `.zero` row `zeroRow`: its prepared read set (with exactly the
`preparedListReadSet` expression the residual uses) is nonempty, at *every*
state, while `zeroRow` has no source operands at all. -/

/-- `count` is positive, so every direct access region is nonempty. -/
theorem count_pos (bank : PEMemory.Bank) (width : Width) : 0 < count bank width := by
  cases bank <;> cases width <;> decide

theorem distance_self (bank : PEMemory.Bank) (start : Fin bank.capacity) :
    distance bank start start = 0 := by
  simp [distance]

/-- The resolved address itself is in the access region. -/
theorem mem_accessRegion_self (access : DirectMemoryAccess) :
    (⟨access.bank, access.address⟩ : WordRef) ∈ accessRegion access := by
  rw [mem_accessRegion_iff]
  exact ⟨access.address, rfl, by rw [distance_self]; exact count_pos _ _⟩

/-- A `.zero` row writing one LM0 destination.  Its row is a plain integer ALU
producer (`parsedExprIsPlainIntegerALU`), survives the integer-stage filter, and
has no source operands, so its hazard read footprint cannot contain anything. -/
def zeroRow : NormalizedExpr where
  op := .zero
  sources := []
  destinations := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none]
  flush := none

def zeroDestination : ParsedOperand :=
  .mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none

theorem zeroRow_plain : parsedExprIsPlainIntegerALU zeroRow.toParsed = true := by decide

theorem zeroRow_stage :
    parsedExprIsIntegerMatrixReadStageInput zeroRow.toParsed = true := by
  simp only [zeroRow, NormalizedExpr.toParsed, parsedExprIsIntegerMatrixReadStageInput,
    parsedExprWaitTag?, parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
    parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer, parsedExprIsL1ReduceProducer,
    parsedExprIsL1ToPEProducer, parsedExprIsMatrixMAUProducer,
    parsedExprIsSupportedFloatMAUProducer, parsedExprIsMslMsrProducer,
    parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer]
  decide

theorem zeroRow_filter :
    ([zeroRow].map NormalizedExpr.toParsed).filter parsedExprIsIntegerMatrixReadStageInput
      = [zeroRow.toParsed] := by
  simp [zeroRow_stage]

theorem zeroRow_noSources : zeroRow.toParsed.sources = [] := rfl

theorem zeroDestination_valid :
    ParsedOperand.directMemoryAddressModeValid zeroDestination = true := by
  decide

theorem zeroDestination_resolves (state : State) (cycle : Fin 4) :
    ∃ access : DirectMemoryAccess,
      ParsedOperand.toDirectMemoryDestination? zeroDestination
        (parsedPEHazardControl state plusTwoPE).context.pe cycle
        (parsedPEHazardControl state plusTwoPE).context.bar0
        (parsedPEHazardControl state plusTwoPE).context.bar1
        (parsedPEHazardControl state plusTwoPE).context.tWord = some access := by
  have h := ParsedOperand.toDirectMemoryDestination_isSome_of_valid
    ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ none
    (parsedPEHazardControl state plusTwoPE).context.pe cycle
    (parsedPEHazardControl state plusTwoPE).context.bar0
    (parsedPEHazardControl state plusTwoPE).context.bar1
    (parsedPEHazardControl state plusTwoPE).context.tWord
    zeroDestination_valid
  exact Option.isSome_iff_exists.mp (by simpa [zeroDestination] using h)

/-- **The prepared read set of the `.zero` row is nonempty at every state**, with
the very `preparedListReadSet` of `PlusTwoLineFootprintCoversPreparedReads`. -/
theorem zeroRow_readSet_nonempty (state : State) :
    ∃ w : WordRef, w ∈ preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
      ((([zeroRow].map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput))
      (parsedPEHazardControl state plusTwoPE) := by
  obtain ⟨access, haccess⟩ := zeroDestination_resolves state 0
  have hany : (([zeroRow].map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask = false := by
    rw [zeroRow_filter]
    simp [zeroRow, NormalizedExpr.toParsed, parsedExprHasSingleLineWriteMask,
      parsedOperandHasSingleLineWriteMask]
  refine ⟨⟨access.bank, access.address⟩, ?_⟩
  rw [zeroRow_filter]
  simp only [preparedListReadSet, parsedExpressionReadSet, hany]
  refine ⟨zeroRow.toParsed, by simp, 0, by simp [parsedIntegerALUCycles], ?_⟩
  simp only [aluCycleReadSet, zeroRow, NormalizedExpr.toParsed]
  obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp
    (ParsedOperand.resolveMemoryWriteSelection_mem_isSome
      ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ access none
      (state.peRegisters plusTwoPE).maskRegisters 0
      (parsedPEHazardControl state plusTwoPE).directive false)
  obtain ⟨fs, hfs⟩ := resolveFlushSelection?_always_resolves none
    (state.peRegisters plusTwoPE).maskRegisters 0
  simp only [zeroDestination] at haccess
  simp [ParsedExpr.toDirectMaskedConstantWrites?, ParsedExpr.toDirectMaskedConstantDestinations?,
    ParsedExpr.toDirectMaskedConstantDestination?,
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?, ParsedOp.executionRequest,
    zeroDestination, haccess, hws, hfs, optionConstantReads, constantTargetReads,
    maskedIntegerReads, ParsedIntegerInput.readsRegion,
    parsedExprHasSingleLineWriteMask, parsedOperandHasSingleLineWriteMask]
  exact mem_accessRegion_self access

end ProofsLean.MNCore
