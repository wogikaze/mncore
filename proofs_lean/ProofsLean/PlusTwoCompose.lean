import ProofsLean.ALUReadSetBound

/-!
# Composing the unconditional read kernel with the per-line read capacity

`ProofsLean/ALUReadSetBound.lean` proves, with no residual premise, that a
correct `2.plus-two` program must read the LM0 word of input `j` for **every**
`j : Fin 20`: some line's concrete hazard-event footprint
(`plusTwoLineFootprint`) must contain `plusTwoInputWord j` in one of the two
states of the input-dependence argument.  This module derives the resource count
that the kernel has to be composed with, and it is precise about how far that
count goes.

## 1. The exact per-line read capacity is `8`

`plusTwoLineFootprint (.pe expressions) state` is the union of the
`accessRegion`s of the line's *source* accesses (`plusTwoLineFootprint_pe`), and
each `accessRegion` is a window of `count bank width ≤ 4` consecutive words
(`accessRegion_subset_advance`).

The number of *distinct* source accesses is what matters, and it is bounded by
the issue checker, **not** by an arity or row limit:

* a `.pe` line may contain any number of rows —
  `prepareParsedIntegerMatrixReadLineExpressions` walks the whole list, nothing
  truncates it to four, so a row count alone bounds nothing;
* a row contributes all `.mem` operands of `expression.sources` to
  `lineSourceAccesses`, not only the two the ALU reads;
* the bound comes from `Issue.Legal`, which every *executed* line passes
  (`executeIntegerProducerInstructionLine` starts with `checkParsedTopLine`):
  `readsAgree` forces all `.mem` source reads of the line that hit the same
  bank to carry the **same `Region`**.  A `Region` fixes the width and the four
  per-cycle addresses, and `toDirectMemoryAccessMode?` resolves an access from
  exactly `(bank, region, pe, bar0, bar1, tWord, cycle)`, so every LM0 access
  of the line is one of **four** accesses, one per cycle
  (`plusTwo_lineSourceAccesses_lm0_eq_cycleAccess`).

The capacity is therefore `4 cycles × (input words in one ≤ 4-word window)`.
The twenty input words are the odd LM0 addresses `1, 3, ..., 39`, and any four
consecutive words contain at most two of them
(`plusTwo_window_inputs_card_le_two`):

> **`plusTwoFootprint_inputs_card_le_eight`** — `plusTwoLineFootprint` contains
> at most `8` distinct `plusTwoInputWord j`, for a checked `.pe` line and *any*
> state.  The sharp bound is `8`, not `4` and not `20`.

## 2. Why `20 / 8` is not yet a line count

The kernel's witnesses are state-existential, and the resolved address contains
the state's BAR word: `(bar0 + regionAddressAt cycle + madpe) / words * words`.
As `bar0` ranges over `2 ^ 12` values the very same line reads *every* input
word, so "at most eight input words per line" is a per-*(line, state)* fact and
does not by itself bound the number of lines.  What is needed is a *pinned*
kernel — the witness states must be the prefix states of two fixed executions.

That strengthening is proved here: `plusTwo_exists_prefix_footprint_meets_chan`
carries the prefix through the channel-level induction of
`execute_agreeOutside_of_determined_chan`, and
`plusTwo_exists_prefix_pe_read` instantiates it at the all-zero input and the
one-hot input at `j`.  Because a one-line program has only the empty prefix, both
witness states are then the *initial* states, whose footprints are
input-independent (`plusTwoInitialState_footprint_eq`):

> **`plusTwo_lowerBound_two_of_determinationChan`** — from the single existing
> residual `PlusTwoWriteDeterminationChan`: `LowerBound plusTwoSealedMachine
> plusTwoSpec 2`.  On the discharged line class the residual is discharged by
> `lineDeterminedAtChan_of_aluRows`, giving `plusTwo_lowerBound_two`
> unconditionally for programs of `nop` / `mv` / checked plain-ALU `.pe` lines.

## 3. What the count does not reach

* `PlusTwoInitialFootprintCoverage` — the residual for `3 ≤ score`.  With the
  PE context frozen along the program, the pinned witness's state has the
  initial context and its footprint is the initial footprint, so the twenty
  input words distribute over the lines at `8` each (`3 * 8 = 24 > 20`).  The
  context is *not* frozen in general: `parsedIntegerALUBarUpdates` stores
  computed data into the BAR of a `.pe` line whose single destination is
  `.bar`, so the prefix context can be input-dependent.
* `LowerBound 4` needs the *write* budgets, not the read capacity: a line
  changes at most eight of the twenty observed words and the first line at most
  three (`PlusTwoLineWriteBudget`, `PlusTwoFirstLineCorrectBudget`;
  `plusTwoLowerBound_four_of_lineBudgets`).  The read capacity contributes
  nothing to either, because reads do not write.
* `LowerBound 5` and `6` are out of reach of *any* count of this shape: the
  capacity is exactly `8 = 4 × 2` because a `Region` carries four independent
  cycle addresses and a `.double` window holds two of the twenty odd input
  addresses, so the read side bottoms out at `⌈20 / 8⌉ = 3` lines.  The
  five-line floor is an *input-parametric provenance* statement (which output
  value each written word carries), of which `PlusTwoOutputProvenance` records
  the write-side shape.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module
edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

/-! ## 0. A Finset counting helper -/

/-- A finite set in which any three elements are not pairwise distinct has at
most two elements. -/
theorem plusTwo_card_le_two_of_forall_three {α : Type*} [DecidableEq α]
    {s : Finset α} (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a = b ∨ a = c ∨ b = c) :
    s.card ≤ 2 := by
  by_contra hle
  have h3 : 2 < s.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h3
  rcases h a ha b hb c hc with same | same | same
  · exact hab same
  · exact hac same
  · exact hbc same

/-! ## 1. The input words are the odd LM0 addresses below forty -/

theorem plusTwoInputWord_val (j : Fin 20) :
    (plusTwoInputWord j).2.val = 2 * j.val + 1 := rfl

theorem plusTwoInputWord_bank_eq (j : Fin 20) :
    (plusTwoInputWord j).1 = PEMemory.Bank.lm0 := rfl

/-- The address of an input word is below forty. -/
theorem plusTwoInputWord_val_lt (j : Fin 20) :
    (plusTwoInputWord j).2.val < 40 := by
  have bound := j.isLt
  rw [plusTwoInputWord_val]
  omega

/-! ## 2. Any four consecutive LM0 words contain at most two input words -/

/-- A cyclic window of `start, ..., start+3` reduced modulo the LM0 capacity is
either literally that window or a wrap; the two cases are the only ones. -/
theorem plusTwo_window_mod_cases (start i : Nat) (hi : i < 4) (hstart : start < 4096) :
    (start + i) % 4096 = start + i ∨ (start + i) % 4096 = start + i - 4096 := by
  by_cases small : start + i < 4096
  · exact Or.inl (Nat.mod_eq_of_lt small)
  · refine Or.inr ?_
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A window of four consecutive LM0 addresses contains at most two input
words.**  The input words are the odd addresses `1, 3, ..., 39`; a four-word
window holds two odd addresses, and a wrapped window can only reach the three
addresses `0, 1, 2`, whose only odd input address is `1`. -/
theorem plusTwo_window_inputs_card_le_two (start : Nat) (hstart : start < 4096) :
    (Finset.univ.filter (fun j : Fin 20 =>
      ∃ i : Nat, i < 4 ∧ (start + i) % 4096 = 2 * j.val + 1)).card ≤ 2 := by
  apply plusTwo_card_le_two_of_forall_three
  intro a ha b hb c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  obtain ⟨ia, hia, hva⟩ := ha
  obtain ⟨ib, hib, hvb⟩ := hb
  obtain ⟨ic, hic, hvc⟩ := hc
  have bounda : 2 * a.val + 1 < 40 := plusTwoInputWord_val_lt a
  have boundb : 2 * b.val + 1 < 40 := plusTwoInputWord_val_lt b
  have boundc : 2 * c.val + 1 < 40 := plusTwoInputWord_val_lt c
  by_cases low : start ≤ 4092
  · -- no wrap: the three addresses all lie in `start, ..., start+3`
    have key : ∀ (j : Fin 20) (i : Nat), i < 4 → (start + i) % 4096 = 2 * j.val + 1 →
        2 * j.val + 1 = start + i := by
      intro j i hi h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      exact h.symm
    have hva' := key a ia hia hva
    have hvb' := key b ib hib hvb
    have hvc' := key c ic hic hvc
    have values : a.val = b.val ∨ a.val = c.val ∨ b.val = c.val := by omega
    rcases values with same | same | same
    · exact Or.inl (Fin.ext same)
    · exact Or.inr (Or.inl (Fin.ext same))
    · exact Or.inr (Or.inr (Fin.ext same))
  · -- wrap: `start ≥ 4093`, so the only address below forty is `1`
    have key : ∀ (j : Fin 20) (i : Nat), i < 4 → (start + i) % 4096 = 2 * j.val + 1 →
        j.val = 0 := by
      intro j i hi h
      rcases plusTwo_window_mod_cases start i hi hstart with h' | h'
      · omega
      · omega
    have ha0 := key a ia hia hva
    have hb0 := key b ib hib hvb
    have hc0 := key c ic hic hvc
    exact Or.inl (Fin.ext (by omega))

/-- **A direct access region contains at most two input words.**  The region is
the window of `count bank width ≤ 4` words starting at the resolved address, and
only LM0 holds input words at all. -/
theorem plusTwo_accessRegion_inputs_card_le_two (access : DirectMemoryAccess) :
    (Finset.univ.filter (fun j : Fin 20 =>
      plusTwoInputWord j ∈ accessRegion access)).card ≤ 2 := by
  classical
  obtain ⟨bank, width, start⟩ := access
  cases bank with
  | lm0 =>
      refine le_trans (Finset.card_le_card ?_)
        (plusTwo_window_inputs_card_le_two start.val start.isLt)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨address, hEq, hwithin⟩ := (mem_accessRegion_iff ⟨.lm0, width, start⟩ (plusTwoInputWord j)).mp hj
      have hval : address.val = 2 * j.val + 1 := by
        have := congrArg (fun w : WordRef => w.2.val) hEq
        simpa [plusTwoInputWord, plusTwoLowAddress] using this.symm
      refine ⟨distance .lm0 start address, ?_, ?_⟩
      · exact Nat.lt_of_lt_of_le hwithin (count_le_four .lm0 width)
      · have hadv := advance_distance_capacity .lm0 start address
        have := congrArg Fin.val hadv
        simp only [advance, Bank.capacity] at this
        omega
  | lm1 =>
      have empty : (Finset.univ.filter (fun j : Fin 20 =>
          plusTwoInputWord j ∈ accessRegion ⟨.lm1, width, start⟩)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have := accessRegion_bank ⟨.lm1, width, start⟩ hj
        rw [plusTwoInputWord_bank_eq] at this
        exact absurd this.symm (by simp)
      rw [empty]
      simp
  | grf0 =>
      have empty : (Finset.univ.filter (fun j : Fin 20 =>
          plusTwoInputWord j ∈ accessRegion ⟨.grf0, width, start⟩)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have := accessRegion_bank ⟨.grf0, width, start⟩ hj
        rw [plusTwoInputWord_bank_eq] at this
        exact absurd this.symm (by simp)
      rw [empty]
      simp
  | grf1 =>
      have empty : (Finset.univ.filter (fun j : Fin 20 =>
          plusTwoInputWord j ∈ accessRegion ⟨.grf1, width, start⟩)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have := accessRegion_bank ⟨.grf1, width, start⟩ hj
        rw [plusTwoInputWord_bank_eq] at this
        exact absurd this.symm (by simp)
      rw [empty]
      simp
  | t =>
      have empty : (Finset.univ.filter (fun j : Fin 20 =>
          plusTwoInputWord j ∈ accessRegion ⟨.t, width, start⟩)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have := accessRegion_bank ⟨.t, width, start⟩ hj
        rw [plusTwoInputWord_bank_eq] at this
        exact absurd this.symm (by simp)
      rw [empty]
      simp

/-! ## 3. Plumbing: reading the hazard-event lowering

`peLineSourceAccesses` is the flattening of the per-row hazard-event lists,
filtered to the non-write events.  To count the *distinct* LM0 accesses it
reports we have to unfold that lowering once; the lemmas below do exactly that
and nothing more. -/

/-- The events one hazard cycle contributes for a `.mem` operand. -/
def plusTwoHazardCycleEvents (control : ParsedMaskExecutionControl) (a : Access)
    (mask : Option ParsedMask) (write : Bool) (pair : Fin 4 × DirectMemoryAccess) :
    List TimedPEAccess :=
  if write && !parsedHazardPatternEnables mask pair.1 then []
  else
    [TimedPEAccess.ofControl control pair.2 write pair.1] ++
      (if !write && a.region.tIndirect then
        [TimedPEAccess.ofControl control (tIndirectHazardAccess pair.1) false pair.1] else [])

theorem plusTwo_mem_getD_option {α : Type*} (o : Option (List α)) {x : α}
    (h : x ∈ o.getD []) : ∃ l, o = some l ∧ x ∈ l := by
  cases o with
  | none => simp at h
  | some l => exact ⟨l, rfl, h⟩

theorem plusTwo_mem_flatten_of_mapM {α β : Type*} (f : α → Option (List β))
    (l : List α) (lists : List (List β)) (h : l.mapM f = some lists) {x : β}
    (hx : x ∈ lists.flatten) : ∃ item ∈ l, x ∈ (f item).getD [] := by
  induction l generalizing lists with
  | nil =>
      rw [List.mapM_nil] at h
      have hnil : lists = [] := (Option.some.inj h).symm
      subst hnil
      simp at hx
  | cons a rest ih =>
      rw [List.mapM_cons] at h
      cases hf : f a with
      | none => simp [hf] at h
      | some va =>
          cases hm : rest.mapM f with
          | none => simp [hf, hm] at h
          | some vs =>
              simp only [hf, hm, bind, Option.bind] at h
              have hlists : lists = va :: vs := (Option.some.inj h).symm
              subst hlists
              rw [List.flatten_cons, List.mem_append] at hx
              rcases hx with hx | hx
              · exact ⟨a, by simp, by rw [hf]; simpa using hx⟩
              · obtain ⟨item, member, hitem⟩ := ih vs hm hx
                exact ⟨item, List.mem_cons_of_mem _ member, hitem⟩

theorem plusTwo_mem_of_mem_zip_mapM {α β : Type*} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ {a : α} {b : β},
      (a, b) ∈ l.zip r → f a = some b := by
  intro l
  induction l with
  | nil => intro r _ a b hmem; simp at hmem
  | cons x rest ih =>
      intro r h a b hmem
      rw [List.mapM_cons] at h
      cases hf : f x with
      | none => simp [hf] at h
      | some vx =>
          cases hm : rest.mapM f with
          | none => simp [hf, hm] at h
          | some vs =>
              simp only [hf, hm, bind, Option.bind] at h
              have hr : r = vx :: vs := (Option.some.inj h).symm
              subst hr
              simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl⟩ | hmem
              · exact hf
              · exact ih hm hmem

/-- The event list of a `.mem` operand, unfolded: either the bank does not
resolve to a PE register bank (no events at all) or the four cycles resolve to
`resolved` and the events are the per-cycle accesses. -/
theorem plusTwo_toTimedPEHazardEvents_mem (a : Access) (neg ext rnd : Bool)
    (mask : Option ParsedMask) (write : Bool) (control : ParsedMaskExecutionControl)
    (events : List TimedPEAccess)
    (h : ParsedOperand.toTimedPEHazardEvents? (.mem a neg ext rnd mask) write control
      = some events) :
    (issueBankToRegisterBank a.bank = none ∧ events = []) ∨
      ∃ resolved : List DirectMemoryAccess,
        parsedHazardCycles.mapM (fun cycle =>
          ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false mask) true
            control.context.pe cycle control.context.bar0 control.context.bar1
            control.context.tWord) = some resolved ∧
        events = (parsedHazardCycles.zip resolved).flatMap
          (plusTwoHazardCycleEvents control a mask write) := by
  unfold ParsedOperand.toTimedPEHazardEvents? at h
  simp only [ParsedOperand.forHazardAddress] at h
  cases hb : issueBankToRegisterBank a.bank with
  | none =>
      simp only [hb] at h
      exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | some bank =>
      rw [hb] at h
      cases hm : parsedHazardCycles.mapM (fun cycle =>
          ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false mask) true
            control.context.pe cycle control.context.bar0 control.context.bar1
            control.context.tWord) with
      | none => simp [hm] at h
      | some resolved =>
          simp only [hm] at h
          exact Or.inr ⟨resolved, rfl, (Option.some.inj h).symm⟩

/-- Membership in the events of a `.mem` operand: either a per-cycle primary
read of the operand's own access, or the T-indirect secondary access. -/
theorem plusTwo_mem_toTimedPEHazardEvents_mem (a : Access) (neg ext rnd : Bool)
    (mask : Option ParsedMask) (write : Bool) (control : ParsedMaskExecutionControl)
    {ev : TimedPEAccess}
    (h : ev ∈ (ParsedOperand.toTimedPEHazardEvents? (.mem a neg ext rnd mask) write
      control).getD []) :
    (∃ cycle : Fin 4, ∃ direct : DirectMemoryAccess,
      ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false mask) true
          control.context.pe cycle control.context.bar0 control.context.bar1
          control.context.tWord = some direct ∧
        ev = TimedPEAccess.ofControl control direct write cycle) ∨
      (∃ cycle : Fin 4,
        ev = TimedPEAccess.ofControl control (tIndirectHazardAccess cycle) false cycle) := by
  obtain ⟨events, hevents, hevIn⟩ := plusTwo_mem_getD_option _ h
  rcases plusTwo_toTimedPEHazardEvents_mem a neg ext rnd mask write control events hevents with
    ⟨-, hempty⟩ | ⟨resolved, hmap, heventsEq⟩
  · rw [hempty] at hevIn
    simp at hevIn
  · rw [heventsEq] at hevIn
    obtain ⟨pair, hpair, hevPair⟩ := List.mem_flatMap.mp hevIn
    obtain ⟨cycle, direct⟩ := pair
    have hresolved : ParsedOperand.toDirectMemoryAccessMode?
        (.mem a false false false mask) true control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord = some direct :=
      plusTwo_mem_of_mem_zip_mapM hmap hpair
    simp only [plusTwoHazardCycleEvents] at hevPair
    by_cases hcond : (write && !parsedHazardPatternEnables mask cycle) = true
    · rw [ite_eq_left hcond] at hevPair
      simp at hevPair
    · rw [ite_eq_right hcond] at hevPair
      by_cases hind : (!write && a.region.tIndirect) = true
      · rw [ite_eq_left hind] at hevPair
        rw [List.mem_append] at hevPair
        rcases hevPair with hprimary | hindirect
        · simp only [List.mem_singleton] at hprimary
          exact Or.inl ⟨cycle, direct, hresolved, hprimary⟩
        · simp only [List.mem_singleton] at hindirect
          exact Or.inr ⟨cycle, hindirect⟩
      · rw [ite_eq_right hind] at hevPair
        rw [List.append_nil] at hevPair
        simp only [List.mem_singleton] at hevPair
        exact Or.inl ⟨cycle, direct, hresolved, hevPair⟩

/-- Every event of a *write* lowering is a write event. -/
theorem plusTwo_writeEvents_true (operand : ParsedOperand)
    (control : ParsedMaskExecutionControl) :
    ∀ ev ∈ (ParsedOperand.toTimedPEHazardEvents? operand true control).getD [],
      ev.write = true := by
  intro ev hev
  cases operand with
  | mem a neg ext rnd mask =>
      obtain ⟨events, hevents, hevIn⟩ := plusTwo_mem_getD_option _ hev
      rcases plusTwo_toTimedPEHazardEvents_mem a neg ext rnd mask true control events hevents with
        ⟨-, hempty⟩ | ⟨resolved, hmap, heventsEq⟩
      · rw [hempty] at hevIn
        simp at hevIn
      · rw [heventsEq] at hevIn
        obtain ⟨pair, hpair, hevPair⟩ := List.mem_flatMap.mp hevIn
        obtain ⟨cycle, direct⟩ := pair
        simp only [plusTwoHazardCycleEvents] at hevPair
        by_cases hcond : (true && !parsedHazardPatternEnables mask cycle) = true
        · rw [ite_eq_left hcond] at hevPair
          simp at hevPair
        · rw [ite_eq_right hcond] at hevPair
          have hfalse : (!true && a.region.tIndirect) = false := rfl
          rw [ite_eq_right (by rw [hfalse]; simp)] at hevPair
          rw [List.append_nil] at hevPair
          simp only [List.mem_singleton] at hevPair
          subst hevPair
          rfl
  | fixed kind => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | forward kind neg ext rnd => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | bar lm1 width mask => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | omr entry mask => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | matrix y width row => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | nowrite => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | l1bm width address => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | l2bm address l2b => simp [ParsedOperand.toTimedPEHazardEvents?] at hev
  | dar address => simp [ParsedOperand.toTimedPEHazardEvents?] at hev

/-- The row-level event list splits into the read events and the write events. -/
theorem plusTwo_toTimedPEHazardEvents_expr (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (events : List TimedPEAccess)
    (h : ParsedExpr.toTimedPEHazardEvents? expression control = some events) :
    ∃ readLists writeLists,
      expression.sources.mapM
          (fun o => ParsedOperand.toTimedPEHazardEvents? o false control) = some readLists ∧
      expression.destinations.mapM
          (fun o => ParsedOperand.toTimedPEHazardEvents? o true control) = some writeLists ∧
      events = readLists.flatten ++ writeLists.flatten := by
  unfold ParsedExpr.toTimedPEHazardEvents? at h
  cases hr : expression.sources.mapM
      (fun o => ParsedOperand.toTimedPEHazardEvents? o false control) with
  | none => simp [hr] at h
  | some readLists =>
      cases hw : expression.destinations.mapM
          (fun o => ParsedOperand.toTimedPEHazardEvents? o true control) with
      | none => simp [hr, hw] at h
      | some writeLists =>
          simp only [hr, hw, bind, Option.bind] at h
          exact ⟨readLists, writeLists, rfl, rfl, (Option.some.inj h).symm⟩

/-- The resolution ignores the operand's own mask once destination masking is
allowed: the mask only feeds a guard that `allowDestinationMask = true` disables. -/
theorem plusTwo_directAccess_mask_irrelevant (a : Access) (mask : Option ParsedMask)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false mask) true pe cycle
        bar0 bar1 tWord =
      ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false none) true pe cycle
        bar0 bar1 tWord := by
  simp [ParsedOperand.toDirectMemoryAccessMode?]

/-- A source access of the line comes from a `.mem` operand of some row, resolved
at some cycle — or it is the T-indirect secondary access. -/
theorem plusTwo_exists_source_access_of_mem_lineSourceAccesses
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    {access : DirectMemoryAccess} (member : access ∈ lineSourceAccesses expressions control) :
    (∃ (expression : ParsedExpr) (_ : expression ∈ expressions)
      (a : Access) (neg ext rnd : Bool) (mask : Option ParsedMask)
      (_ : ParsedOperand.mem a neg ext rnd mask ∈ expression.sources)
      (cycle : Fin 4),
      ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false none) true
          control.context.pe cycle control.context.bar0 control.context.bar1
          control.context.tWord = some access) ∨
    (∃ cycle : Fin 4, access = tIndirectHazardAccess cycle) := by
  classical
  unfold lineSourceAccesses at member
  obtain ⟨ev, hevmem, hev⟩ := List.mem_filterMap.mp member
  by_cases hw : ev.write = true
  · rw [hw] at hev
    exact absurd hev (by simp)
  · have hw' : ev.write = false := by
      cases hwv : ev.write with
      | false => rfl
      | true => exact absurd hwv hw
    rw [hw'] at hev
    simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at hev
    obtain ⟨eventList, heventList, hevflatten⟩ := List.mem_flatten.mp hevmem
    obtain ⟨expression, hexp, rfl⟩ := List.mem_map.mp heventList
    obtain ⟨events, hevents, hevIn⟩ := plusTwo_mem_getD_option _ hevflatten
    obtain ⟨readLists, writeLists, hreads, hwrites, heventsEq⟩ :=
      plusTwo_toTimedPEHazardEvents_expr expression control events hevents
    rw [heventsEq] at hevIn
    rw [List.mem_append] at hevIn
    rcases hevIn with hread | hwrite
    · obtain ⟨operand, hoperand, hopEvent⟩ := plusTwo_mem_flatten_of_mapM _ _ _ hreads hread
      cases operand with
      | mem a neg ext rnd mask =>
          rcases plusTwo_mem_toTimedPEHazardEvents_mem a neg ext rnd mask false control
            hopEvent with ⟨cycle, direct, hresolved, hevent⟩ | ⟨cycle, hevent⟩
          · have hdir : direct = access := by
              have h1 : ev.access = direct := by simp [hevent, TimedPEAccess.ofControl]
              rw [hev] at h1
              exact h1.symm
            have hres := hresolved
            rw [hdir] at hres
            rw [plusTwo_directAccess_mask_irrelevant] at hres
            exact Or.inl ⟨expression, hexp, a, neg, ext, rnd, mask, hoperand, cycle, hres⟩
          · refine Or.inr ⟨cycle, ?_⟩
            have h1 : ev.access = tIndirectHazardAccess cycle := by
              simp [hevent, TimedPEAccess.ofControl]
            rw [hev] at h1
            exact h1
      | fixed kind => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | forward kind neg ext rnd => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | bar lm1 width mask => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | omr entry mask => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | matrix y width row => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | nowrite => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | l1bm width address => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | l2bm address l2b => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
      | dar address => simp [ParsedOperand.toTimedPEHazardEvents?] at hopEvent
    · obtain ⟨operand, hoperand, hopEvent⟩ := plusTwo_mem_flatten_of_mapM _ _ _ hwrites hwrite
      have htrue := plusTwo_writeEvents_true operand control _ hopEvent
      rw [hw'] at htrue
      simp at htrue


/-! ## 4. The canonical cycle access, and why there are only four of them -/

/-- The canonical resolution of one parsed access at one PE cycle. -/
def plusTwoCycleAccess (a : Access) (control : ParsedMaskExecutionControl) (cycle : Fin 4) :
    Option DirectMemoryAccess :=
  ParsedOperand.toDirectMemoryAccessMode? (.mem a false false false none) true
    control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord

/-- The resolution only depends on the access through its bank and its `Region`:
the width, the four cycle addresses and the T-indirect / MADPE flags are all
fields of the region, and the remaining inputs are the line's control. -/
theorem plusTwoCycleAccess_congr {a a' : Access} (hbank : a.bank = a'.bank)
    (hregion : a.region = a'.region) (control : ParsedMaskExecutionControl) (cycle : Fin 4) :
    plusTwoCycleAccess a control cycle = plusTwoCycleAccess a' control cycle := by
  obtain ⟨bank, region⟩ := a
  obtain ⟨bank', region'⟩ := a'
  simp only at hbank hregion
  rw [hbank, hregion]

/-- The resolved access has the register bank the access resolves to. -/
theorem plusTwoCycleAccess_bank {a : Access} {control : ParsedMaskExecutionControl}
    {cycle : Fin 4} {d : DirectMemoryAccess} (h : plusTwoCycleAccess a control cycle = some d) :
    issueBankToRegisterBank a.bank = some d.bank := by
  obtain ⟨bank, region⟩ := a
  cases bank <;>
    simp only [plusTwoCycleAccess, ParsedOperand.toDirectMemoryAccessMode?,
      issueBankToRegisterBank] at h ⊢
  all_goals (try (repeat' split at h)) <;> grind

/-- `issueBankToRegisterBank` is injective at `.lm0`. -/
theorem issueBankToRegisterBank_eq_lm0 {b : Issue.Bank}
    (h : issueBankToRegisterBank b = some .lm0) : b = .lm0 := by
  cases b <;> simp [issueBankToRegisterBank] at h ⊢

/-- A `.mem` operand's access is a member of the row's access list. -/
theorem plusTwo_mem_accesses {sources : List ParsedOperand} {a : Access} {neg ext rnd : Bool}
    {mask : Option ParsedMask} (h : ParsedOperand.mem a neg ext rnd mask ∈ sources) :
    a ∈ ParsedOperand.accesses sources :=
  List.mem_filterMap.mpr ⟨_, h, by simp⟩

/-- **The issue checker's shared-read rule.**  All `.mem` source operands of one
line that resolve to the same register bank carry the same `Region`.  This is
`Issue.readsAgree` transported from the projected issue records back to the
parsed rows. -/
def SourceRegionsAgree (expressions : List ParsedExpr) : Prop :=
  ∀ (e : ParsedExpr), e ∈ expressions → ∀ (f : ParsedExpr), f ∈ expressions →
    ∀ a ∈ ParsedOperand.accesses e.sources, ∀ b ∈ ParsedOperand.accesses f.sources,
      a.bank = b.bank → a.region = b.region

theorem plusTwo_toIssueExpr_mem_projectFrom (expressions : List ParsedExpr) (nextId : Nat)
    {expression : ParsedExpr} (member : expression ∈ expressions) :
    ∃ id, expression.toIssueExpr id ∈ projectFrom nextId expressions := by
  induction expressions generalizing nextId with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨nextId, by simp [projectFrom]⟩
      · obtain ⟨id, hid⟩ := ih (nextId + 1) member
        exact ⟨id, List.mem_cons_of_mem _ hid⟩

/-- **`SourceRegionsAgree` follows from the line's issue check.** -/
theorem plusTwo_sourceRegionsAgree_of_check (expressions : List ParsedExpr)
    (checked : checkParsedLine expressions = true) : SourceRegionsAgree expressions := by
  have legal := parsed_check_sound expressions checked
  unfold LegalParsedLine at legal
  obtain ⟨-, -, -, -, -, -, -, -, hreads, -, -, -, -, -, -, -, -⟩ := legal
  unfold readsAgree at hreads
  intro e he f hf a ha b hb hbank
  obtain ⟨idE, hidE⟩ := plusTwo_toIssueExpr_mem_projectFrom expressions 0 he
  obtain ⟨idF, hidF⟩ := plusTwo_toIssueExpr_mem_projectFrom expressions 0 hf
  have ha' : a ∈ (e.toIssueExpr idE).reads := by simpa [ParsedExpr.toIssueExpr] using ha
  have hb' : b ∈ (f.toIssueExpr idF).reads := by simpa [ParsedExpr.toIssueExpr] using hb
  exact hreads _ hidE _ hidF a ha' b hb' hbank

/-- **All LM0 accesses the line's hazard lowering reports are cycle accesses of
one region.**  The line's `.mem` sources share a `Region` per bank
(`SourceRegionsAgree`), and the resolution is a function of
`(bank, region, control, cycle)`, so at each of the four cycles there is at most
one LM0 access. -/
theorem plusTwo_lineSourceAccesses_lm0_eq_cycleAccess
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (agree : SourceRegionsAgree expressions) {a0 : Access}
    (a0mem : a0 ∈ expressions.flatMap (fun e => ParsedOperand.accesses e.sources))
    (a0lm0 : a0.bank = .lm0)
    {access : DirectMemoryAccess} (member : access ∈ lineSourceAccesses expressions control)
    (lm0 : access.bank = .lm0) :
    ∃ cycle : Fin 4, plusTwoCycleAccess a0 control cycle = some access := by
  rcases plusTwo_exists_source_access_of_mem_lineSourceAccesses expressions control member with
    ⟨e, he, a, neg, ext, rnd, mask, hoperand, cycle, hres⟩ | ⟨cycle, hres⟩
  · have hamem : a ∈ ParsedOperand.accesses e.sources := plusTwo_mem_accesses hoperand
    obtain ⟨e0, he0, ha0⟩ := List.mem_flatMap.mp a0mem
    have habank : issueBankToRegisterBank a.bank = some .lm0 := by
      rw [plusTwoCycleAccess_bank hres, lm0]
    have hbankEq : a.bank = a0.bank := by
      rw [issueBankToRegisterBank_eq_lm0 habank, a0lm0]
    have hregion : a.region = a0.region := agree e he e0 he0 a hamem a0 ha0 hbankEq
    exact ⟨cycle, (plusTwoCycleAccess_congr hbankEq hregion control cycle).symm.trans hres⟩
  · exfalso
    rw [hres] at lm0
    simp [tIndirectHazardAccess] at lm0

/-- **One cycle of one region reads at most two input words.** -/
theorem plusTwo_cycleAccess_inputs_card_le_two (a : Access)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) :
    (Finset.univ.filter (fun j : Fin 20 => ∃ d : DirectMemoryAccess,
      plusTwoCycleAccess a control cycle = some d ∧
        plusTwoInputWord j ∈ accessRegion d)).card ≤ 2 := by
  classical
  cases h : plusTwoCycleAccess a control cycle with
  | none =>
      have hempty : (Finset.univ.filter (fun j : Fin 20 => ∃ d : DirectMemoryAccess,
          none = some d ∧ plusTwoInputWord j ∈ accessRegion d)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨d, hd, -⟩ := hj
        simp at hd
      rw [hempty]
      simp
  | some d =>
      have heq : (Finset.univ.filter (fun j : Fin 20 => ∃ d' : DirectMemoryAccess,
          some d = some d' ∧ plusTwoInputWord j ∈ accessRegion d')) =
          (Finset.univ.filter (fun j : Fin 20 => plusTwoInputWord j ∈ accessRegion d)) := by
        apply Finset.filter_congr
        intro j _
        constructor
        · rintro ⟨d', hd', hj⟩
          have hsame : d = d' := Option.some.inj hd'
          subst hsame
          exact hj
        · intro hj
          exact ⟨d, rfl, hj⟩
      rw [heq]
      exact plusTwo_accessRegion_inputs_card_le_two d

theorem plusTwo_fin_four_cases (c : Fin 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  rcases c with ⟨n, hn⟩
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h with h | h | h | h <;> subst h <;> simp

/-- **The per-line read capacity: a legal `.pe` line's footprint contains at
most eight distinct input words.**  The line may have any number of rows; the
issue checker's shared-region rule collapses every LM0 source read of the line
to the four cycle accesses of one region, and each of those is a window of at
most four consecutive words, holding at most two of the twenty odd input
addresses. -/
theorem plusTwoFootprint_inputs_card_le_eight (expressions : List NormalizedExpr)
    (agree : SourceRegionsAgree (expressions.map NormalizedExpr.toParsed))
    (state : State) :
    (Finset.univ.filter (fun j : Fin 20 =>
      plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) state)).card ≤ 8 := by
  classical
  set control := parsedPEHazardControl state plusTwoPE with hcontrol
  set sources := (expressions.map NormalizedExpr.toParsed).flatMap
    (fun e => ParsedOperand.accesses e.sources) with hsources
  have key : ∀ (j : Fin 20),
      plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) state →
      ∃ access ∈ lineSourceAccesses (expressions.map NormalizedExpr.toParsed) control,
        plusTwoInputWord j ∈ accessRegion access ∧ access.bank = .lm0 := by
    intro j hj
    obtain ⟨access, haccess, hjreg⟩ := (plusTwoLineFootprint_pe expressions state).mp hj
    have haccess' : access ∈ lineSourceAccesses (expressions.map NormalizedExpr.toParsed)
        control := by
      rw [hcontrol]
      exact haccess
    have hbank : access.bank = .lm0 := by
      have := accessRegion_bank access hjreg
      rw [plusTwoInputWord_bank_eq] at this
      exact this.symm
    exact ⟨access, haccess', hjreg, hbank⟩
  by_cases hex : ∃ a, a ∈ sources ∧ a.bank = .lm0
  · obtain ⟨a0, ha0mem, ha0bank⟩ := hex
    set window : Fin 4 → Finset (Fin 20) := fun c =>
      Finset.univ.filter (fun j : Fin 20 => ∃ d : DirectMemoryAccess,
        plusTwoCycleAccess a0 control c = some d ∧ plusTwoInputWord j ∈ accessRegion d)
      with hwindow
    have hwindowCard : ∀ c, (window c).card ≤ 2 := fun c =>
      plusTwo_cycleAccess_inputs_card_le_two a0 control c
    have hsubset : (Finset.univ.filter (fun j : Fin 20 =>
        plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) state)) ⊆
        (window 0 ∪ window 1) ∪ (window 2 ∪ window 3) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨access, haccess, hjreg, hbank⟩ := key j hj
      have ha0mem' : a0 ∈ (expressions.map NormalizedExpr.toParsed).flatMap
          (fun e => ParsedOperand.accesses e.sources) := by rw [← hsources]; exact ha0mem
      obtain ⟨cycle, hcycle⟩ := plusTwo_lineSourceAccesses_lm0_eq_cycleAccess
        (expressions.map NormalizedExpr.toParsed) control agree ha0mem' ha0bank haccess hbank
      have hmem : ∀ c : Fin 4, plusTwoCycleAccess a0 control c = some access →
          j ∈ window c := by
        intro c hc
        rw [hwindow]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨access, hc, hjreg⟩
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
      rcases plusTwo_fin_four_cases cycle with h | h | h | h
      · subst h
        exact Or.inl (Or.inl (hmem 0 hcycle))
      · subst h
        exact Or.inl (Or.inr (hmem 1 hcycle))
      · subst h
        exact Or.inr (Or.inl (hmem 2 hcycle))
      · subst h
        exact Or.inr (Or.inr (hmem 3 hcycle))
    have step1 : (window 0 ∪ window 1).card ≤ (window 0).card + (window 1).card :=
      Finset.card_union_le _ _
    have step2 : (window 2 ∪ window 3).card ≤ (window 2).card + (window 3).card :=
      Finset.card_union_le _ _
    have step3 : ((window 0 ∪ window 1) ∪ (window 2 ∪ window 3)).card ≤
        (window 0 ∪ window 1).card + (window 2 ∪ window 3).card :=
      Finset.card_union_le _ _
    have h0 := hwindowCard 0
    have h1 := hwindowCard 1
    have h2 := hwindowCard 2
    have h3 := hwindowCard 3
    calc (Finset.univ.filter (fun j : Fin 20 =>
          plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) state)).card
        ≤ ((window 0 ∪ window 1) ∪ (window 2 ∪ window 3)).card :=
          Finset.card_le_card hsubset
      _ ≤ (window 0 ∪ window 1).card + (window 2 ∪ window 3).card := step3
      _ ≤ ((window 0).card + (window 1).card) + ((window 2).card + (window 3).card) := by
          omega
      _ ≤ 8 := by omega
  · have hempty : (Finset.univ.filter (fun j : Fin 20 =>
        plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) state)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨access, haccess, hjreg, hbank⟩ := key j hj
      rcases plusTwo_exists_source_access_of_mem_lineSourceAccesses
        (expressions.map NormalizedExpr.toParsed) control haccess with
        ⟨e, he, a, neg, ext, rnd, mask, hoperand, cycle, hres⟩ | ⟨cycle, hres⟩
      · have hamem : a ∈ sources := by
          rw [hsources]
          exact List.mem_flatMap.mpr ⟨e, he, plusTwo_mem_accesses hoperand⟩
        have habank : issueBankToRegisterBank a.bank = some .lm0 := by
          rw [plusTwoCycleAccess_bank hres, hbank]
        exact hex ⟨a, hamem, issueBankToRegisterBank_eq_lm0 habank⟩
      · exfalso
        rw [hres] at hbank
        simp [tIndirectHazardAccess] at hbank
    rw [hempty]
    simp


/-! ## 5. The footprint is a function of the PE context, not of the state

`plusTwoLineFootprint` only ever consults `parsedPEHazardControl`, i.e. the PE
context's BAR/T words, the mask directive and the hazard clock.  Two states that
agree on those have the same footprint, so the *only* reason the read capacity
`8` does not immediately bound the line count is that the BAR/T context is
updated by the program. -/

theorem plusTwoLineFootprint_context_determined (line : InstructionLine) (s s' : State)
    (hcontext : s.peContext plusTwoPE = s'.peContext plusTwoPE)
    (hdirective : s.maskDirective = s'.maskDirective)
    (hclock : s.hazardClock = s'.hazardClock) :
    plusTwoLineFootprint line s = plusTwoLineFootprint line s' := by
  have hcontrol : parsedPEHazardControl s plusTwoPE = parsedPEHazardControl s' plusTwoPE := by
    unfold parsedPEHazardControl
    rw [hcontext, hdirective, hclock]
  cases line with
  | pe expressions =>
      simp only [plusTwoLineFootprint, peLineSourceAccesses, hcontrol]
  | nop count wait => rfl
  | mv transfer => rfl

/-- **The initial state's footprint is input-independent.**  `plusTwoInitialState`
only varies the LM0 bank, which the hazard control never reads. -/
theorem plusTwoInitialState_footprint_eq (line : InstructionLine)
    (input input' : PlusTwoWords) :
    plusTwoLineFootprint line (plusTwoSpec.initial input) =
      plusTwoLineFootprint line (plusTwoSpec.initial input') := by
  apply plusTwoLineFootprint_context_determined <;> rfl

/-! ## 6. Pinning the kernel's witness states

`exists_footprint_meets_of_output_ne_chan` reports `∃ s s'` for the witness
states.  For a *count* the states have to be pinned to the prefix states of the
two executions, otherwise the existential is worthless: a single line can read
every input word in *some* state, because the resolved address is
`(bar0 + regionAddressAt cycle) / words * words`.

The theorem below is that strengthening.  The induction is the one of
`execute_agreeOutside_of_determined_chan`, with the conclusion carrying the
prefix. -/

theorem plusTwo_exists_prefix_footprint_meets_chan
    (footprint : InstructionLine → State → Set WordRef) (pe : PEId) (D : Set WordRef)
    (w : WordRef) (hw : w ∉ D) :
    ∀ (program : List InstructionLine),
      (∀ line ∈ program, LineDeterminedAtChan footprint pe line) →
      ∀ (s0 s0' : State), FilesAgreeOn Dᶜ (s0.peRegisters pe) (s0'.peRegisters pe) →
      ChanAgree pe s0 s0' → ∀ (final final' : State),
      ProofsLean.execute plusTwoSealedMachine program s0 = some final →
      ProofsLean.execute plusTwoSealedMachine program s0' = some final' →
      wordValue (final.peRegisters pe) w ≠ wordValue (final'.peRegisters pe) w →
      ∃ (pre : List InstructionLine) (line : InstructionLine) (rest : List InstructionLine)
        (s s' : State),
        program = pre ++ line :: rest ∧
          ProofsLean.execute plusTwoSealedMachine pre s0 = some s ∧
          ProofsLean.execute plusTwoSealedMachine pre s0' = some s' ∧
          ∃ v : WordRef, v ∈ D ∧ (v ∈ footprint line s ∨ v ∈ footprint line s') := by
  intro program
  induction program with
  | nil =>
      intro determined s0 s0' hInit hChan final final' run run' different
      simp only [ProofsLean.execute] at run run'
      have same : final = s0 := (Option.some.inj run).symm
      have same' : final' = s0' := (Option.some.inj run').symm
      subst same
      subst same'
      exact absurd (hInit w hw) different
  | cons line rest ih =>
      intro determined s0 s0' hInit hChan final final' run run' different
      rw [ProofsLean.execute.eq_2] at run run'
      cases hstep : plusTwoSealedMachine.step line s0 with
      | none => rw [hstep] at run; simp at run
      | some middle =>
          rw [hstep] at run
          simp only [Option.bind_some] at run
          cases hstep' : plusTwoSealedMachine.step line s0' with
          | none => rw [hstep'] at run'; simp at run'
          | some middle' =>
              rw [hstep'] at run'
              simp only [Option.bind_some] at run'
              by_cases hmeet : ∃ v : WordRef, v ∈ D ∧
                  (v ∈ footprint line s0 ∨ v ∈ footprint line s0')
              · exact ⟨[], line, rest, s0, s0', rfl, rfl, rfl, hmeet⟩
              · push Not at hmeet
                have agrees : FilesAgreeOn (footprint line s0 ∪ footprint line s0')
                    (s0.peRegisters pe) (s0'.peRegisters pe) :=
                  hInit.mono (fun v hv => by
                    by_contra outside
                    have hnot := hmeet v (by simpa using outside)
                    rcases hv with hv | hv
                    · exact hnot.1 hv
                    · exact hnot.2 hv)
                obtain ⟨writes, commit, commit', chan⟩ :=
                  determined line (by simp) s0 s0' middle middle' agrees hChan hstep hstep'
                have hBank : FilesAgreeOn Dᶜ (middle.peRegisters pe)
                    (middle'.peRegisters pe) := by
                  rw [commit, commit']
                  exact commitParsedMaskedWrites_congr_on _ _ writes Dᶜ hInit
                obtain ⟨pre, mid, rest', s, s', heq, hrun, hrun', hmeet'⟩ :=
                  ih (fun item mem => determined item (List.mem_cons_of_mem _ mem))
                    middle middle' hBank chan final final' run run' different
                refine ⟨line :: pre, mid, rest', s, s', by simp [heq], ?_, ?_, hmeet'⟩
                · rw [ProofsLean.execute.eq_2, hstep]
                  simp only [Option.bind_some]
                  exact hrun
                · rw [ProofsLean.execute.eq_2, hstep']
                  simp only [Option.bind_some]
                  exact hrun'

/-! ## 7. The one-hot input family and the pinned read witness -/

/-- The input that is `1` at index `j` and `0` elsewhere: admissible, and it
differs from the all-zero input exactly at `j`. -/
def plusTwoOneHotWords (j : Fin 20) : PlusTwoWords := fun k => if k = j then 1 else 0

theorem plusTwoOneHotWords_admissible (j : Fin 20) :
    plusTwoSpec.admissible (plusTwoOneHotWords j) := by
  intro k
  by_cases same : k = j <;> simp [plusTwoOneHotWords, same]

theorem plusTwoOneHotWords_agree (j : Fin 20) :
    ∀ k, k ≠ j → plusTwoZeroWords k = plusTwoOneHotWords j k := by
  intro k other
  simp [plusTwoZeroWords, plusTwoOneHotWords, other]

/-- **Every input word is read at a pinned prefix position.**  For a correct
discharged program, the LM0 word of input `j` lies in the footprint of a `.pe`
line of the program, in one of the two states in front of that line in the
executions of the all-zero input and of the one-hot input at `j`.  The all-zero
side is the *same* execution for every `j`; the one-hot side is not, which is
exactly why the read capacity needs a state-fixing argument to become a line
count. -/
theorem plusTwo_exists_prefix_pe_read_of_chan (program : List InstructionLine)
    (determined : ∀ line ∈ program,
      LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program) (j : Fin 20) :
    ∃ (pre : List InstructionLine) (expressions : List NormalizedExpr)
      (rest : List InstructionLine) (s s' : State),
      program = pre ++ InstructionLine.pe expressions :: rest ∧
        ProofsLean.execute plusTwoSealedMachine pre
          (plusTwoSpec.initial plusTwoZeroWords) = some s ∧
        ProofsLean.execute plusTwoSealedMachine pre
          (plusTwoSpec.initial (plusTwoOneHotWords j)) = some s' ∧
        (plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) s ∨
          plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) s') := by
  obtain ⟨final, run, post⟩ := correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  obtain ⟨final', run', post'⟩ :=
    correct.2 (plusTwoOneHotWords j) (plusTwoOneHotWords_admissible j)
  have different : wordValue (final.peRegisters plusTwoPE) (plusTwoOutputWord j) ≠
      wordValue (final'.peRegisters plusTwoPE) (plusTwoOutputWord j) := by
    have low := (post j).2
    have low' := (post' j).2
    simp only [plusTwoOutputWord, wordValue_lm1]
    rw [low, low']
    simp [plusTwoZeroWords, plusTwoOneHotWords]
  have outside : plusTwoOutputWord j ∉ ({plusTwoInputWord j} : Set WordRef) := by
    intro mem
    exact plusTwoOutputWord_not_inputWord j (Set.mem_singleton_iff.mp mem)
  obtain ⟨pre, line, rest, s, s', heq, hrun, hrun', v, hvD, hvfoot⟩ :=
    plusTwo_exists_prefix_footprint_meets_chan plusTwoLineFootprint plusTwoPE
      ({plusTwoInputWord j} : Set WordRef) (plusTwoOutputWord j) outside program
      determined
      (plusTwoSpec.initial plusTwoZeroWords)
      (plusTwoSpec.initial (plusTwoOneHotWords j))
      (by
        rw [plusTwoSpec_initial, plusTwoSpec_initial]
        exact plusTwoInitialPERegisters_agree_outside plusTwoZeroWords
          (plusTwoOneHotWords j) j (plusTwoOneHotWords_agree j))
      (by
        rw [plusTwoSpec_initial, plusTwoSpec_initial]
        exact plusTwoInitialState_chanAgree plusTwoZeroWords (plusTwoOneHotWords j) plusTwoPE)
      final final' run run' different
  have hvEq : v = plusTwoInputWord j := Set.mem_singleton_iff.mp hvD
  subst hvEq
  cases line with
  | nop count wait =>
      exact absurd hvfoot (by
        rcases hvfoot with h | h <;> simp [plusTwoLineFootprint] at h)
  | mv transfer =>
      exact absurd hvfoot (by
        rcases hvfoot with h | h <;> simp [plusTwoLineFootprint] at h)
  | pe expressions =>
      exact ⟨pre, expressions, rest, s, s', heq, hrun, hrun', hvfoot⟩


/-- The discharged-class form of `plusTwo_exists_prefix_pe_read_of_chan`. -/
theorem plusTwo_exists_prefix_pe_read (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedALULine line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program) (j : Fin 20) :
    ∃ (pre : List InstructionLine) (expressions : List NormalizedExpr)
      (rest : List InstructionLine) (s s' : State),
      program = pre ++ InstructionLine.pe expressions :: rest ∧
        ProofsLean.execute plusTwoSealedMachine pre
          (plusTwoSpec.initial plusTwoZeroWords) = some s ∧
        ProofsLean.execute plusTwoSealedMachine pre
          (plusTwoSpec.initial (plusTwoOneHotWords j)) = some s' ∧
        (plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) s ∨
          plusTwoInputWord j ∈ plusTwoLineFootprint (.pe expressions) s') :=
  plusTwo_exists_prefix_pe_read_of_chan program
    (fun line _ => lineDeterminedAtChan_of_aluRows line (discharged line ‹_›)) correct j

/-! ## 8. The issue check is a consequence of a successful step -/

theorem plusTwo_check_of_step_pe (expressions : List NormalizedExpr) (state next : State)
    (step : plusTwoSealedMachine.step (.pe expressions) state = some next) :
    checkParsedTopLine (InstructionLine.pe expressions).toParsed = true :=
  executeIntegerProducerInstructionLine_accepted_of_ok (.pe expressions) state next
    (stepTo_pe expressions state next step)

/-- **A checked plain-ALU line's sources share a region per bank** — the capacity
hypothesis, obtained from any state in which the line steps successfully. -/
theorem plusTwo_sourceRegionsAgree_of_step_pe (expressions : List NormalizedExpr)
    (state next : State) (step : plusTwoSealedMachine.step (.pe expressions) state = some next) :
    SourceRegionsAgree (expressions.map NormalizedExpr.toParsed) :=
  plusTwo_sourceRegionsAgree_of_check _
    (by
      have := plusTwo_check_of_step_pe expressions state next step
      simpa [InstructionLine.toParsed, checkParsedTopLine] using this)

/-- Every line of a program that executes successfully has a successful step
from some state. -/
theorem plusTwo_exists_step_of_mem (program : List InstructionLine) :
    ∀ (state final : State),
      ProofsLean.execute plusTwoSealedMachine program state = some final →
      ∀ line ∈ program, ∃ s next : State, plusTwoSealedMachine.step line s = some next := by
  induction program with
  | nil => intro state final run line mem; simp at mem
  | cons head rest ih =>
      intro state final run line mem
      rw [ProofsLean.execute.eq_2] at run
      cases hstep : plusTwoSealedMachine.step head state with
      | none => rw [hstep] at run; simp at run
      | some middle =>
          rw [hstep] at run
          simp only [Option.bind_some] at run
          rcases List.mem_cons.mp mem with rfl | mem
          · exact ⟨state, middle, hstep⟩
          · exact ih middle final run line mem

/-- **Every `.pe` line of a correct program passes the issue check.** -/
theorem plusTwo_check_of_correct_mem (program : List InstructionLine)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (expressions : List NormalizedExpr) (mem : InstructionLine.pe expressions ∈ program) :
    checkParsedTopLine (InstructionLine.pe expressions).toParsed = true := by
  obtain ⟨final, run, -⟩ := correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  rw [plusTwoSpec_initial] at run
  obtain ⟨s, next, hstep⟩ :=
    plusTwo_exists_step_of_mem program (plusTwoSpec.initial plusTwoZeroWords) final run
      (.pe expressions) mem
  exact plusTwo_check_of_step_pe expressions s next hstep

/-- A union bound: `n` sets of size at most `k` cover at most `n * k` points. -/
theorem plusTwo_card_biUnion_le_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) (n : Nat) (h : ∀ a ∈ s, (f a).card ≤ n) :
    (s.biUnion f).card ≤ s.card * n := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      have h1 : (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card :=
        Finset.card_union_le _ _
      have h2 : (s.biUnion f).card ≤ s.card * n :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have h3 : (f a).card ≤ n := h a (Finset.mem_insert_self _ _)
      rw [Finset.card_insert_of_notMem ha, Nat.add_mul, one_mul]
      omega

/-! ## 9. The read count as a line count, under initial-state coverage -/

/-- **Twenty input words at one state need three lines.**  If every input word
lies in some line's footprint computed at the *same* state, then the program has
at least three lines: each line's footprint holds at most eight input words
(`plusTwoFootprint_inputs_card_le_eight`), and `3 * 8 = 24 > 20`. -/
theorem plusTwo_length_of_initial_coverage (program : List InstructionLine)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (coverage : ∀ j : Fin 20, ∃ line ∈ program,
      plusTwoInputWord j ∈ plusTwoLineFootprint line
        (plusTwoSpec.initial plusTwoZeroWords)) :
    20 ≤ 8 * program.length := by
  classical
  set cover : InstructionLine → Finset (Fin 20) := fun line =>
    Finset.univ.filter (fun j : Fin 20 =>
      plusTwoInputWord j ∈ plusTwoLineFootprint line (plusTwoSpec.initial plusTwoZeroWords))
    with hcover
  have hcard : ∀ line ∈ program.toFinset, (cover line).card ≤ 8 := by
    intro line mem
    have memList : line ∈ program := by simpa using mem
    cases line with
    | nop count wait =>
        have hempty : cover (InstructionLine.nop count wait) = ∅ := by
          rw [hcover]
          simp [plusTwoLineFootprint]
        rw [hempty]
        simp
    | mv transfer =>
        have hempty : cover (InstructionLine.mv transfer) = ∅ := by
          rw [hcover]
          simp [plusTwoLineFootprint]
        rw [hempty]
        simp
    | pe expressions =>
        have checked := plusTwo_check_of_correct_mem program correct expressions memList
        have agree := plusTwo_sourceRegionsAgree_of_check _
          (by simpa [InstructionLine.toParsed, checkParsedTopLine] using checked)
        exact plusTwoFootprint_inputs_card_le_eight expressions agree _
  have hsubset : (Finset.univ : Finset (Fin 20)) ⊆ program.toFinset.biUnion cover := by
    intro j _
    obtain ⟨line, mem, hj⟩ := coverage j
    refine Finset.mem_biUnion.mpr ⟨line, by simpa using mem, ?_⟩
    rw [hcover]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj
  have h1 : (Finset.univ : Finset (Fin 20)).card ≤ (program.toFinset.biUnion cover).card :=
    Finset.card_le_card hsubset
  have h2 : (program.toFinset.biUnion cover).card ≤ program.toFinset.card * 8 :=
    plusTwo_card_biUnion_le_mul _ _ 8 hcard
  have h3 : program.toFinset.card ≤ program.length := List.toFinset_card_le program
  have h4 : (Finset.univ : Finset (Fin 20)).card = 20 := by simp
  omega

/-- **`3 ≤ score` from initial-state coverage.** -/
theorem plusTwo_lowerBound_three_of_initial_coverage (program : List InstructionLine)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (coverage : ∀ j : Fin 20, ∃ line ∈ program,
      plusTwoInputWord j ∈ plusTwoLineFootprint line
        (plusTwoSpec.initial plusTwoZeroWords)) :
    3 ≤ ProofsLean.score plusTwoSealedMachine program := by
  have hlen := plusTwo_length_of_initial_coverage program correct coverage
  have hscore : program.length ≤ ProofsLean.score plusTwoSealedMachine program :=
    ProofsLean.length_le_score plusTwoSealedMachine program
  omega

/-! ## 10. `LowerBound 2`, unconditionally on the discharged line class -/

/-- **No one-line program in the discharged class is correct.**  For every input
index `j` the pinned kernel produces a prefix position and two states whose
footprint contains the LM0 word of input `j`; a one-line program has only the
empty prefix, so both states are the *initial* states, whose footprints are
input-independent.  All twenty input words would then lie in one footprint,
which the capacity bounds by eight. -/
theorem plusTwo_lowerBound_two_of_chan (program : List InstructionLine)
    (determined : ∀ line ∈ program,
      LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program) :
    2 ≤ ProofsLean.score plusTwoSealedMachine program := by
  by_contra h
  push Not at h
  have lengthLe : program.length ≤ ProofsLean.score plusTwoSealedMachine program :=
    ProofsLean.length_le_score plusTwoSealedMachine program
  have lengthLt : program.length < 2 := by omega
  have initialZero : ∀ k : Fin 20,
      ((plusTwoInitialState plusTwoZeroWords).peRegisters plusTwoPE).lm1
        (plusTwoLowAddress k) = 0 :=
    fun k => plusTwoInitialState_lm1_zero plusTwoZeroWords (plusTwoLowAddress k)
  cases program with
  | nil =>
      obtain ⟨result, executed, post⟩ := correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
      rw [plusTwoSpec_initial] at executed
      have resultEq : result = plusTwoInitialState plusTwoZeroWords :=
        (Option.some.inj executed).symm
      subst resultEq
      have target := (post ⟨0, by decide⟩).2
      rw [initialZero] at target
      simp [plusTwoZeroWords] at target
  | cons line rest =>
      cases rest with
      | cons second tail =>
          simp only [List.length_cons] at lengthLt
          omega
      | nil =>
          obtain ⟨pre0, expressions, rest0, _t0, _t0', heq0, _hrun0, _hrun0', -⟩ :=
            plusTwo_exists_prefix_pe_read_of_chan (line :: []) determined correct ⟨0, by decide⟩
          have hlen0 : pre0.length = 0 ∧ rest0.length = 0 := by
            have := congrArg List.length heq0
            simp only [List.length_cons, List.length_nil, List.length_append] at this
            omega
          have hpre0 : pre0 = [] := List.length_eq_zero_iff.mp hlen0.1
          have hrest0 : rest0 = [] := List.length_eq_zero_iff.mp hlen0.2
          subst hpre0
          subst hrest0
          simp only [List.nil_append, List.append_nil] at heq0
          have hline : line = InstructionLine.pe expressions := by
            simpa using heq0
          subst hline
          have hcover : ∀ j : Fin 20, plusTwoInputWord j ∈
              plusTwoLineFootprint (.pe expressions)
                (plusTwoSpec.initial plusTwoZeroWords) := by
            intro j
            obtain ⟨pre, expressions', rest, s, s', heq, hrun, hrun', hfp⟩ :=
              plusTwo_exists_prefix_pe_read_of_chan (.pe expressions :: []) determined correct j
            have hlen : pre.length = 0 ∧ rest.length = 0 := by
              have := congrArg List.length heq
              simp only [List.length_cons, List.length_nil, List.length_append] at this
              omega
            have hpre : pre = [] := List.length_eq_zero_iff.mp hlen.1
            have hrest : rest = [] := List.length_eq_zero_iff.mp hlen.2
            subst hpre
            subst hrest
            simp only [List.nil_append, List.append_nil] at heq
            obtain ⟨hpe, -⟩ := List.cons.inj heq
            have hexpr : expressions' = expressions := by
              simpa using hpe.symm
            rw [hexpr] at hfp
            have hs : s = plusTwoSpec.initial plusTwoZeroWords := by
              simp only [ProofsLean.execute, Option.some.injEq] at hrun
              exact hrun.symm
            have hs' : s' = plusTwoSpec.initial (plusTwoOneHotWords j) := by
              simp only [ProofsLean.execute, Option.some.injEq] at hrun'
              exact hrun'.symm
            subst hs
            subst hs'
            rcases hfp with hfp | hfp
            · exact hfp
            · rw [plusTwoInitialState_footprint_eq (.pe expressions)
                (plusTwoOneHotWords j) plusTwoZeroWords] at hfp
              exact hfp
          have agree := plusTwo_sourceRegionsAgree_of_check _
            (by
              have checked := plusTwo_check_of_correct_mem (.pe expressions :: []) correct
                expressions (by simp)
              simpa [InstructionLine.toParsed, checkParsedTopLine] using checked)
          have hcard := plusTwoFootprint_inputs_card_le_eight expressions agree
            (plusTwoSpec.initial plusTwoZeroWords)
          have hsub : (Finset.univ : Finset (Fin 20)) ⊆
              Finset.univ.filter (fun j : Fin 20 => plusTwoInputWord j ∈
                plusTwoLineFootprint (.pe expressions)
                  (plusTwoSpec.initial plusTwoZeroWords)) := by
            intro j _
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hcover j
          have h20 : (Finset.univ : Finset (Fin 20)).card = 20 := by simp
          have hle := Finset.card_le_card hsub
          rw [h20] at hle
          omega


/-- **`LowerBound 2` from the write-determination contract alone.**  The read
count does not need the discharged line class: `plusTwo_lowerBound_two_of_chan`
only uses the per-line channel contract, so any program that is write-determined
at the concrete footprint has at least two lines. -/
theorem plusTwoLowerBound_two_of_determinationChan
    (determination : PlusTwoWriteDeterminationChan) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 2 :=
  fun program correct =>
    plusTwo_lowerBound_two_of_chan program (fun line _ => determination line) correct

/-- **`2 ≤ score` on the discharged line class, unconditionally.** -/
theorem plusTwo_lowerBound_two (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedALULine line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program) :
    2 ≤ ProofsLean.score plusTwoSealedMachine program :=
  plusTwo_lowerBound_two_of_chan program
    (fun line _ => lineDeterminedAtChan_of_aluRows line (discharged line ‹_›)) correct

/-! ## 11. What the count reaches, and the exact residuals beyond it -/

/-- **The residual for `3 ≤ score`.**  Every input word lies in the footprint of
some line computed at the *initial* state.  `plusTwo_exists_prefix_pe_read`
proves the same statement with one of the two prefix states of that line, and
`plusTwoLineFootprint_context_determined` identifies the two footprint sets as
soon as both states carry the same hazard control.

This is the exact statement that the read capacity needs and does not get for
free: the resolved address is
`(bar + regionAddressAt cycle + madpe) / words * words`, so the PE's BAR words
are an input to the footprint.  A `.pe` line whose single destination is `.bar`
(`parsedIntegerALUBarUpdates` stores `write.data 0` into the BAR) writes them
from computed data, so the prefix context — and with it the footprint — can be
input-dependent.  Nothing in the kernel forbids that, and this is why the count
stops at three rather than continuing to four. -/
def PlusTwoInitialFootprintCoverage (program : List InstructionLine) : Prop :=
  ∀ j : Fin 20, ∃ line ∈ program,
    plusTwoInputWord j ∈ plusTwoLineFootprint line (plusTwoSpec.initial plusTwoZeroWords)

/-- **`LowerBound 3` from the coverage residual**, by the read capacity. -/
theorem plusTwoLowerBound_three_of_coverage
    (coverage : ∀ (program : List InstructionLine),
      ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program →
      PlusTwoInitialFootprintCoverage program) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 3 :=
  fun program correct =>
    plusTwo_lowerBound_three_of_initial_coverage program correct (coverage program correct)

/-- **The residual for `LowerBound 4` is on the *write* side, not the read
side.**  `LowerBound 4` needs a line to change at most eight of the twenty
observed words *and* the first line to change at most three of them; the read
capacity contributes nothing to either, because reads do not write.  These are
the two budgets of `ProofsLean/PlusTwoBoundSix.lean`, restated here so that the
boundary between the read count and the write count is explicit. -/
theorem plusTwoLowerBound_four_of_writeBudgets
    (budget : PlusTwoLineWriteBudget) (firstBudget : PlusTwoFirstLineCorrectBudget) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 4 :=
  plusTwoLowerBound_four_of_lineBudgets budget firstBudget

/-- **`LowerBound 5` and `LowerBound 6` are out of reach of the read count.**
The capacity proved here is `8 = 4 cycles × 2 input words` and it is not
improvable from the footprint: a `Region` carries four *independent* cycle
addresses (`Region.address0 … address3`), each resolved to a word-aligned
window, and a `.double` window holds two of the twenty odd input addresses.  So
`20 / 8` lines is the best the read side can say (`3`), while `5` would need
`4` input words per line and `6` would need `3`.

The five-line floor is therefore not a read count.  Its exact missing ingredient
is the *provenance of the observed output values*, of which
`PlusTwoOutputProvenance` below records the write-side shape: what has to be
counted is not how many words a line touches but which output value each written
word carries.  It is what `PlusTwoBoundSix.lean` §6 records as the open end of
the counting argument: at the all-zero input every output is the same value `2`
(`plusTwoZero_computed_slot_no_two` only rules `2` out for the *first* line's
computed slots), so a single computed `2` can be relayed into many output words,
and no count of writes separates the twenty outputs. -/
def PlusTwoOutputProvenance : Prop :=
  ∀ (program : List InstructionLine),
    ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program →
    ∀ k : Fin 20, ∃ (line : InstructionLine) (member : line ∈ program)
      (state next : State),
      plusTwoSealedMachine.step line state = some next ∧
        (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) =
          (plusTwoZeroWords k) + 2

end ProofsLean.MNCore
