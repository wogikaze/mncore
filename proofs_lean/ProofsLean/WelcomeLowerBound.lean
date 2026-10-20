import ProofsLean.WelcomeOptimal

/-! # Lower bounds for the sealed Welcome machine

`WelcomeOptimal.lean` proves `welcomeAnswer_correct` but does not prove any
lower bound. This module adds the one-line lower-bound material that is
independent of the answer's expression list:

* `welcomeEmpty_not_correct` — the empty program is incorrect.
* `welcomeWelcomeLine_not_correct` — a one-line program consisting of one
  `IsWelcomeLine` line is incorrect, for both accepted Welcome bases.
* `welcomeWelcomeLine_anyBase_not_correct` — the same for `welcomeExpr base`
  at **every** base, not only the accepted `0` and `8`.
* `welcomeAtMostOneWelcome_not_correct` — no program of at most one
  `IsWelcomeLine` line is correct.
* `welcomeLowerBound_one` and `welcomeBoundOneCertificate` — the (weak)
  `LowerBound welcomeSealedMachine welcomeSpec 1`.
* `welcomeBoundTwoCertificate_rejects_every_short_line` — **any**
  `SymbolicBoundCertificate` at bound `2` must reject *every* line of cost
  below `2`, not only the Welcome lines.
* `welcomeOnlyClass_does_not_cover` — the Welcome-only family cannot be the
  certificate's `contains` at bound `2`.
* `welcomeLowerBound_two_iff_rejects_short_lines` — `LowerBound ... 2` is
  *equivalent* to the unrestricted one-line statement, so the missing piece
  is exactly that statement.

Nothing in this file asserts `Optimal welcomeSealedMachine welcomeSpec
welcomeAnswer`. With `welcomeSealedMachine.legal = fun _ => True` the
`covers` field of a certificate quantifies over **all** programs of score
below the bound (including `.nop`, `.mv` and arbitrary `.pe` lines), so the
Welcome-only class cannot be used as `contains`; see
`welcomeBoundTwoCertificate_rejects_every_short_line` and
`welcomeLowerBound_two_iff_rejects_short_lines`.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## Preserving an LM1 long-word read across the four committed writes -/

/-- Committing `.long` LM1 writes at `cycles` preserves a `.long` LM1 read
whose word window avoids every written word window. -/
theorem welcomeWrites_preserves_read_of_outside
    (base : Nat) (files writeFiles : IntegerRegisterFiles)
    (cycles : List (Fin 4)) (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (outside : ∀ c ∈ cycles,
      count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress base c)
        (advance .lm1 read index.val)) :
    readDirectAccess (commitParsedMaskedWrites files
      (cycles.map (welcomePreparedWrite writeFiles base)))
      ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  induction cycles generalizing files with
  | nil => rfl
  | cons cycle rest ih =>
      rw [List.map_cons]
      rw [show commitParsedMaskedWrites files
          (welcomePreparedWrite writeFiles base cycle ::
            rest.map (welcomePreparedWrite writeFiles base)) =
        commitParsedMaskedWrites
          (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base cycle])
          (rest.map (welcomePreparedWrite writeFiles base)) from rfl]
      rw [ih (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base cycle])
        (by
          intro c member
          exact outside c (List.mem_cons_of_mem _ member))]
      unfold welcomePreparedWrite welcomeDestinationAccess
      rw [commitParsedMaskedWrites_singleton_lm1Long]
      exact readDirectAccess_lm1Long_after_write_outside files
        (welcomeDestinationAddress base cycle) read _ _ index
        (outside cycle (by simp))

/-- The four committed `.long` LM1 writes at `base` preserve a `.long` LM1
read whose window avoids all four written windows. -/
theorem welcomeBaseWrites_preserves_read
    (base : Nat) (files : IntegerRegisterFiles)
    (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (outside : ∀ c : Fin 4,
      count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress base c)
        (advance .lm1 read index.val)) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
       welcomePreparedWrite files base 2, welcomePreparedWrite files base 3])
      ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  simpa using welcomeWrites_preserves_read_of_outside base files files [0, 1, 2, 3] read index
    (by
      intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      exacts [outside 0, outside 1, outside 2, outside 3])

/-- A high LM1 word (`8..15`) lies outside the four `.long` windows written
by the base-0 Welcome line (words `0..7`). -/
theorem welcomeBase0Distance (read : Fin Bank.lm1.capacity) (cycle : Fin 4)
    (index : Fin 4) (indexBound : index.val < 2)
    (high : 8 ≤ read.val) (upper : read.val + index.val < 16) :
    count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress 0 cycle)
      (advance .lm1 read index.val) := by
  have htarget : (advance .lm1 read index.val).val = read.val + index.val := by
    simp [advance, Bank.capacity]
    have := read.isLt
    have := index.isLt
    omega
  rw [show (advance .lm1 read index.val) =
      ⟨read.val + index.val,
        by have := read.isLt; have := index.isLt; change read.val + index.val < 4096; omega⟩
    from Fin.ext htarget]
  have hstart := welcomeDestinationAddress_val 0 (Or.inl rfl) cycle
  simp only [count, Width.words, distance, Bank.capacity, hstart]
  have hx : read.val + index.val + 4096 - (0 + 2 * cycle.val) =
      4096 + (read.val + index.val - 2 * cycle.val) := by
    have := cycle.isLt
    omega
  rw [hx, Nat.add_mod_left, Nat.mod_eq_of_lt]
  · change 2 ≤ read.val + index.val - 2 * cycle.val
    have := cycle.isLt
    omega
  · have := cycle.isLt
    omega

/-- Committing the base-0 Welcome writes preserves a `.long` LM1 read of a
high word (`8..15`). -/
theorem welcomeBase0Writes_preserves_read_high
    (files writeFiles : IntegerRegisterFiles)
    (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (indexBound : index.val < 2) (high : 8 ≤ read.val)
    (upper : read.val + index.val < 16) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles 0 0, welcomePreparedWrite writeFiles 0 1,
       welcomePreparedWrite writeFiles 0 2, welcomePreparedWrite writeFiles 0 3])
      ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  simpa using welcomeWrites_preserves_read_of_outside 0 files writeFiles [0, 1, 2, 3]
    read index
    (by
      intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      exacts [welcomeBase0Distance read 0 index indexBound high upper,
        welcomeBase0Distance read 1 index indexBound high upper,
        welcomeBase0Distance read 2 index indexBound high upper,
        welcomeBase0Distance read 3 index indexBound high upper])

/-- Committing the base-8 Welcome writes preserves a low LM1 read, restated
through the four-element literal write list. -/
theorem welcomeBase8Writes_preserves_read_low
    (files writeFiles : IntegerRegisterFiles)
    (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (_indexBound : index.val < 2) (low : read.val + index.val < 8) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles 8 0, welcomePreparedWrite writeFiles 8 1,
       welcomePreparedWrite writeFiles 8 2, welcomePreparedWrite writeFiles 8 3])
      ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  simpa using welcomeWrites_preserves_read_of_outside 8 files writeFiles [0, 1, 2, 3]
    read index
    (by
      intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      exacts [welcomeBase8Distance read 0 index low,
        welcomeBase8Distance read 1 index low,
        welcomeBase8Distance read 2 index low,
        welcomeBase8Distance read 3 index low])


/-! ## Arbitrary-base widening of the one-line refutation

The same argument applies to `iinc $lm<base>v $ln<base>v` for **every** base:
the four `.long` writes cover the eight consecutive LM1 words starting at
`2 * (base / 2) % 4096`, so some LM1 word in `0..15` is untouched. -/

/-- The address of the spec word `word` inside its `.long` window, advanced by
its in-window index, is the word itself. -/
theorem welcomeWordAdvance_val (word : Fin 16) :
    (advance .lm1 (welcomeWordLongAddress word) (welcomeWordIndex word)).val =
      word.val := by
  simp [advance, welcomeWordLongAddress, welcomeWordLongStart, welcomeWordIndex,
    Bank.capacity]
  have := word.isLt
  omega

/-- Word arithmetic: if `w` is a word outside the eight consecutive addresses
starting at `s`, then it is outside every two-word write window
`(s + 2c, s + 2c + 1)`. -/
theorem welcomeWindowDistance (s w c : Nat) (hs : s < 4096) (hc : c < 4)
    (h1 : s < 8 → w = 15) (h2 : 8 ≤ s → s ≤ 4088 → w = 0)
    (h3 : 4088 < s → w = 15) :
    2 ≤ (w + 4096 - (s + 2 * c) % 4096) % 4096 := by
  by_cases hlow : s < 8
  · have hw := h1 hlow
    subst w
    have hd : s + 2 * c < 4096 := by omega
    rw [Nat.mod_eq_of_lt hd]
    have hx : 4096 ≤ 15 + 4096 - (s + 2 * c) := by omega
    rw [Nat.mod_eq_sub_mod hx]
    rw [show 15 + 4096 - (s + 2 * c) - 4096 = 15 - (s + 2 * c) by omega]
    rw [Nat.mod_eq_of_lt (by omega : 15 - (s + 2 * c) < 4096)]
    omega
  · by_cases hmid : s ≤ 4088
    · have hw := h2 (by omega) hmid
      subst w
      have hd : s + 2 * c < 4096 := by omega
      rw [Nat.mod_eq_of_lt hd]
      rw [Nat.mod_eq_of_lt (by omega : 0 + 4096 - (s + 2 * c) < 4096)]
      omega
    · have hs' : 4088 < s := by omega
      have hw := h3 hs'
      subst w
      by_cases hd : s + 2 * c < 4096
      · rw [Nat.mod_eq_of_lt hd]
        rw [Nat.mod_eq_of_lt (by omega : 15 + 4096 - (s + 2 * c) < 4096)]
        omega
      · have hge : 4096 ≤ s + 2 * c := by omega
        have hle : s + 2 * c ≤ 4101 := by omega
        have hdval : (s + 2 * c) % 4096 = s + 2 * c - 4096 := by
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
        rw [hdval]
        have hx : 15 + 4096 - (s + 2 * c - 4096) =
            4096 + (15 - (s + 2 * c - 4096)) := by omega
        rw [hx, Nat.add_mod_left]
        rw [Nat.mod_eq_of_lt (by omega : 15 - (s + 2 * c - 4096) < 4096)]
        omega

/-- **Arbitrary base.** Some spec word is untouched by the four `.long` LM1
writes of the Welcome line at any base. -/
theorem welcomeAnyBaseWord (base : Nat) :
    ∃ word : Fin 16, ∀ c : Fin 4,
      count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress base c)
        (advance .lm1 (welcomeWordLongAddress word) (welcomeWordIndex word)) := by
  set A := base / 2 * 2 with hA
  set s := A % 4096 with hs
  have hslt : s < 4096 := by
    rw [hs]
    exact Nat.mod_lt _ (by decide)
  have hstep : ∀ (w : Fin 16) (c : Fin 4),
      distance .lm1 (welcomeDestinationAddress base c)
        (advance .lm1 (welcomeWordLongAddress w) (welcomeWordIndex w)) =
      (w.val + 4096 - (s + 2 * c.val) % 4096) % 4096 := by
    intro w c
    have hdiv : (base + 2 * c.val) / 2 = base / 2 + c.val := by omega
    have hmul : (base / 2 + c.val) * 2 = A + 2 * c.val := by
      rw [hA]
      omega
    have hwritten : (welcomeDestinationAddress base c).val = (s + 2 * c.val) % 4096 := by
      simp only [welcomeDestinationAddress, welcomeRawAddress]
      rw [hdiv, hmul]
      rw [← Nat.mod_add_mod A 4096 (2 * c.val), ← hs]
    rw [show distance .lm1 (welcomeDestinationAddress base c)
        (advance .lm1 (welcomeWordLongAddress w) (welcomeWordIndex w)) =
        ((advance .lm1 (welcomeWordLongAddress w) (welcomeWordIndex w)).val + 4096 -
          (welcomeDestinationAddress base c).val) % 4096 from rfl]
    rw [welcomeWordAdvance_val, hwritten]
  by_cases hlow : s < 8
  · refine ⟨⟨15, by decide⟩, ?_⟩
    intro c
    rw [hstep]
    change 2 ≤ (15 + 4096 - (s + 2 * c.val) % 4096) % 4096
    exact welcomeWindowDistance s 15 c.val hslt c.isLt (fun _ => rfl)
      (fun hge _ => False.elim (by omega)) (fun _ => rfl)
  · by_cases hmid : s ≤ 4088
    · refine ⟨⟨0, by decide⟩, ?_⟩
      intro c
      rw [hstep]
      change 2 ≤ (0 + 4096 - (s + 2 * c.val) % 4096) % 4096
      exact welcomeWindowDistance s 0 c.val hslt c.isLt
        (fun hlt => False.elim (by omega)) (fun _ _ => rfl)
        (fun hgt => False.elim (by omega))
    · refine ⟨⟨15, by decide⟩, ?_⟩
      intro c
      rw [hstep]
      change 2 ≤ (15 + 4096 - (s + 2 * c.val) % 4096) % 4096
      exact welcomeWindowDistance s 15 c.val hslt c.isLt (fun _ => rfl)
        (fun _ hle => False.elim (by omega)) (fun _ => rfl)

/-! ## The empty program -/

/-- The empty program is incorrect: its output is the initial state, whose
LM1 word 15 is zero, while the specification demands `input 15 + 1`. -/
theorem welcomeEmpty_not_correct :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      ([] : ProofsLean.Program welcomeSealedMachine) := by
  intro correct
  let input : ProofsLean.MNCore.PlusOne.Words := fun _ => 0
  have admissible : welcomeSpec.admissible input := by
    intro i
    simp [input]
  obtain ⟨result, executed, post⟩ := correct.2 input admissible
  have executed' : execute welcomeSealedMachine [] (welcomeInitialState input) =
      some result := by
    simpa [welcomeSpec] using executed
  have stateEq : welcomeInitialState input = result := by
    have h : (some (welcomeInitialState input) : Option welcomeSealedMachine.State) =
        some result := by
      simpa [ProofsLean.execute] using executed'
    exact Option.some.inj h
  subst result
  have wanted := post ⟨15, by decide⟩
  simp [input, welcomeInitialState, welcomeInitialPERegisters,
    zeroInitialPERegisterFiles] at wanted

/-! ## One Welcome line -/

/-- A one-line program of one Welcome line at `base` is incorrect when the
line leaves some spec word untouched and that word starts at zero. `read` and
`index` address that word inside its `.long` window; `preserved` is the frame
fact for the four committed writes. -/
theorem welcomeWelcomeLine_not_correct_of_preserved
    (base : Nat) (word : Fin 16) (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (readEq : read = welcomeWordLongAddress word) (indexEq : index = welcomeWordIndex word)
    (preserved : ∀ (files : IntegerRegisterFiles),
      readDirectAccess (commitParsedMaskedWrites files
        [welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
         welcomePreparedWrite files base 2, welcomePreparedWrite files base 3])
        ⟨.lm1, .long, read⟩ index =
      readDirectAccess files ⟨.lm1, .long, read⟩ index) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      [InstructionLine.pe [welcomeExpr base]] := by
  intro correct
  let input : ProofsLean.MNCore.PlusOne.Words := fun _ => 0
  have admissible : welcomeSpec.admissible input := by
    intro i
    simp [input]
  obtain ⟨result, executed, post⟩ := correct.2 input admissible
  obtain ⟨next, stepEq, _lineExecuted, _invariant, value⟩ :=
    welcomeSealed_step base (welcomeInitialState input) (welcomeInitialState_invariant input)
  have executed' : execute welcomeSealedMachine [InstructionLine.pe [welcomeExpr base]]
      (welcomeInitialState input) = some result := by
    simpa [welcomeSpec] using executed
  have stepResult : welcomeSealedMachine.step (InstructionLine.pe [welcomeExpr base])
      (welcomeInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed'
  rw [stepEq] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  subst readEq
  subst indexEq
  have readZero : readDirectAccess (next.peRegisters welcomePE)
      ⟨.lm1, .long, welcomeWordLongAddress word⟩ (welcomeWordIndex word) = 0 := by
    rw [value welcomePE]
    rw [preserved ((welcomeInitialState input).peRegisters welcomePE)]
    rw [readDirectAccess_welcomeWord]
    simp [welcomeInitialState, welcomeInitialPERegisters, zeroInitialPERegisterFiles]
  have wordZero : (next.peRegisters welcomePE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ = 0 := by
    rw [← readDirectAccess_welcomeWord (next.peRegisters welcomePE) word]
    exact readZero
  have wanted := post word
  rw [wordZero] at wanted
  simp [input] at wanted

/-- The one-line program `iinc $lm0v $ln0v` is incorrect (word 15 is not
written and starts at zero). -/
theorem welcomeWelcomeLine_zero_not_correct :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      [InstructionLine.pe [welcomeExpr 0]] := by
  apply welcomeWelcomeLine_not_correct_of_preserved 0 ⟨15, by decide⟩
    (welcomeWordLongAddress ⟨15, by decide⟩) (welcomeWordIndex ⟨15, by decide⟩) rfl rfl
  intro files
  exact welcomeBaseWrites_preserves_read 0 files (welcomeWordLongAddress ⟨15, by decide⟩)
    (welcomeWordIndex ⟨15, by decide⟩)
    (by
      intro c
      exact welcomeBase0Distance (welcomeWordLongAddress ⟨15, by decide⟩) c
        (welcomeWordIndex ⟨15, by decide⟩) (welcomeWordIndex_lt_two _)
        (by decide)
        (by decide))

/-- The one-line program `iinc $lm8v $ln8v` is incorrect (word 0 is not
written and starts at zero). -/
theorem welcomeWelcomeLine_eight_not_correct :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      [InstructionLine.pe [welcomeExpr 8]] := by
  apply welcomeWelcomeLine_not_correct_of_preserved 8 ⟨0, by decide⟩
    (welcomeWordLongAddress ⟨0, by decide⟩) (welcomeWordIndex ⟨0, by decide⟩) rfl rfl
  intro files
  exact welcomeBaseWrites_preserves_read 8 files (welcomeWordLongAddress ⟨0, by decide⟩)
    (welcomeWordIndex ⟨0, by decide⟩)
    (by
      intro c
      exact welcomeBase8Distance (welcomeWordLongAddress ⟨0, by decide⟩) c
        (welcomeWordIndex ⟨0, by decide⟩)
        (by decide))

/-- **Widening.** A one-line program whose line is `iinc $lm<base>v $ln<base>v`
is incorrect for **every** base, not only `0` and `8`. -/
theorem welcomeWelcomeLine_anyBase_not_correct (base : Nat) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      [InstructionLine.pe [welcomeExpr base]] := by
  obtain ⟨word, outside⟩ := welcomeAnyBaseWord base
  exact welcomeWelcomeLine_not_correct_of_preserved base word
    (welcomeWordLongAddress word) (welcomeWordIndex word) rfl rfl
    (fun files => welcomeBaseWrites_preserves_read base files
      (welcomeWordLongAddress word) (welcomeWordIndex word) outside)

/-- No one-line program consisting of an `IsWelcomeLine` line is correct. -/
theorem welcomeWelcomeLine_not_correct (line : InstructionLine)
    (welcome : IsWelcomeLine line) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec [line] := by
  rcases welcome with rfl | rfl
  · exact welcomeWelcomeLine_zero_not_correct
  · exact welcomeWelcomeLine_eight_not_correct

/-- No program of at most one `IsWelcomeLine` line is correct. -/
theorem welcomeAtMostOneWelcome_not_correct
    (p : ProofsLean.Program welcomeSealedMachine)
    (shape : p = [] ∨ ∃ line : InstructionLine, IsWelcomeLine line ∧ p = [line]) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec p := by
  rcases shape with rfl | ⟨line, welcome, rfl⟩
  · exact welcomeEmpty_not_correct
  · exact welcomeWelcomeLine_not_correct line welcome

/-! ## A genuine (weak) lower bound and the certificate obstruction -/

/-- The empty program is the only program of score below one, so the sealed
machine has lower bound one. This does **not** give optimality of the
two-line answer. -/
theorem welcomeLowerBound_one :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 1 := by
  intro p correct
  cases p with
  | nil => exact False.elim (welcomeEmpty_not_correct correct)
  | cons line rest =>
      have positive := welcomeSealedMachine.positiveCost line
      simp only [ProofsLean.score]
      omega

/-- **Certificate obstruction.** Any `SymbolicBoundCertificate` at bound `2`
would have to reject *every* one-line program: `legal` is `True` and every
line has score `1 < 2`, so `covers` forces `contains [line]`. In particular
the class of Welcome lines is not enough; `contains` cannot be restricted to
`p = [] ∨ ∃ line, IsWelcomeLine line ∧ p = [line]`. -/
theorem welcomeBoundTwoCertificate_rejects_every_short_line
    (certificate : ProofsLean.SymbolicBoundCertificate welcomeSealedMachine
      welcomeSpec 2) :
    ∀ line : InstructionLine, InstructionLine.cost line < 2 →
      ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec [line] := by
  intro line short
  have legal : welcomeSealedMachine.legal [line] := trivial
  have scoreShort : ProofsLean.score welcomeSealedMachine [line] < 2 := by
    simpa [ProofsLean.score, welcomeSealedMachine] using short
  exact certificate.rejected [line]
    (certificate.covers [line] legal scoreShort)

/-- The Welcome-only family cannot satisfy `covers` at bound `2`: the one-line
`.nop 1` program has score `1` and is legal, but is not a Welcome line. -/
theorem welcomeOnlyClass_does_not_cover :
    ¬ ∀ p : ProofsLean.Program welcomeSealedMachine,
        welcomeSealedMachine.legal p → ProofsLean.score welcomeSealedMachine p < 2 →
        (p = [] ∨ ∃ line : InstructionLine, IsWelcomeLine line ∧ p = [line]) := by
  intro covers
  have member := covers [InstructionLine.nop ⟨1, by decide⟩ none] trivial (by
    decide)
  rcases member with empty | ⟨line, welcome, single⟩
  · simp at empty
  · have lineEq : line = InstructionLine.nop ⟨1, by decide⟩ none := by
      exact List.eq_of_mem_singleton
        (single.symm ▸ List.mem_singleton.mpr rfl)
    subst line
    rcases welcome with bad | bad <;> cases bad


/-- A program of score zero is empty. -/
theorem welcomeScore_eq_zero (p : ProofsLean.Program welcomeSealedMachine) :
    ProofsLean.score welcomeSealedMachine p = 0 ↔ p = [] := by
  constructor
  · cases p with
    | nil => intro _; rfl
    | cons line rest =>
        intro h
        have positive := welcomeSealedMachine.positiveCost line
        simp only [ProofsLean.score] at h
        omega
  · intro h
    rw [h]
    rfl

/-- The bound-one certificate: only the empty program has score below one,
and the empty program is incorrect. -/
noncomputable def welcomeBoundOneCertificate :
    ProofsLean.SymbolicBoundCertificate welcomeSealedMachine welcomeSpec 1 where
  contains := fun p => p = []
  covers := by
    intro p _ short
    exact (welcomeScore_eq_zero p).mp (by omega)
  rejected := by
    intro p empty
    rw [empty]
    exact welcomeEmpty_not_correct

/-- **Exact remaining gap.** `LowerBound welcomeSealedMachine welcomeSpec 2`
is equivalent to the unrestricted one-line statement. The Welcome-only
theorems of this file do not discharge it. -/
theorem welcomeLowerBound_two_iff_rejects_short_lines :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 ↔
      (∀ line : InstructionLine, InstructionLine.cost line < 2 →
        ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec [line]) := by
  constructor
  · intro lower line short correct
    have bound := lower [line] correct
    have scoreLine : ProofsLean.score welcomeSealedMachine [line] =
        InstructionLine.cost line := rfl
    rw [scoreLine] at bound
    omega
  · intro rejects p correct
    by_contra hle
    have short : ProofsLean.score welcomeSealedMachine p < 2 := by omega
    cases p with
    | nil => exact welcomeEmpty_not_correct correct
    | cons line rest =>
        have positive : 0 < InstructionLine.cost line :=
          welcomeSealedMachine.positiveCost line
        have scoreEq : ProofsLean.score welcomeSealedMachine (line :: rest) =
            InstructionLine.cost line + ProofsLean.score welcomeSealedMachine rest := rfl
        have restZero : ProofsLean.score welcomeSealedMachine rest = 0 := by
          rw [scoreEq] at short
          omega
        have restEmpty : rest = [] := (welcomeScore_eq_zero rest).mp restZero
        subst rest
        have costShort : InstructionLine.cost line < 2 := by
          rw [scoreEq] at short
          simp only [ProofsLean.score] at short
          omega
        exact rejects line costShort correct

end ProofsLean.MNCore
