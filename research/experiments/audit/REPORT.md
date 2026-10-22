# Independent adversarial audit — Welcome / GenericLowerBound / 1.a-b / 4.mul7

Date: 2026-10-21 (JST), ~01:10.
Repository: `/home/wogikaze/wgkz/mncore`.
HEAD: `a94a26e` ("Record the FizzBuzz investigation, its measuring tools and the proofs rule").
Welcome optimality commit: `5565452c8c432d7ca17d3533723a4b37c0becdb9` (2026-10-20 23:24:19 +0900).

This report edits nothing. No Lean module and no shared note was modified. All evidence below was
produced with `#check`, `#print axioms`, `decide`, explicit `lake build` targets, and comment-stripped
token scans.

Audited file hashes (SHA-256 prefix, taken at 01:04 JST):

| file | sha256 (16) | git status |
|---|---|---|
| `ProofsLean/WelcomeWholeMachineOptimal.lean` | `83833cd0ed7054e9` | tracked (HEAD `5565452`) |
| `ProofsLean/WelcomeOptimalFinal.lean` | `07e830396ba9504e` | tracked (HEAD `5565452`) |
| `ProofsLean/GenericLowerBound.lean` | `cd8d0a8028e86655` | **untracked** |
| `ProofsLean/ABLowerBound.lean` | `e03c082a1dbf8347` | **untracked** |
| `ProofsLean/ABNarrowPlain.lean` | `224ace7c8d1619a1` | **untracked** |
| `ProofsLean/Mul7Spec.lean` | `320bae709aff9e74` | **untracked** |
| `ProofsLean/Mul7LowerBound.lean` | `3e095cc358381f08` | **untracked** |
| `ProofsLean/Mul7FloatGap.lean` | `8181c61ead64ff7a` | **untracked** |
| `ProofsLean/AplusBLowerBound.lean` | `d9b75601459a6fbf` | **untracked**, fails to build |

> **Provenance finding (affects the word "landed").** Only item 1 is committed. Items 2–4 exist only
> in the working tree (`git status --short` lists them as `??`). The committed tree at HEAD does not
> contain them. See §0 for the build consequence.

---

## Verdict summary

| # | claim | verdict |
|---|---|---|
| 1 | `Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer`, exact type | **confirmed** |
| 1 | only standard axioms | **confirmed** (`propext`, `Classical.choice`, `Quot.sound`) |
| 1 | `welcomeWholeMachine` is the total presentation (`.ok↦some`, failure/unknown↦none) | **confirmed** (definitional) |
| 1 | `welcomeWholeSpec.post` is the real Welcome postcondition | **confirmed as the 0..50 / PE-0 spec**; the public problem statement has no 0..50 bound — *scope caveat* |
| 1 | `wholeMachine_not_complete` genuinely proved, `seal` unavailable | **confirmed** (literal witness uses issue-illegal tag 0; the same `.unknown` holds for an issue-legal tag > 0) |
| 2 | re-exported "theorems" are real proofs, not restatements | **confirmed** |
| 2 | `lowerBound_two_iff_residual` never used with an unimplemented `outsideRefuted` to claim a bound | **confirmed** |
| 2 | `hazardProblem_lowerBound_two_of_sealed_of_nil_pending` "really requires its two hypotheses" | **confirmed that both are used**; **overstated** if read as necessary for the conclusion (`tagsIncomplete` necessity not established) |
| 3 | neither A/B module proves `LowerBound 2` | **confirmed** |
| 3 | no prose implies otherwise | **wrong** — the `ABLowerBound.lean` header says "(all unconditional)" for a conditional theorem, and cites three declarations and a section that do not exist |
| 4 | `mul7LowerBound_two_of_peFootprint` is conditional | **confirmed** (`Mul7PELineFootprint → LowerBound … 2`) |
| 4 | `mul7_input_is_subnormal` states what the prose says | **confirmed** (minor wording mismatch: "subnormal" vs `decode = zero`) |
| 5 | no `sorry` / `admit` / `native_decide` / `axiom` in code | **confirmed** (0 real code hits in all of `ProofsLean/*.lean`) |
| 5 | axioms of every "unconditional" theorem in the notes | **confirmed only standard axioms** (full list in §5) |
| — | `cd proofs_lean && lake build ProofsLean` exits 0 | **confirmed** (900 jobs) — **but it does not typecheck items 2–4** |

---

## 0. Build results and build coverage

### 0.1 Required build

```
$ cd proofs_lean && lake build ProofsLean
Build completed successfully (900 jobs).
EXIT=0
```

Warnings only (no errors): unused simp args at `WelcomeWholeMachineOptimal.lean:156,543,807`,
deprecated `if_true`/`if_false`, unused variable `busesCopy` in `WelcomeHalfBlockFloat.lean`.
Re-running it after the audit costs 1.1 s (all cached) and still exits 0.

### 0.2 Coverage gap (important)

`proofs_lean/ProofsLean.lean` (92 imports) does **not** import:

```
GenericLowerBound, ABLowerBound, ABNarrowPlain, Mul7Spec, Mul7LowerBound, Mul7FloatGap,
AplusBLowerBound, ConvertEndianLowerBound, PlainALUDestination, PlusTwoLowerBound,
StageCommitSpecific, StageCommitWalk
```

(`grep -n "GenericLowerBound\|ABLowerBound\|ABNarrowPlain\|Mul7" proofs_lean/ProofsLean.lean` → no hits).
`lake build ProofsLean` therefore builds the root module and its transitive imports only. This is
proved empirically: `AplusBLowerBound.lean` currently **fails** to compile, yet the root build exits 0
in 1.1 s and no `AplusBLowerBound.olean` exists.

Consequence: the "only hard gate" quoted in `research/problems-survey.md` (900 jobs, exit 0) is
**not** a gate for items 2–4. Each module had to be built explicitly:

```
$ lake build ProofsLean.GenericLowerBound      # EXIT 0
$ lake build ProofsLean.ABLowerBound           # EXIT 0
$ lake build ProofsLean.ABNarrowPlain          # EXIT 0
$ lake build ProofsLean.Mul7Spec               # EXIT 0
$ lake build ProofsLean.Mul7LowerBound         # EXIT 0
$ lake build ProofsLean.Mul7FloatGap           # EXIT 0
$ lake build ProofsLean.PlainALUDestination    # EXIT 0
$ lake build ProofsLean.StageCommitSpecific    # EXIT 0
$ lake build ProofsLean.AplusBLowerBound       # EXIT 1  (errors at 375, 424, 456, 443 as of 01:03)
```

`AplusBLowerBound.lean` is outside the five requested items, but it is currently cited as an asset in
the working tree and its header claims "No `sorry`, no `admit`, no `native_decide`, no new axioms"
while the file does not elaborate.  Errors observed at 01:03: `simp` made no progress (line 375),
failed `rewrite` (424), application type mismatch (456), unsolved goals (443); an earlier snapshot also
reported an unknown identifier `aplusb_or_shift_append'` (364).  It has no `.olean`.  Its mtime changed
during the audit (01:01:29), so it is being edited concurrently; re-check before citing.

The three experiment scripts used as evidence by the generic-core README do compile:

```
$ cd proofs_lean
$ lake env lean ../research/experiments/generic-core/instantiate.lean        # EXIT 0
$ lake env lean ../research/experiments/generic-core/instantiate_hazard.lean  # EXIT 0
$ lake env lean ../research/experiments/generic-core/axioms.lean              # EXIT 0
```

---

## 1. `WelcomeWholeMachineOptimal.lean` / `WelcomeOptimalFinal.lean`

### 1.1 Exact type — CONFIRMED

`ProofsLean/WelcomeWholeMachineOptimal.lean:760-769`:

```lean
theorem welcomeWholeMachine_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer
```

`#check` (with `import ProofsLean.WelcomeWholeMachineOptimal`) prints exactly:

```
MNCore.welcomeWholeMachine_optimal : Optimal MNCore.welcomeWholeMachine MNCore.welcomeWholeSpec MNCore.welcomeAnswer
```

No implicit parameters, no hypotheses. `Optimal` is `Correct ∧ LowerBound` (`Optimality.lean:5-10`),
with `Correct := legal p ∧ ∀ input, admissible input → ∃ result, execute … = some result ∧ post …`
(`Semantics.lean:47-50`), so "unconditional" is literally true.

Axioms:

```
#print axioms welcomeWholeMachine_optimal
  → [propext, Classical.choice, Quot.sound]
#print axioms welcomeWholeMachine_correct        → [propext, Classical.choice, Quot.sound]
#print axioms welcomeWholeMachine_lowerBound_two → [propext, Classical.choice, Quot.sound]
#print axioms welcomeWhole_partialOptimal        → [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

The parallel `PartialMachine` statement for `wholeMachine` itself is
`welcomeWhole_partialOptimal : PartialOptimal wholeMachine welcomeWholePartialSpec welcomeAnswer`
(line 929), also closed and standard-axioms. This is the honest fix for the fact that
`Optimal` is typed over `Machine`, not `PartialMachine`.

### 1.2 Total presentation — CONFIRMED (definitional)

`WelcomeWholeMachineOptimal.lean:396-424`:

```lean
noncomputable def welcomeWholeExecute : List InstructionLine → HazardAwareState → Option HazardAwareState
  | [], state => some state
  | line :: rest, state =>
      match wholeMachine.step line state with
      | .ok next => welcomeWholeExecute rest next
      | .failure => none
      | .unknown => none

noncomputable def welcomeWholeMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := HazardAwareState
  Input := ProofsLean.MNCore.PlusOne.Words
  step := fun line state =>
    match wholeMachine.step line state with
    | .ok next => some next
    | .failure => none
    | .unknown => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive
```

The following `example`s elaborate by `rfl` (checked in a scratch file, `open ProofsLean.MNCore`):

```lean
example : ∀ line state, welcomeWholeMachine.step line state =
    (match wholeMachine.step line state with
     | .ok n => some n | .failure => none | .unknown => none) := fun _ _ => rfl

example : ∀ line state, wholeMachine.step line state =
    executeHazardAwareNormalizedLine line.toNormalizedLine state := fun _ _ => rfl

example : wholeMachine.legal = fun _ => True := rfl
```

So it is exactly `PartialMachine.seal`'s step construction without the `Complete` argument, and it is a
total function into `Option`. This matches the docstring at lines 390-394 and 409-414.

### 1.3 `welcomeWholeSpec` postcondition — CONFIRMED for the written spec, with a scope caveat

`WelcomeWholeMachineOptimal.lean:426-436`:

```lean
noncomputable def welcomeWholeSpec : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun input => welcomeSpec.admissible input
  initial := fun input => HazardAwareState.initial (welcomeSpec.initial input)
  post := fun input state => welcomeSpec.post input state.machine
```

and (`WelcomeOptimal.lean:124-131`):

```lean
noncomputable def welcomeSpec : ProofsLean.Problem welcomeSealedMachine where
  admissible := fun input => ∀ i, (input i).toNat ≤ 50
  initial := welcomeInitialState
  post := fun input state => ∀ i : Fin 16,
    (state.peRegisters welcomePE).lm1 ⟨i.val, …⟩ = input i + 1
```

* The **postcondition is the real one**: 16 `BitVec 32` LM1 words of PE 0 (`welcomePE = ⟨0,…⟩`,
  `WelcomeOptimal.lean:51`), each equal to `input i + 1` (wrapping `BitVec` addition).  This matches
  `problems/challenge/1.plus-one/problem.md` ("16 32-bit integers … add 1 … output to LM1 head").
* The three spec fields agree definitionally with `welcomeSpec` (all three `rfl`-checked), so the
  hazard-aware theorem is about the same problem read through `state.machine`.
* **Caveat 1 (domain):** `admissible` is `(input i).toNat ≤ 50`, not "all 32-bit integers".  The public
  problem statement has no such bound.  This restriction is documented in this repo
  (`WelcomeOptimal.lean:124-126`; `research/lean-plan-progress.md:379-381`), but the headline
  "1.plus-one is done" in `research/problems-survey.md:20-24` does not repeat it.
* **Caveat 2 (observed PEs):** the post observes only PE 0.  The public testcase reads only
  `n0c0b0m0p0`, and the project models PE-uniform inputs (`welcomeInitialState` writes the same 16
  words into every PE, `WelcomeOptimal.lean:65-70`), so this is testcase-faithful, but it is a weaker
  postcondition than "every PE".
* Direction of soundness: the Lean spec is *implied by* the official spec on the official domain
  (fewer constraints on outputs, subset of inputs), so a Lean `LowerBound 2` transfers to the official
  problem.  The **correctness** half does not transfer: `welcomeAnswer_correct` is proved only for the
  0..50 / PE-0 spec, so `Optimal` for the unrestricted public problem is not established by these
  files alone.  (The `iinc` answer is almost certainly correct for all 32-bit inputs, but that is not
  the theorem.)

### 1.4 `wholeMachine_not_complete` and `seal` — CONFIRMED, with a nuance about the witness

`WelcomeWholeMachineOptimal.lean:800-819`:

```lean
theorem welcomeWhole_nop_wait_unknown (tag : Fin 256) (input : …Words) :
    wholeMachine.step (.nop ⟨1, by decide⟩ (some tag))
      (HazardAwareState.initial (welcomeInitialState input)) = .unknown

theorem wholeMachine_not_complete : ¬ wholeMachine.Complete :=
  wholeMachine_not_complete_of_unknown (.nop ⟨1, by decide⟩ (some ⟨0, by decide⟩))
    (HazardAwareState.initial (welcomeInitialState (fun _ : Fin 16 => 0)))
    (welcomeWhole_nop_wait_unknown ⟨0, by decide⟩ (fun _ : Fin 16 => 0))
```

`PartialMachine.Complete` is `∀ line state, m.step line state ≠ .unknown`
(`PartialSemantics.lean:22-23`), and `seal` has type `(m : PartialMachine) → m.Complete → Machine`
(`#check @ProofsLean.PartialMachine.seal`).  Since `¬ Complete` is a theorem, no `Complete` argument
can be produced without inconsistency, so `seal` is indeed unavailable.  Axioms are standard.

Nuance about the witness.  The literal witness uses **tag 0**, and
`checkParsedTopLine (.nop 1 (some ⟨0⟩)) = false` (verified by `decide`), i.e. that particular line is
rejected by the issue checker; the wrapper checks the wait tag *before* the core's issue check
(`WholeMachineStep.lean:7877-7886`), so it returns `.unknown` rather than the `.failure` it would get
later.  This does not weaken the theorem: `welcomeWhole_nop_wait_unknown` is quantified over **every**
tag (`∀ tag : Fin 256`), and for a positive tag the same nop is issue-**legal**
(`ParsedLine.checked_nop_wait_positive`, `Issue.lean:2381-2391`; `checkParsedTopLine (.nop 1 (some ⟨1⟩))
= true` verified by `decide`), yet the completion still fails (empty pending queue) and the step is
`.unknown`.  So an issue-legal witness exists; `wholeMachine_not_complete` and the unavailability of
`seal` are robust.

---

## 2. `GenericLowerBound.lean`

### 2.1 Re-exports are real proofs — CONFIRMED

I inspected §2 (`:355-655`, the `.lm1` write-shape algebra) and §4 (`:959-1027`, certificates).

* Every re-export is an application of an existing theorem, e.g.
  `lm1FreeWrites_append := ProofsLean.MNCore.lm1FreePreparedWrites_append headFree tailFree`
  (`:391-395`), `lm1WritesShape_of_six_first := ProofsLean.MNCore.lm1WritesShape_of_six_first …`
  (`:519-525`).  None is a hypothesis or a `structure` field masquerading as a theorem.
* The only definitional restatements are genuine characterisations:
  `lm1FreeWrites_iff := Iff.rfl` (`:382-386`) and `hazardMachine_step_eq := rfl` (`:708-719`).
* New generic mathematics is proved, not assumed: `score_eq_zero_iff` (`:137`), `score_lt_two_iff`
  (`:153`), `lowerBound_two_iff_rejects_unit_lines` (`:186`), `lowerBound_two_of_residual` (`:220`),
  `lowerBound_two_iff_residual` (`:244`), `hazardExecute_project` (`:721`),
  `hazardInitialNoWait_of_pendingMv_nil` (`:777`), `hazardLine_correct_sealed` (`:852`),
  `hazardProblem_lowerBound_two_of_sealed` (`:919`).
* `#print axioms` on the key ones gives only `[propext, Classical.choice, Quot.sound]`
  (`lowerBound_two_iff_residual`, `hazardProblem_lowerBound_two_of_sealed_of_nil_pending`, …).

The header claim "every theorem below is either a re-export … or a short generic corollary" (`:10-18`)
is accurate in spirit; several are genuine new inductions, but none hides its conclusion as a
hypothesis.

### 2.2 `lowerBound_two_iff_residual` and `outsideRefuted` — CONFIRMED clean

The theorem (`:244-259`) is an **iff** whose statement carries

```lean
(outsideRefuted : ∀ line : m.Line, m.lineCost line = 1 →
  (∀ i, line ≠ lineOf i) → ¬ Correct m spec [line])
```

so it cannot yield a bound unless `outsideRefuted` is proved.  Search over the whole repo:

* Only use outside the module itself: `research/experiments/generic-core/instantiate.lean:35`
  (the `1.a-b` instantiation).  That file **compiles (exit 0)**, and the `?_` goal is discharged by a
  real case split:

  ```lean
  refine lowerBound_two_iff_residual abSealedMachine abSpec
    (fun expressions => InstructionLine.pe expressions) (fun _ => rfl) abEmpty_not_correct ?_
  intro line short outside
  cases line with
  | pe expressions => exact absurd rfl (outside expressions)
  | nop count wait => … abNop_not_correct …
  | mv transfer    => exact abMv_not_correct transfer
  ```

  Note also that this example concludes the **iff**, not `LowerBound abSealedMachine abSpec 2`.
* No other Lean or markdown file applies it as if it produced a bound.  The generic-core README
  (`:66-89`) describes `outsideRefuted` as the intended syntactic case split; it does not claim the
  split has been done generically.

Verdict: no unimplemented `outsideRefuted` is used to claim a bound anywhere in the tree.

### 2.3 `hazardProblem_lowerBound_two_of_sealed_of_nil_pending` — both hypotheses are used; necessity for the conclusion is overstated

The exact type (`:943-953`):

```lean
theorem hazardProblem_lowerBound_two_of_sealed_of_nil_pending {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (sealedLower : LowerBound (sealedMachine Input) sealedSpec 2)
    (sealedEmpty : ¬ Correct (sealedMachine Input) sealedSpec [])
    (pendingNil : ∀ input, (sealedSpec.initial input).pendingMv = [])
    (tagsIncomplete : ∀ input tag, (sealedSpec.initial input).mvCompletedTags tag = false) :
    LowerBound (hazardMachine Input) (hazardProblem Input sealedSpec) 2
```

There are **four** hypotheses: two problem inputs (`sealedLower`, `sealedEmpty`) and the two side
conditions the task calls "its two hypotheses".  The proof routes both side conditions through
`hazardInitialNoWait_of_pendingMv_nil` (`:777-799`), which calls
`completePendingMvTagFuel_none_of_pendingMv_nil` (`WelcomeWholeMachineOptimal.lean:504-513`):

* `pendingNil` — if a pending transfer carried the tag, `completePendingMvTag` would drain it and
  commit its writes into `blockMemory` (`WholeMachineStep.lean:7337-7345`), i.e. the wait branch would
  change `state.machine` before the core step.  The sealed machine does not model this.  This
  hypothesis is semantically load-bearing.
* `tagsIncomplete` — used to make the fuel loop return `none`.  Its necessity for the *conclusion* is
  not established.  I proved in the audit that a completed tag makes completion a no-op:

  ```lean
  example (state : State) (tag : Fin 256) (h : state.mvCompletedTags tag = true) :
      completePendingMvTag state tag = some state := by simp [completePendingMvTag, h]
  example … : completePendingMvTagAll state tag = some state := by
      simp [completePendingMvTagAll, completePendingMvTagFuel, h]
  ```

  (definitions at `WholeMachineStep.lean:7337-7358`).  The wait branch then proceeds to the core step
  on the *same* `machine`, whose `.machine` projection is exactly the sealed step
  (`executeHazardAwareNormalizedLineCore_ok_project`, `GenericLowerBound.lean:665-671`).  Moreover,
  `HazardInitialNoWait` **is** false without `tagsIncomplete`: I proved in the audit, using
  `executeHazardAwareNormalizedLine_completed_wait_nop` (`WholeMachineStep.lean:8274`) with tag `1`
  (issue-legal: `checkParsedTopLine (.nop 1 (some ⟨1⟩)) = true` by `decide`), that

  ```lean
  example : ¬ HazardInitialNoWait (fun _ : Unit => st)
  -- st = the Welcome initial state with `mvCompletedTags := fun _ => true`
  ```

  compiles.  So `tagsIncomplete` is genuinely required for the `HazardInitialNoWait` route; what is
  not established is that it is required for the **lower bound itself**, since the successful
  completed-tag wait step has the same `.machine` payload as the sealed step.

Verdict: "really requires its two hypotheses" is **true of the proof route** and both are satisfiable
for Welcome (`fun _ => rfl`, `instantiate_hazard.lean`).  But the stronger reading — "the theorem fails
without `tagsIncomplete`" — is **not proved**; on the evidence above the hypothesis looks removable
from the conclusion (it is load-bearing only for the `HazardInitialNoWait` intermediate).  Say "used
by the proof" rather than "required".

For Welcome the lift is redundant anyway: `welcomeWholeMachine_lowerBound_two` is proved directly
(`WelcomeWholeMachineOptimal.lean:732-755`), not through this generic theorem.  The generic theorem
reproduces it in one line (`instantiate_hazard.lean`), which is a genuine cross-check.

---

## 3. `ABLowerBound.lean` / `ABNarrowPlain.lean` — no `LowerBound 2`

### 3.1 No bound is proved — CONFIRMED

`#check`:

```
abLowerBound_two_of_residual :
  (∀ expressions, AbPEUnrefuted expressions →
     ¬ Correct abSealedMachine abSpec [InstructionLine.pe expressions]) →
  LowerBound abSealedMachine abSpec 2

abShortLine_not_correct :
  ∀ line, line.cost < 2 →
    (∀ expressions, AbPEUnrefuted expressions →
       ¬ Correct abSealedMachine abSpec [InstructionLine.pe expressions]) →
    ¬ Correct abSealedMachine abSpec [line]

abLowerBound_two_iff_residual :
  LowerBound abSealedMachine abSpec 2 ↔
    ∀ expressions, AbPEUnrefuted expressions → ¬ Correct abSealedMachine abSpec [pe expressions]

abPE_singleWelcomeLine_not_correct_of_narrow : ∀ base,
  ¬ Correct abSealedMachine abSpec [InstructionLine.pe [welcomeExpr base]]
```

There is no closed declaration of type `LowerBound abSealedMachine abSpec 2`:
`abLowerBound_two_of_residual` takes the residual refutation, `abShortLine_not_correct` takes it too,
and `abLowerBound_two_iff_residual` is an equivalence.  `ABNarrowPlain.lean` proves only the narrow
one-line refutation (`abNarrowAtOnes_welcomeExpr`, `:35`; `abPE_singleWelcomeLine_not_correct_of_narrow`,
`:70`), not a bound.  Verdict: **confirmed**.

The A/B header is also commendably explicit about the specification weakening (only PE 0 observed,
PE-uniform inputs) and about the bit-exact postcondition being stronger than the official `1e-4`
tolerance, so `LowerBound abSealedMachine abSpec 2` does not formally imply the official tolerance
bound (`:30-45`).  That part is accurate.

### 3.2 "No text or docstring implies otherwise" — WRONG

Three concrete prose defects:

1. **`ABLowerBound.lean:49`** says `## Results proved here (all unconditional)`, but the bullet at
   `:61-63` describes `abShortLine_not_correct` as "every line of cost below two outside the residual
   class" — the theorem at `:637-651` has the explicit hypothesis
   `(residual : ∀ expressions, AbPEUnrefuted expressions → ¬ Correct …)`.  It is **conditional**.
   (The other bullets in that list are unconditional; only this one and the derived residual theorems
   are not.)
2. **`ABLowerBound.lean:75-77` and `:736`** cite facts that do not exist:
   `ABNarrowTransfer`, `AbDoubleOrIndependent`, `abLowerBound_two_of_transfer`, and "section 12".
   `grep` over the file finds only these mentions; there is no section 12 and no such declarations.
   The header says "The last section states the two obligations that close it … and proves
   `abLowerBound_two_of_transfer`; neither is proved here."  That is a stale description of a section
   that is absent.  It could mislead a reader into thinking a transfer theorem exists that closes
   `LowerBound abSealedMachine abSpec 2`.
3. The bullet at `:61-62` says "hence `abLowerBound_two_of_residual` and the exact equivalence
   `abLowerBound_two_iff_residual`" without repeating that both are conditional.  The later "The
   remainder" paragraph does say the residual is not proved, so this is a presentation weakness rather
   than a false statement.

---

## 4. `Mul7Spec.lean` / `Mul7LowerBound.lean` / `Mul7FloatGap.lean`

### 4.1 `mul7LowerBound_two_of_peFootprint` is conditional — CONFIRMED

`Mul7LowerBound.lean:231-249`; `#check` prints:

```
mul7LowerBound_two_of_peFootprint : Mul7PELineFootprint → LowerBound mul7SealedMachine mul7Spec 2
```

`Mul7PELineFootprint` (`:210-212`) is `∀ expressions, Mul7OneLineLm1Footprint (.pe expressions)`, and
`Mul7OneLineLm1Footprint` (`:97-106`) is the per-line "changes LM1 on at most 8 of 16 lanes" footprint.
It is **not** proved in the module.  `mul7ShortLine_not_correct` (`:220-228`) is conditional on the
same footprint.  The header's bullet `mul7LowerBound_two_of_peFootprint — LowerBound … from
Mul7PELineFootprint` is honest.

Prose defects in the same header:

* **`:29`** names `mul7_oneLine_not_correct`, which does not exist.  The actual theorem is
  `mul7_oneLine_not_correct_of_footprint` (`:131`).  Also, the sentence says the "counting half
  (`mul7_exists_unwritten_lane`, `mul7_oneLine_not_correct`) is proved unconditionally"; the real
  `mul7_oneLine_not_correct_of_footprint` takes the footprint hypothesis (though
  `mul7_exists_unwritten_lane` is unconditional).  This is a **wrong name** plus a conditional
  presented as unconditional.
* **`:44-45`** bullet: "`mul7ShortLine_not_correct` — the exact shape of the residual: every single
  line of cost `< 2` that is incorrect."  The theorem takes `footprint : Mul7PELineFootprint`; the
  bullet omits it.  The phrase "that is incorrect" is also circular.
* **`Mul7Spec.lean:12`**: "on `1024` output words: `16 MAB x 4 PE x 16 ULong` per PE."  `1024` is the
  total over the 64 observed PEs, not per PE (per PE it is 16 ULong).  The trailing "per PE" makes
  the arithmetic 65,536.  Minor but wrong wording.
* **`Mul7FloatGap.lean:14-18`**: "the correctness of the published answer cannot be *stated* against
  `SingleFMA.singleFma`, no matter how the executor is inverted."  The formal content is only
  `mul7_float_multiply_is_zero` (`:58`): for `m < 2^23`, `singleFma (ofNat 32 m) seven 0 = 0`, plus
  `7 * 5 = 35 ≠ 0`.  "No matter how the executor is inverted" is an informal extrapolation, not a
  theorem.

### 4.2 `mul7_input_is_subnormal` vs the prose — CONFIRMED (wording nit)

The theorem (`Mul7FloatGap.lean:42-55`):

```
mul7_input_is_subnormal : ∀ m < 2 ^ 23,
  SingleFMA.decode (BitVec.ofNat 32 m) = SingleFMA.Value.zero false
```

The "Results" bullet (`:22`) says "every admissible input word decodes to zero" — exactly the
theorem, since `admissible` is `toNat ≤ 1000 < 2^23` (`Mul7Spec.lean:206-213`).  The body text
(`:15-17`) says "every admissible input word … is an exponent-zero (subnormal) pattern".  That is a
paraphrase, not the statement: the theorem is about `decode`, and the zero pattern (m = 0) is
exponent-zero but is not a subnormal number.  The substantive claim (FTZ model maps every admissible
input to zero) is correct.

Also note the theorem is stated for `m : Nat < 2^23`, not for the `Fin 16 → Fin 4 → Fin 16 →
BitVec 32` input structure; the connection to admissible inputs is by the definition of `admissible`
and is not itself a theorem.  That is a small gap between the name ("input is subnormal") and the
type (a bit-pattern decode fact).

---

## 5. Escape-hatch scan and axioms of the "unconditional" theorems

### 5.1 Scan of all `ProofsLean/*.lean` — CONFIRMED clean

I stripped nested block comments (`/- … -/`, including `/-!` docstrings), line comments, and string
literals, then searched for whole-word `sorry`, `admit`, `native_decide`, declaration-initial
`axiom`, `constant`, `opaque`, `unsafe`, `extern`, and `implemented_by`.

Result: **0 real occurrences** of `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe`,
`implemented_by`, `extern`.  The only 3 remaining `constant` hits are the identifier `constant` used
as a tactic argument (`WelcomeMixedStructure.lean:411`, `WelcomePlainReadPackages.lean:129`,
`WelcomeShapes.lean:204`), not declarations.  Every `sorry`/`admit`/`native_decide` in the tree is
inside a docstring sentence "No `sorry`, no `admit`, no `native_decide`…" (117 such lines).

### 5.2 Axioms of every theorem described as "unconditional"

The notes `research/lean-plan-progress.md` and `research/problems-survey.md` were searched for
`無条件` / `仮定なし` / `unconditional`.  `problems-survey.md` has **no theorem-level
"unconditional" claim** (its only hit is a filename, `WelcomeMatrixMAUUnconditional.lean`).  All
theorem-level claims are in `lean-plan-progress.md`; the table below covers every name in those
claims.  `#print axioms` was run on each (a name that is only a `def`/`Prop`, such as
`WelcomePEStageLm1Frame`, was resolved to its proving theorem).

**Group S — `[propext, Classical.choice, Quot.sound]`** (the standard three; no extra axioms):

| note line | theorems |
|---|---|
| 543 | `welcome_not_correct_of_word_ne_one`, `welcome_not_correct_of_doubleCopyShape`, `welcome_not_correct_of_narrowShape`, `exists_uncovered_of_windows`, `prepareParsedIntegerALUExprCycle_alu_direct_double_copy_of_fixed` |
| 614 | `welcomeSealed_pe_prepared`, `welcomeIntegerPrep_inv`, `welcomeIntegerPrep_single_plain_eq`, `prepareParsedIntegerALUExprCycles_four`, `constantTargets_lm1_count_le` |
| 664 | `writeCycles_four`, `writeCycles_cons`, `writeCycles_nil` |
| 755 | `executeParsedSharedBlockProducers_lm1_frame` |
| 838 | `welcomePE_line_stage_commit_unconditional` |
| 880 | `welcomePEStageLm1Frame` (theorem at `WelcomeLm1FrameResidual.lean:719`), `executeIntegerProducerInstructionLine_pe_lm1_frame` |
| 947 | `executeParsedFloatMAUsAtPE_zeroNarrow_static`, `writeParsedMAUDestinations?_widthCount`, `executeParsedFloatMAUCyclesAtPE_widthCount` |
| 976 | `executeParsedFloatMAUsAtPE_zeroShape_static_unconditional` |
| 1041 | `executeParsedMatrixMAUProducer_zeroNarrow_static`, `executeParsedMatrixMAUProducer_widthCount` |
| 1087 | `welcomePEWriteShape_singleton_of_floatMAU` |
| 1130 | `WelcomePEMatrixMAUProducer_zeroShape_static`, `WelcomePEMatrixMAUAndWrites_zeroShape_static` |
| 1131 | `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions_unconditional` |
| 1319–1321 | `welcomePEMslMsrWriterShapeObligation`, `welcomePEFloatReluWriterShapeObligation`, `welcomePEBlockFloatLowPrecisionWriterShapeObligation` |
| 1386 | `welcomePELm1PhantomWriterProvenance`, `welcomePESpecialALUWriterShapeObligation`, `welcomePEMatrixMAUWriterData`, `welcomePEWriteShape_of_matrixMAUWriter` |
| 1446–1448 | `welcomePEFloatMAUWriterData_intRows`, `welcomePEWriteShape_of_floatMAUWriter` |
| 1497–1523 (round 51; described as "パッケージ不要" = no package hypothesis) | `welcomePEWriteShape_of_plainWriter_closed`, `welcomePEWriteShape_of_matrixReadWriter_closed`, `welcomePEWriteShape_of_l1bmWriter_dataMultiDest` |
| 1484/1520 | `welcomePEL1BMWriterDataMultiDest_holds` |
| 1510 | `welcomePEPlainWriterDataDoubleFree` |
| 1524 | `welcomeLowerBound_two`, `welcomeAnswer_optimal` |
| 1561/1568 | `welcomeWholeMachine_optimal`, `welcomeWhole_partialOptimal`, `welcomeWholeMachine_lowerBound_two`, `welcomePELm1WriteShapeObligation` |
| audit | `welcomePEUnrefuted_inhabited` (non-vacuity witness for `WelcomePEUnrefuted`) |

**Group T — `[propext, Quot.sound]`** (strictly fewer):

| note line | theorems |
|---|---|
| 543 | `commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy`, `welcomeLm1Writer_unique` |
| 614 | `plain_legal_length_le_one`, `updateParsedIntegerALUForwardingCycle_frame`, `lm1Destinations_unique_positions`, `mapM_lm1_count_le` |
| 664 | `l1ToPEBusAt_welcomeInitialState`, `l1ToPE_data_word_two_isWelcomeCopy`, `parsedOutputAfterFlush_l1ToPEBusAt_zero`, `l1ToPEWrites_doubleCopy`, `l1ToPEWrites_narrow` |

No theorem in either group depends on `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.
This is the decisive check for "no `sorry`/`native_decide`": an actual `sorry` would print
`sorryAx`, and an actual `native_decide` would print `Lean.ofReduceBool`/`Lean.trustCompiler`.

Two note-side corrections: `writeCycles` (line 664) is not a top-level declaration (it is the
`executeParsedL1ToPEAtPEs.writeCycles` namespace/field; use `writeCycles_four/_cons/_nil`), and
`WelcomePEStageLm1Frame` is a `def : Prop` (`WelcomeAssembly.lean:910`) whose proof is the theorem
`welcomePEStageLm1Frame`, so `#print axioms` applies to the theorem, not the def.

---

## 6. Prose-versus-type disagreements (consolidated)

| location | prose | actual type / fact | verdict |
|---|---|---|---|
| `ABLowerBound.lean:49` | "Results proved here (**all unconditional**)" | `abShortLine_not_correct` (`:637`) takes `residual : ∀ expressions, AbPEUnrefuted … → ¬ Correct …` | **overstated** |
| `ABLowerBound.lean:61-63` | "`abShortLine_not_correct` — every line of cost below two outside the residual class" | conditional on the residual refutation | **overstated** (bullet omits hypothesis) |
| `ABLowerBound.lean:75-77, :736` | cites `ABNarrowTransfer`, `AbDoubleOrIndependent`, `abLowerBound_two_of_transfer`, "section 12" | none of these declarations/sections exist in the file | **wrong** (stale docstring) |
| `Mul7LowerBound.lean:29` | "(`mul7_exists_unwritten_lane`, `mul7_oneLine_not_correct`) is proved unconditionally" | no `mul7_oneLine_not_correct`; the theorem is `mul7_oneLine_not_correct_of_footprint` (`:131`) and is conditional on the footprint | **wrong name + overstated** |
| `Mul7LowerBound.lean:44-45` | "`mul7ShortLine_not_correct` — … every single line of cost `< 2`" | `Mul7PELineFootprint → ∀ line, cost < 2 → ¬ Correct …` (`:220`) | **overstated** (omits footprint) |
| `Mul7Spec.lean:12` | "`1024` output words: `16 MAB x 4 PE x 16 ULong` **per PE**" | 1024 is the total across 64 PEs; per PE it is 16 ULong | **wrong wording** |
| `Mul7FloatGap.lean:15-17` | "every admissible input word … is an exponent-zero (subnormal) pattern" | `∀ m < 2^23, decode (ofNat 32 m) = zero false` (`:42`) | **paraphrase** (zero ≠ subnormal; decode, not a predicate) |
| `Mul7FloatGap.lean:16-18` | correctness "cannot be stated … no matter how the executor is inverted" | only `singleFma X 7.0 0 = 0` and `7*5 = 35 ≠ 0` are proved | **not formalised** |
| `GenericLowerBound.lean:943-953` | "once the initial state has no pending MV transfers and incomplete tags" | both are explicit hypotheses (plus `sealedLower`, `sealedEmpty`); both are used | **confirmed**; "required for the conclusion" is **overstated** (see §2.3) |
| `GenericLowerBound.lean:919-923` | "the exact shape of `welcomeWholeMachine_lowerBound_two`: only an empty-program refutation and the initial no-wait analysis are problem-specific" | `welcomeWholeMachine_lowerBound_two` is proved directly and also needs `welcomeLowerBound_two`; the generic theorem is a different proof route | **slightly overstated** (shape claim, not type claim) |
| `WelcomeOptimalFinal.lean:45-48` | "the per-line write-shape obligation, the lower bound and the optimality claim carry no hypotheses" | `#check welcomePELm1WriteShapeObligation`, `welcomeLowerBound_two`, `welcomeAnswer_optimal` — all closed | **confirmed** |
| `WelcomeWholeMachineOptimal.lean:44-47` | "`welcomeWholeMachine` — the total presentation of `wholeMachine`" | definitional (see §1.2) | **confirmed** |
| `problems-survey.md:20-24` | "`1.plus-one` is the baseline and is **done**" | `Optimal` is proved for `welcomeSpec` whose `admissible` is `toNat ≤ 50` and whose post observes only PE 0; the public problem statement has no 0..50 bound | **overstated** for the public problem |
| `lean-plan-progress.md:664` | lists `writeCycles` among unconditional facts | no such top-level declaration | **minor** |
| `lean-plan-progress.md:859,880` | "`WelcomePEStageLm1Frame` … unconditional" | it is a `def : Prop`; the theorem is `welcomePEStageLm1Frame` (`WelcomeLm1FrameResidual.lean:719`) | **minor** |
| `WelcomeOptimal.lean:38-39` | "the unrestricted statement `LowerBound … 2` is still open" | stale after `WelcomeOptimalFinal.lean`; the file is tracked and not edited, so the docstring is now false | **stale** (not a claim of a result) |

---

## 7. Corrections to the research notes

These are proposed text corrections only; no note was edited.

### `research/lean-plan-progress.md`

1. **Round 52 / lines 1524–1580 ("Phase 4 の数学的内容が完成").**  Add the scope in the same
   paragraph: the theorem is about `welcomeSpec`, i.e. inputs `toNat ≤ 50`, PE-uniform LM0, and
   PE 0 observed.  The public `problems/challenge/1.plus-one/problem.md` states "16 32-bit integers"
   with no 0..50 bound.  The lower bound transfers to the official problem (the Lean spec is weaker
   on outputs and narrower on inputs), but the correctness half `welcomeAnswer_correct` does not
   transfer to inputs outside 0..50 / other PEs.  Therefore "`Optimal` for the public plus-one
   problem" is not established by this chain; "`Optimal` for the project's documented 0..50 / PE-0
   spec" is.
2. **Round 52 / line 1563.**  The `#print axioms` line is correct as far as it goes; extend it to
   `welcomeWhole_partialOptimal`, `welcomePELm1WriteShapeObligation` and `welcomeWholeMachine_correct`
   (all `[propext, Classical.choice, Quot.sound]`), and note that the whole chain was checked with
   the token scan of §5.
3. **Round 51/52 build lines ("900 jobs 成功", "897", "898", "899").**  Add: `lake build ProofsLean`
   does **not** compile `GenericLowerBound`, `ABLowerBound`, `ABNarrowPlain`, `Mul7*`,
   `AplusBLowerBound`, etc., because `ProofsLean.lean` does not import them.  Any claim that "the
   tree builds" must distinguish root-target jobs from per-module builds.  As of this audit the six
   audited modules build individually; `AplusBLowerBound` does not.
4. **Line 664 list.**  Replace `writeCycles` with `writeCycles_four`, `writeCycles_cons`,
   `writeCycles_nil`; `writeCycles` is a namespace/field, not a theorem.
5. **Line 859/880.**  Say "`WelcomePEStageLm1Frame` (a `Prop`) is proved by
   `welcomePEStageLm1Frame`", not that the `def` itself is unconditional.
6. **Any "landed" wording for rounds 50–52.**  `GenericLowerBound.lean`, `ABLowerBound.lean`,
   `ABNarrowPlain.lean`, `Mul7Spec.lean`, `Mul7LowerBound.lean`, `Mul7FloatGap.lean` are **untracked**.
   They are working-tree results, not commits.  Commit them (and add them to `ProofsLean.lean` if they
   are meant to be part of the library gate) before describing them as landed.
7. **Add a warning about `AplusBLowerBound.lean`.**  It does not compile at
   `d9b75601459a6fbf` (errors at 375, 424, 456, 443), is outside the root target, and its header's
   "no sorry / no axioms" claim is moot until it elaborates.  Do not list it as an asset.

### `research/problems-survey.md`

1. **§0 and §2.2 row 1 ("`1.plus-one` … **Done** on the hazard-aware machine").**  Change "Done" to
   "Done for the project's 0..50 / PE-0 `welcomeSpec` (the public problem statement has no 0..50
   bound)".  Also note that `audit.json` still reports the problem `unproven`, which is consistent
   with the narrower claim.
2. **§0 build gate ("the only hard gate measured here is `lake build ProofsLean` … 900 jobs, exit
   0").**  This gate is not sufficient for the new modules (see §0.2 above).  Either add
   `lake build ProofsLean.GenericLowerBound ProofsLean.ABLowerBound ProofsLean.ABNarrowPlain
   ProofsLean.Mul7LowerBound ProofsLean.Mul7FloatGap` as an additional gate, or import the modules
   from `ProofsLean.lean`.
3. **§1.4 / table row 4 (`4.mul7`).**  The row correctly says "one-line LB is reduced to
   `Mul7PELineFootprint`".  Add that `mul7ShortLine_not_correct` is conditional on the same footprint
   and that the header currently omits it; and that `Mul7Spec.lean:12` overstates the word count
   ("per PE").

### Suggested note text for the headline

> `Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer` is proved
> (`WelcomeWholeMachineOptimal.lean:760`), where `welcomeWholeSpec` is the project's documented
> 0..50, PE-0, PE-uniform-input Welcome specification (`WelcomeOptimal.lean:124-131`;
> `lean-plan-progress.md:379-381`).  The postcondition is the real `+1` relation; the admissible
> domain is narrower than the public problem statement's "16 32-bit integers".  The lower-bound
> half transfers to the public problem; the correctness half is only proved on 0..50.

---

## 8. Reproducibility

All scratch Lean files were created outside the repository (in a per-command temporary directory);
nothing under `proofs_lean/` or `research/` was modified except this report.

Key commands and results:

```bash
# required build
cd proofs_lean && lake build ProofsLean
# → Build completed successfully (900 jobs).  exit 0

# coverage-aware builds
lake build ProofsLean.GenericLowerBound      # 0
lake build ProofsLean.ABLowerBound           # 0
lake build ProofsLean.ABNarrowPlain          # 0
lake build ProofsLean.Mul7Spec               # 0
lake build ProofsLean.Mul7LowerBound         # 0
lake build ProofsLean.Mul7FloatGap           # 0
lake build ProofsLean.AplusBLowerBound       # 1 (errors 375, 424, 456, 443)

# experiment scripts cited by generic-core/README.md
cd proofs_lean
lake env lean ../research/experiments/generic-core/instantiate.lean         # 0
lake env lean ../research/experiments/generic-core/instantiate_hazard.lean   # 0
lake env lean ../research/experiments/generic-core/axioms.lean               # 0
```

Scratch checks that produced the quotes above (run via `lake env lean` with `import ProofsLean`,
`import ProofsLean.ABLowerBound`, `import ProofsLean.Mul7LowerBound`, or
`import ProofsLean.GenericLowerBound` as appropriate):

```lean
#check @ProofsLean.MNCore.welcomeWholeMachine_optimal
#print axioms ProofsLean.MNCore.welcomeWholeMachine_optimal
#print axioms ProofsLean.MNCore.welcomeLowerBound_two
#print axioms ProofsLean.MNCore.welcomeAnswer_optimal
#print axioms ProofsLean.MNCore.welcomePELm1WriteShapeObligation
#print axioms ProofsLean.MNCore.wholeMachine_not_complete
#print axioms ProofsLean.MNCore.Mul7Float.mul7_input_is_subnormal
#check @ProofsLean.MNCore.mul7LowerBound_two_of_peFootprint
#check @ProofsLean.MNCore.abLowerBound_two_of_residual
#check @ProofsLean.MNCore.abShortLine_not_correct
#check @ProofsLean.MNCore.Generic.hazardProblem_lowerBound_two_of_sealed_of_nil_pending

-- definitional checks
example : ∀ line state, welcomeWholeMachine.step line state =
    (match wholeMachine.step line state with
     | .ok n => some n | .failure => none | .unknown => none) := fun _ _ => rfl

-- witness line (tag 0) is issue-rejected; the same theorem holds for issue-legal tag 1
example : checkParsedTopLine (Issue.InstructionLine.toParsed
    (.nop ⟨1, by decide⟩ (some (⟨0, by decide⟩ : Fin 256)))) = false := by decide
example : checkParsedTopLine (.nop (0+1) (some (⟨1, by decide⟩ : Fin 256))) = true := by decide

-- completed tag makes MV completion a no-op ...
example (state : State) (tag : Fin 256) (h : state.mvCompletedTags tag = true) :
    completePendingMvTagAll state tag = some state := by
  simp [completePendingMvTagAll, completePendingMvTagFuel, h]

-- ... and a completed positive tag makes HazardInitialNoWait false
def st : HazardAwareState :=
  { HazardAwareState.initial (welcomeInitialState (fun _ : Fin 16 => 0)) with
    machine := { (HazardAwareState.initial (welcomeInitialState (fun _ : Fin 16 => 0))).machine with
      mvCompletedTags := fun _ => true } }
example : ¬ HazardInitialNoWait (fun _ : Unit => st) := by
  intro h
  have ok := executeHazardAwareNormalizedLine_completed_wait_nop st 0
    (⟨1, by decide⟩ : Fin 256) (by rfl) (by decide) (by rfl)
  exact h () (Issue.InstructionLine.nop ⟨1, by decide⟩ (some ⟨1, by decide⟩))
    ⟨1, by decide⟩ rfl _ ok
```

---

## 9. Bottom line

* **Item 1 is sound and the headline theorem is exactly what it claims**, modulo the scope of
  `welcomeSpec` (0..50, PE 0, PE-uniform inputs).  If the claim is meant to be the public plus-one
  problem, the correctness half is not proved for the full input domain; the lower-bound half does
  transfer.
* **Items 2–4 are mathematically sound but not "landed"**: they are untracked and outside the root
  build.  They build individually, and their key theorems carry only the standard axioms.
* **The only hard prose errors** are in the `ABLowerBound.lean` header (a conditional listed as
  unconditional; three non-existent declarations and a non-existent section 12) and in the
  `Mul7LowerBound.lean` header (a non-existent theorem name; the conditional `mul7ShortLine_not_correct`
  presented without its footprint hypothesis).  These are documentation defects, not proof holes.
* **`hazardProblem_lowerBound_two_of_sealed_of_nil_pending`** is fine as an interface; both side
  conditions are used, but only `pendingNil` is clearly semantically necessary.  Do not describe
  `tagsIncomplete` as required for the conclusion without a counterexample.
* **AplusBLowerBound.lean is broken** and should not be cited until it builds; the 900-job root gate
  hides it.
