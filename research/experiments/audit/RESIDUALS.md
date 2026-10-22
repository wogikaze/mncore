# Residuals audit — satisfiability, not just provability

Date: 2026-10-21 (JST).
Repository: `/home/wogikaze/wgkz/mncore`, Lean project `proofs_lean` (Lean `v4.35.0`).
Auditor: independent read-only pass. **No Lean file was edited.** Scratch files used for
machine checks live under `/tmp/wgkz_audit/` and are not part of the tree.

The audit targets the failure mode already seen three times in this project: a named
`Prop` is introduced as a “residual”, conditional theorems are proved from it, and it
later turns out to be **false**, so the conditional theorems were vacuous. The question
for every residual below is therefore not “can it be proved?” but “is it *true* / is it
*inhabited*?”, and, if not, which theorems become vacuous.

### Build and provenance

The audited modules build with the current toolchain:

```text
cd proofs_lean
lake build ProofsLean.PlusTwoCompose ProofsLean.ABUnconditional \
  ProofsLean.CendUnconditional ProofsLean.ProgramWitness \
  ProofsLean.FamilyDestinationCongruence ProofsLean.ChannelResiduals \
  ProofsLean.FootprintCoverage ProofsLean.AplusBLowerBound \
  ProofsLean.WelcomeOptimalFinal ProofsLean.WelcomeWholeMachineOptimal
# exit 0 (cached)
```

`ProofsLean/ChannelResiduals.lean` builds now, contrary to the stale comment in
`ProgramWitness.lean:910` (“currently does not build”). `AplusBLowerBound.lean` also
builds now. Several audited modules are **untracked** in git (`ABUnconditional`,
`CendUnconditional`, `ChannelResiduals`, `FootprintCoverage`, `PlusTwoCompose`, …);
“in the tree” below means the working tree, not `HEAD`.

Status legend:

* **Proved** — there is a theorem in the tree concluding the residual (or the negation
  of a failure condition), or a machine-checked proof in the audit scratch.
* **Refuted (named)** — there is a theorem in the tree whose conclusion is `¬ P`.
* **Refuted (in substance)** — the tree contains a machine-checked concrete
  counterexample/computation refuting `P`, but not the lifted theorem `¬ P`.
* **Open** — no proof and no refutation found in the tree.

---

## 0. Verdict summary

| Residual / hypothesis | Definition | Used at | Status | What happens to the theorem using it |
|---|---|---|---|---|
| `PlusTwoInitialFootprintCoverage` | `PlusTwoCompose.lean:1261` | `plusTwoLowerBound_three_of_coverage`, `1266–1272` | **Open in tree; false in substance (semantic counterexample below)** | Conditional; should be treated as vacuous once the 11-line counterexample’s `Correct` lift is formalized. |
| `PlusTwoOutputProvenance` | `PlusTwoCompose.lean:1302` | **unused** | **Proved unconditionally in audit scratch** (standard axioms only) | Not a residual at all; if used, it is live. |
| `PlusTwoWriteDeterminationChan` | `ChannelResiduals.lean:2339` | `plusTwoLowerBound_two_of_determinationChan`, `PlusTwoCompose.lean:1231` | **Open generally; proved on `DischargedALULine`** by `plusTwoWriteDeterminationChan_of_aluRows` (`ALUReadSetBound.lean:1179–1183`) | Conditional form live; `plusTwo_lowerBound_two` (`PlusTwoCompose.lean:1238–1243`) is unconditional on that class. |
| `PlusTwoLineCoverage` | `PlusTwoLowerBound.lean:547` | `plusTwo_execute_coverage` (`:567`), `plusTwoLowerBound_five_of_coverage` (`:604`) | **Refuted in substance** by the wide `.zero` line (`PlusTwoSuffix.lean:249–320`); the tree itself says it is false (`PlusTwoBoundSix.lean:478`) | **Vacuous**: `plusTwoLowerBound_five_of_coverage` assumes a false statement. |
| `PlusTwoLineWriteBudget` | `PlusTwoBoundSix.lean:362` | `plusTwo_execute_notTwo` (`:383`), `plusTwoLowerBound_four_of_lineBudgets` (`:420`), `PlusTwoCompose.lean:1280` | **Open, not refuted** | Conditional/live. |
| `PlusTwoFirstLineCorrectBudget` | `PlusTwoBoundSix.lean:372` | same | **Open, not refuted** | Conditional/live. |
| `PlusTwoLineFootprintCoversPreparedReads` (old) | `ChannelResiduals.lean:1436` | `plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged`, `:2298`; many `:1449–2374` | **Refuted in substance** by the `.zero` read-modify-write obstruction (`FootprintCoverage.lean:7–18`, `:52–70`, `zeroRow_readSet_nonempty` `:565`) | **Vacuous** for the old `DischargedLine` theorems; repaired form is proved. |
| `PlusTwoALULineFootprintCoversPreparedReads` (repaired) | `ALUReadSetBound.lean:1105` | `:1120–1122` | **Proved** | Live. |
| `ABPlainDoubleResidual` | `ABUnconditional.lean:585` | `abLowerBound_two_of_residuals` (`:607`), `abLowerBound_two_iff_residuals` (`:650`) | **Open, not refuted** | Conditional; not vacuous from anything in the tree. |
| `ABNonPlainResidual` | `ABUnconditional.lean:597` | same; `abNonPlainResidual_of_matrixReadFamily` (`FamilyDestinationCongruence.lean:761`) | **Open, not refuted**; `.matrixRead` narrow branch only **partially** closes it | Conditional; not vacuous. |
| `ABRightWindowData` | `ABUnconditional.lean:533` | `abLowerBound_two_of_rightWindowData` (`:637`), `abPE_not_correct_of_rightWindowData` (`:542`) | **Open, not refuted** | Conditional; not vacuous. |
| `CendPENonClosedRefuted` | `CendUnconditional.lean:1010` | `cendPELinesRefuted_of_nonClosed` (`:1017`), `cendLowerBound_two_of_nonClosed` (`:1037`) | **Open, not refuted**; class is coarser than the prose (includes rejected lines) | Conditional; not vacuous. |
| `CendPENonConstantRefuted` | `ProgramWitness.lean:831` | `cendPENonClosedRefuted_of_nonConstant` (`:838`), `cendLowerBound_two_of_nonConstant` (`:846`) | **Open, not refuted**; equivalent to the non-closed residual because constant lines are refuted (`:809`) | Conditional; not vacuous. |
| `CendValueResidual` | `CendUnconditional.lean:1045` | `cendLowerBound_two_of_residual` (`:1055`), `cendLowerBound_two_iff_residual` (`:1065`) | **Open, not refuted**; minimal “unrefuted, non-closed, non-constant” form | Conditional; not vacuous. |
| `CendLineWitnessObligation` / `CendWitnessValueResidual` | `ProgramWitness.lean:855` / `:877` | `:865` / `:884` | **Open, not refuted** | Conditional; not vacuous. |
| `CendTwoLinesRefuted` | `ConvertEndianLowerBound.lean:463` | `cendLowerBound_three_of_residuals` (`:470`) | **Open, not refuted** | Conditional; not vacuous. |
| `Mul7PELineFootprint` | `Mul7LowerBound.lean:210` | `mul7PELine_not_correct` (`:214`), `mul7LowerBound_two_of_peFootprint` (`:231`) | **Open, not refuted** | Conditional; not vacuous. |
| `AplusBPEUnrefuted` residual class | `AplusBLowerBound.lean:948–1046` | `aplusbLowerBound_two_of_residual` (`:1036`) | **Open, not refuted** | Conditional; no unconditional `LowerBound` in the tree. |
| `WelcomePELm1WriteShapeObligation` | `WelcomeValueBound.lean:688` | `welcomeLowerBound_two_of_lm1WriteShapes` (`:694`) | **Proved** by `welcomePELm1WriteShapeObligation` (`WelcomeOptimalFinal.lean:141`) | Discharged; final `welcomeLowerBound_two` (`:159`) is unconditional. |
| `WelcomePEWriterKindDataResiduals` / `...Three` | `WelcomeAssemblyFinal.lean:322` / `WelcomeWriterPackages.lean:1123` | `welcomeLowerBound_two_of_writerKindDataResiduals` (`:379`), `..._of_plainReadL1` (`WelcomeWriterPackages.lean:1162`) | **Refuted (named)**: `welcomePEWriterKindDataResiduals_false` (`:1147`), `...Three_false` (`:1154`); components `WelcomePEL1BMWriterData` / `...NoSingleton` are themselves false (`:885`, `:1032`) | **Vacuous** conditional Welcome lower bounds. |
| `WelcomePEMixedPlainInertFlagAgreement` | `WelcomeMixedStructure.lean:597` | `WelcomeMixedStructure.lean:753`, `:839`, `:870` | **Refuted (named)**: `welcomePEMixedPlainInertFlagAgreement_false` (`WelcomeFlagAgreement.lean:331`) | Conditional intermediate theorems are vacuous; final Welcome theorem bypasses this. |
| `PlusTwoSuffixPreservesWitness` | `PlusTwoLowerBound.lean:503` | `plusTwoRecorded_not_correct_of_suffixFrame` (`:512`) | **False in substance** (`PlusTwoSuffix.lean:27–30`, per-PE false `:327`); no named `¬` theorem | Conditional recorded-answer theorem vacuous; the corrected `plusTwoRecorded_not_correct` (`PlusTwoSuffixFrame.lean:787`) is unconditional. |

The headline result of this audit: **`PlusTwoInitialFootprintCoverage` is not a harmless
open residual.** The BAR caveat in its own docstring (`PlusTwoCompose.lean:72–78`) is
real, and there is a concrete 11-line `DischargedALULine` program whose initial footprint
misses every input word while its observed-PE execution computes `input + 2`. This is
spelled out in §1.1. The only reason it is not already a machine-checked refutation is
that the full 4096-PE `Correct` lift was not formalized in the tree (and this audit was
not allowed to add Lean files). The theorem `plusTwoLowerBound_three_of_coverage` is
therefore conditional on a statement that is **false in the model**.

---

## 1. Plus-two residuals

### 1.1 `PlusTwoInitialFootprintCoverage` — false in substance

Definition (`ProofsLean/PlusTwoCompose.lean:1261–1263`):

```lean
def PlusTwoInitialFootprintCoverage (program : List InstructionLine) : Prop :=
  ∀ j : Fin 20, ∃ line ∈ program,
    plusTwoInputWord j ∈ plusTwoLineFootprint line
      (plusTwoSpec.initial plusTwoZeroWords)
```

Used by (`:1266–1272`):

```lean
theorem plusTwoLowerBound_three_of_coverage
    (coverage : ∀ (program : List InstructionLine),
      ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program →
      PlusTwoInitialFootprintCoverage program) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 3 :=
  fun program correct =>
    plusTwo_lowerBound_three_of_initial_coverage program correct
      (coverage program correct)
```

The docstring itself explains the issue (`:72–78`): the resolved PE address is
`(bar0 + regionAddressAt cycle + madpe) / words * words`, and
`parsedIntegerALUBarUpdates` can store computed data into `bar0`/`bar1` when a `.pe`
row’s sole destination is `.bar`. The BAR context is therefore state/input dependent,
and the prefix-state footprint used by `plusTwo_exists_prefix_pe_read` need not equal
the initial-state footprint.

The relevant implementation facts:

* `parsedIntegerALUBarUpdates` (`ParsedIntegerStep.lean:5216–5223`) special-cases
  `expression.destinations = [.bar lm1 _ _]` and, when the write-selection flags are
  nonzero, emits `(lm1, write.data 0 mod 2^12)`.
* `executeIntegerProducerLineAtPECore` folds those updates into `bar0`/`bar1`
  (`WholeMachineStep.lean:7160–7228`, especially `:7202–7228`), and
  `executeIntegerProducerLineAtPE` allows a BAR-writing row only when the line has
  exactly one expression (`:7232–7237`). A single `.alu` expression with a sole
  `.bar` destination is therefore fully supported.
* `plusTwoLineFootprint` consults exactly `parsedPEHazardControl`, i.e. BAR/T/mask/clock
  (`InputDependence.lean:917–927`), and `plusTwoLineFootprint_context_determined`
  (`PlusTwoCompose.lean:798–810`) says two states with the same context have the same
  footprint. Different BARs therefore give different footprints.

The docstring only says “the context is not frozen in general”. It does not say the
residual is false, and the tree contains no theorem refuting it. The audit finds that
the caveat is enough to build a counterexample **inside `DischargedALULine`**, not just
outside the class:

* `DischargedALULine` (`ALUReadSetBound.lean:1154–1166`) allows any `.pe` row whose op
  is `.alu name p f g` and whose sources/destinations are all
  `directMemoryAddressModeValid`. `.fixed` sources and `.bar` destinations both satisfy
  `directMemoryAddressModeValid` (`ParsedIntegerStep.lean:141–149`, `_ => true`).
* A line

  ```lean
  { op := .alu .lnot (some .i) false none
    sources := [.fixed .l1bid]
    destinations := [.bar false 1 none]
    flush := none, text := "" }
  ```

  is in `DischargedALULine`. At PE 0, `.fixed .l1bid` is `0` and logical-not yields
  `1`, so its sole BAR write sets `bar0 = 1` (evaluated in audit scratch; see below).
  It has no LM0 source, so its initial footprint is empty.
* The input words `plusTwoInputWord j` are the **odd** LM0 addresses `1,3,...,39`
  (`InputDependence.lean:726–730`, `PlusTwoCompose.lean:125–136`). A `.word` source at
  an **even** LM0 address reads an even word when `bar0 = 0`, so a read line whose region
  addresses are even misses every input word at the initial state.
* After the BAR line, `bar0 = 1`, and the same even addresses resolve to
  `2j+1`, i.e. input `j`.

A concrete 11-line program in `DischargedALULine`:

```lean
-- not added to the tree; names are local to this audit
def barOneLine : InstructionLine := .pe [barOneExpr.normalize]

-- LM0 source (even addresses), LM1 destination (odd addresses), .inc
def readLine (s : Nat) : InstructionLine := .pe [(readExpr s).normalize]

-- LM1 source and destination (odd addresses), .inc
def readLm1Line (s : Nat) : InstructionLine := .pe [(readLm1Expr s).normalize]

def prog : List InstructionLine :=
  [barOneLine,
   readLine 0, readLine 4, readLine 8, readLine 12, readLine 16,
   readLm1Line 0, readLm1Line 4, readLm1Line 8, readLm1Line 12, readLm1Line 16]
```

The counterexample claim, stated in Lean form (not added to the tree and not
machine-checked as a whole):

```lean
theorem plusTwoBarShift_members :
    ∀ line ∈ prog, DischargedALULine line := ...

theorem plusTwoBarShift_not_coverage :
    ¬ PlusTwoInitialFootprintCoverage prog := ...

theorem plusTwoBarShift_correct :
    ProofsLean.Correct plusTwoSealedMachine plusTwoSpec prog := ...
```

The first is a finite syntactic check; the second is the finite address check explained
below; the third is the missing 4096-PE walk/composition. The last one is what turns the
residual from “open” into “false”, and is the only non-routine missing piece.

Semantics: the first pass adds `1` to each input word and writes the low output word;
the second pass reads that output word and adds `1` again, writing `input + 2`. The high
output words are never written and stay `0`. The first line is a single plain `.alu`
row with a `.bar` destination; the other ten are single plain `.alu .inc` rows. Every
source/destination region is a `.word` region.

The audit evaluated the per-PE executor for this program (scratch
`/tmp/wgkz_audit/eval_bar.lean`, `#eval`, no `native_decide`):

```text
-- bar line at PE 0
(1, 0, 0#32)                    -- bar0 = 1, bar1 = 0

-- readLine 0 at input 5, after the bar line
(6, 6)                          -- LM1 words 1 and 7 = 6 = 5 + 1

-- full 11-line program at PE 0, test input: index 3 = 17, all others 5
[(6, 0), (6, 0), (6, 0), (18, 0), (6, 0), ... (6, 0)]
-- after the second pass:
[(7, 0), (7, 0), (7, 0), (19, 0), (7, 0), ... (7, 0)]
```

The final list is `input + 2` in the low word and `0` in the high word, for all 20
outputs, at PE 0. The program is uniform in the input; the `#eval` is only a concrete
check, but the per-cycle computation is the identity `x ↦ x + 1` applied twice.

The representative line shapes also pass the issue checker by direct unfolding
(`LegalParsedLine` for `[barOneExpr]`, `[readExpr 0]`, and `[readLm1Expr 0]` is
machine-checked in `/tmp/wgkz_audit/legal_lines.lean`; no `native_decide`). Their
membership in `DischargedALULine` is the direct syntactic witness (op `.alu`, all
operands `directMemoryAddressModeValid`).

What is missing for a formal refutation:

1. `checkParsedTopLine` for the 11 concrete lines (the representative shapes are
   machine-checked; the concrete copies need the same unfolding).
2. Lifting the per-PE `executeIntegerProducerLineAtPE` computation to
   `executeIntegerProducerLineAtPEs (List.finRange 4096)` and then to
   `executeNormalizedLine`/`plusTwoSealedMachine.step`. The zero/inc rows have no
   input-dependent failure path, so all 4096 PEs succeed; this is a routine but
   non-trivial walk induction.
3. Composing 11 steps and proving `post` for arbitrary input.

None of these is in the tree. Consequently:

* `PlusTwoInitialFootprintCoverage prog` is false (the initial footprints of the bar
  line and the read lines contain no odd LM0 word; the `readLm1Line`s touch LM1, not
  LM0).
* `Correct plusTwoSealedMachine plusTwoSpec prog` is true in the model, but not
  machine-checked in the tree.
* The hypothesis `coverage` of `plusTwoLowerBound_three_of_coverage` is therefore
  **not inhabited** in the model. Once the routine lift above is formalized,
  `plusTwoLowerBound_three_of_coverage` is vacuous.

**Answer to “is it inhabited?”** The *predicate* `PlusTwoInitialFootprintCoverage` is
satisfiable (e.g. any program whose lines jointly read all twenty odd words at the
initial BAR), but the
*universal residual* used by the theorem is false in the model. It is not proved, and
the tree has no `¬ PlusTwoInitialFootprintCoverage` theorem.

### 1.2 `PlusTwoOutputProvenance` — unconditionally true, and unused

Definition (`PlusTwoCompose.lean:1302–1309`):

```lean
def PlusTwoOutputProvenance : Prop :=
  ∀ (program : List InstructionLine),
    ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program →
    ∀ k : Fin 20, ∃ (line : InstructionLine) (member : line ∈ program)
      (state next : State),
      plusTwoSealedMachine.step line state = some next ∧
        (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) =
          (plusTwoZeroWords k) + 2
```

It says: in every correct program, each low output word is observed with value `2` at
*some* step. This is **not** a provenance statement (it does not say the step wrote the
word, or that the value came from a particular input); it is a trivial consequence of
correctness and the initial LM1 being zero:

* the final all-zero-input execution has low word `0 + 2 = 2` by `plusTwoSpec.post`;
* the initial low word is `0` (`plusTwoInitialState_lm1_zero`);
* walking the program, either the word is already `2` after the head (then the head is
  the witness), or it is not, and the induction hypothesis finds a later step.

The audit machine-checked exactly this in scratch
(`/tmp/wgkz_audit/output_prov.lean`, `lake env lean`, no `sorry`/`native_decide`):

```lean
theorem plusTwo_exists_step_reaching_two
    (program : List InstructionLine) (state final : State)
    (target : Fin Bank.lm1.capacity)
    (run : execute plusTwoSealedMachine program state = some final)
    (startNe : (state.peRegisters plusTwoPE).lm1 target ≠ 2)
    (finalEq : (final.peRegisters plusTwoPE).lm1 target = 2) :
    ∃ pre line rest s next, program = pre ++ line :: rest ∧
      execute plusTwoSealedMachine pre state = some s ∧
      plusTwoSealedMachine.step line s = some next ∧
      (next.peRegisters plusTwoPE).lm1 target = 2

theorem plusTwoOutputProvenance_proved : PlusTwoOutputProvenance := ...
```

`#print axioms plusTwoOutputProvenance_proved` reports only
`[propext, Classical.choice, Quot.sound]`.

`PlusTwoOutputProvenance` is **not used anywhere** in the tree (grep finds only its
definition and two docstring mentions, `PlusTwoCompose.lean:89`, `:1295`). It is a live,
trivially satisfiable statement, not a residual. If it were used as a hypothesis, it
would not make a theorem vacuous.

### 1.3 `PlusTwoWriteDeterminationChan`

Definition `ChannelResiduals.lean:2339–2341`:

```lean
def PlusTwoWriteDeterminationChan : Prop :=
  ∀ line, LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line
```

As a statement about **all** lines it is open. On the repaired class
`DischargedALULine` it is discharged:

* `lineDeterminedAtChan_of_aluRows` (`ALUReadSetBound.lean:1169–1175`);
* `plusTwoWriteDeterminationChan_of_aluRows` (`:1179–1183`).

`plusTwo_lowerBound_two` (`PlusTwoCompose.lean:1238–1243`) uses the discharged version
and is unconditional on `DischargedALULine`. The conditional
`plusTwoLowerBound_two_of_determinationChan` (`:1231–1235`) remains a weakening, not a
vacuous theorem: the hypothesis is not known false, and on the class it is proved.

### 1.4 `PlusTwoLineCoverage` — false; `LowerBound 5` theorem is vacuous

Definition `PlusTwoLowerBound.lean:547–553`:

```lean
def PlusTwoLineCoverage : Prop :=
  ∀ (line : InstructionLine) (state next : State),
    plusTwoSealedMachine.step line state = some next →
      ∃ S : Finset (Fin 20), S.card ≤ 4 ∧ ...
```

The tree itself refutes the bound: §4 of `PlusTwoSuffix.lean` (`:249–320`) constructs a
`.zero` row with a width-four LM1 destination at addresses `0,4,8,12`. Four cycles
write words `0..15`, changing eight of the twenty observed low words
(`plusTwoWideZeroLine_changes_eight`, `:312`). `PlusTwoBoundSix.lean:478` states
explicitly: “`plusTwoLowerBound_five_of_coverage` needs the false
`PlusTwoLineCoverage`.”

There is **no named theorem `¬ PlusTwoLineCoverage`**; the tree has the per-PE
computation `plusTwoWideZeroLine_changes_eight` and the prose, but not the lifted
`¬` statement. In substance the residual is false, and
`plusTwoLowerBound_five_of_coverage` (`PlusTwoLowerBound.lean:604`) is vacuous.
`plusTwo_execute_coverage` (`:567`), which also takes `PlusTwoLineCoverage`, is
vacuous for the same reason.

### 1.5 `PlusTwoLineWriteBudget` / `PlusTwoFirstLineCorrectBudget`

Definitions `PlusTwoBoundSix.lean:362–370` and `:372–380`. These are the per-line
write budgets used by `plusTwoLowerBound_four_of_lineBudgets` (`:420`) and
`plusTwoLowerBound_four_of_writeBudgets` (`PlusTwoCompose.lean:1280–1283`). The audit
found **no proof and no refutation** of either. They are not refuted by the wide
`.zero` line: that line changes eight words, which is exactly the budget 8; the
first-line budget is about *correct* words at the all-zero input, not changed words.

Status: open, conditional/live. There is no unconditional `LowerBound 4` in the tree.

### 1.6 `PlusTwoLineFootprintCoversPreparedReads` (old) vs the repaired residual

Old definition `ChannelResiduals.lean:1436–1445`. It is refuted in substance by the
`.zero` row’s read-modify-write of its destination:

* `FootprintCoverage.lean:7–18` states the residual “as stated in
  `ChannelResiduals.lean` is false, hence ... currently vacuous”.
* `FootprintCoverage.lean:52–70` explains the obstruction: a `.zero`/`.immediate`
  row’s destination read is in `preparedListReadSet`, but the hazard lowering reports
  only the destination’s write event and `peLineSourceAccesses` filters writes out, so
  the footprint is empty.
* `zeroRow_readSet_nonempty` (`:565`) machine-checks the read-set half at every state.

The repaired residual `PlusTwoALULineFootprintCoversPreparedReads`
(`ALUReadSetBound.lean:1105–1116`) restricts rows to `.alu` and addressable
sources/destinations and is **proved** (`:1120–1122`). The old conditional theorems
`plusTwoWriteDeterminationChan_of_discharged` (`ChannelResiduals.lean:2287`) and
`plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` (`:2298`) are
vacuous. The new `..._of_aluRows` versions (`ALUReadSetBound.lean:1179`, `:1187`) are
unconditional on `DischargedALULine` and live.

### 1.7 `PlusTwoSuffixPreservesWitness` (recorded-answer route)

Definition `PlusTwoLowerBound.lean:503–510`. It is false in substance:
`PlusTwoSuffix.lean:27–30` says the unconditional frame is false;
`plusTwoSuffixLine2_perPE_frame_false` (`:327`) gives the per-PE counterexample; the
`bar1 = 0` state restriction is the true statement
`PlusTwoSuffixPreservesWitnessOfBar1Zero` (`:418–426`). The recorded-answer theorem
`plusTwoRecorded_not_correct_of_suffixFrame` (`PlusTwoLowerBound.lean:512`) is
conditional on the false frame and is therefore vacuous. The corrected
`plusTwoRecorded_not_correct` (`PlusTwoSuffixFrame.lean:787`) is unconditional and
live.

---

## 2. AB residuals (`1.a-b`)

### 2.1 The equivalence is real

`abLowerBound_two_iff_residuals` (`ABUnconditional.lean:650–661`):

```lean
theorem abLowerBound_two_iff_residuals :
    LowerBound abSealedMachine abSpec 2 ↔
      ABPlainDoubleResidual ∧ ABNonPlainResidual := by
  constructor
  · intro lower
    refine ⟨?_, ?_⟩
    · intro e unrefuted _plain _shape
      exact (abLowerBound_two_iff_residual.mp lower) [e] unrefuted
    · intro expressions unrefuted _plainLine
      exact (abLowerBound_two_iff_residual.mp lower) expressions unrefuted
  · rintro ⟨plainDouble, nonPlain⟩
    exact abLowerBound_two_of_residuals plainDouble nonPlain
```

It uses `abLowerBound_two_iff_residual` (`ABLowerBound.lean:714–722`), which is a
genuine equivalence between the lower bound and the one-line residual class
`AbPEUnrefuted` (`:581–585`), proved via the cost-1 line reduction. The forward
direction of `abLowerBound_two_iff_residuals` is actually stronger than the stated
`ABPlainDoubleResidual`: it uses the lower bound at `[e]` for **every** unrefuted plain
row, not only the `.double`-shaped ones. That is valid (the extra hypotheses `_plain`
and `_shape` are unused). The reverse direction uses
`abLowerBound_two_of_residuals` (`:607–630`), which case-splits `ABPlainLine` and
`abPE_plain_not_correct_or_doubleCase`. There is no circularity and no weakening hidden
in the equivalence.

The residuals themselves:

* `ABPlainDoubleResidual` (`:585–590`) quantifies over an unrefuted single plain row
  whose shape is `ABPlainImmediateDouble` or `ABPlainZeroDouble`.
* `ABNonPlainResidual` (`:597–600`) quantifies over an unrefuted line that is not a
  single plain row.

Both are **open**; neither is refuted by anything in the tree.

### 2.2 Does the `.zero` read-modify-write finding refute them?

No. The `.zero` finding is about `PlusTwoLineFootprintCoversPreparedReads`, a
different residual of the plus-two read kernel. `FootprintCoverage.zeroRow` is a
`.zero` row with an **LM0** destination; its read set is nonempty because the masked
destination is read-modify-written. That says nothing about one-line **correctness** of
an AB line. `ABPlainZeroDouble` uses `Lm1WritesDoubleCopy` (`WelcomeValueBound.lean:722`)
and `IsWelcomeCopy` (`:121–127`); zero data satisfies `IsWelcomeCopy` (the zero theorem
is `isWelcomeCopy_zero`, `:126`). A `.zero` row with a `.double` LM1 destination is
therefore a genuine instance of the `ABPlainDoubleResidual` shape, but it writes zero
data at the `A = 1, B = 0` witness, where the target is `0x3F800000`; it is **incorrect**,
which is the residual’s conclusion, not a counterexample to it.

No theorem of the form `¬ ABPlainDoubleResidual`, `¬ ABNonPlainResidual`, or a proof of
a correct one-line AB program exists in the tree (grep over all `ProofsLean/*.lean`).
The only positive correctness statements for AB are none; `abLowerBound_two` is not
proved unconditionally.

### 2.3 Does the `.matrixRead` family closure refute `ABNonPlainResidual`?

No; it is a **partial proof**, not a refutation. `FamilyDestinationCongruence.lean`:

* `abPE_not_correct_of_matrixReadNarrowClosed` (`:743–753`) refutes a single
  `.matrixRead` row with a narrow zero-state write list. This is one family inside
  `ABNonPlainResidual`.
* `abNonPlainResidual_of_matrixReadFamily` (`:761–770`) proves `ABNonPlainResidual`
  **provided** every other non-plain line is refuted (the `rest` hypothesis). It is a
  decomposition of the residual, not an unconditional proof or a negation.

The theorem is conditional on `rest`; the `.matrixRead` branch itself is closed. No
`¬ ABNonPlainResidual` follows.

---

## 3. Cend residuals (`12.convert-endian`)

### 3.1 Class definitions and inclusions

`CendClosedLines` (`CendUnconditional.lean:993–996`):

```lean
def CendClosedLines (expressions : List NormalizedExpr) : Prop :=
  CendAllMatrixReadLines expressions ∨
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)
```

`CendPENonClosedRefuted` (`:1010–1013`):

```lean
def CendPENonClosedRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, ¬ CendClosedLines expressions →
    ¬ Correct cendSealedMachine cendSpec ([.pe expressions] : List InstructionLine)
```

The prose (`:1011–1012`, `:1008–1009`) says: “every `.pe` line outside
`CendClosedLines`: it has at least one `.matrixRead`-free row and at least one row that
writes a PE register file.” That matches the definition. The two closed classes are
exactly the all-`.matrixRead` lines and the PE-inert lines (`:960–999`).

One nuance the prose understates: `CendPENonClosedRefuted` does **not** restrict to
`CendPEUnrefuted` (`ConvertEndianLowerBound.lean:328–332`). It includes syntactically
rejected lines, wait-pending lines, unsupported-ALU lines, all-`.noforward` lines, and
constant lines outside the closed classes (`CendConstantLines`), even though those classes are
already unconditionally refuted. This makes the residual *coarser than the minimal
gap*, but not unsound: `cendPELinesRefuted_of_nonClosed` (`:1017–1025`) uses only
`¬closed`; the already-refuted classes still satisfy the conclusion. The equivalence `cendPELinesRefuted_iff_nonClosed` (`:1027–1032`) is real
because the forward direction is trivial and the reverse direction uses the already
proved `cendPE_closedLines_not_correct` for the closed class.

`CendValueResidual` (`:1045–1049`) is the minimal version restricted to
`CendPEUnrefuted`; `cendLowerBound_two_iff_residual` (`:1065–1071`) is a real
equivalence.

### 3.2 `CendPENonConstantRefuted`

`CendConstantLines` (`ProgramWitness.lean:802–807`) is a single plain row whose op is
`.zero` or `.immediate`. `CendPENonConstantRefuted` (`:831–835`) excludes both
`CendClosedLines` and `CendConstantLines`:

```lean
def CendPENonConstantRefuted : Prop :=
  ∀ expressions, ¬ CendClosedLines expressions →
    ¬ CendConstantLines expressions →
    ¬ Correct cendSealedMachine cendSpec ([.pe expressions] : List InstructionLine)
```

`cendPENonClosedRefuted_of_nonConstant` (`:838–844`) is sound:

```lean
intro expressions closed correct
by_cases constant : CendConstantLines expressions
· exact cendPE_constantLines_not_correct expressions constant correct
· exact rest expressions closed constant correct
```

Constant lines are refuted unconditionally by `cendPE_constantLines_not_correct`
(`:809–815`), itself from `cendPE_constantLine_not_correct` (`:792–799`). The
`¬constant` hypothesis is therefore removable: the two residuals are logically
equivalent, even though `CendPENonConstantRefuted` is syntactically “smaller” (fewer
cases). The class inclusions match the prose: the constant family is exactly a single
plain `.zero`/`.immediate` row; a multi-row line containing a constant row is still in
the nonconstant residual, which is consistent with the prose.

Neither `CendPENonClosedRefuted` nor `CendPENonConstantRefuted` is proved or refuted in
the tree. No correct one-line Cend program is proved anywhere. The conditional theorems
are live but conditional, not vacuous.

### 3.3 `CendTwoLinesRefuted` and the bound-three theorem

`CendTwoLinesRefuted` (`ConvertEndianLowerBound.lean:463–468`) is an open two-line
obligation. `cendLowerBound_three_of_residuals` (`:470–509`) is conditional on it and
on `CendPELinesRefuted`; `cendLowerBound_three_iff_residuals` (`:512–530`) is a real
equivalence. No proof or refutation of the two-line obligation exists in the tree.

---

## 4. Other false residuals already in the tree

These are not part of the three named residuals, but they matter for the “is the
theorem vacuous?” question and for the accumulation warning.

### 4.1 Welcome L1 packages

`WelcomePEL1BMWriterData` (`WelcomeWriterPackages.lean:581` region) is **false**:

```lean
theorem l1ToPESecondRow_oldPackage_false : ¬ WelcomePEL1BMWriterData := ...
theorem l1ToPETwoDestination_weakPackage_false :
    ¬ WelcomePEL1BMWriterDataNoSingleton := ...
```

Consequences:

* `WelcomePEWriterKindDataResiduals` (`WelcomeAssemblyFinal.lean:322–325`) contains
  `WelcomePEL1BMWriterData`, so it is false (`welcomePEWriterKindDataResiduals_false`,
  `WelcomeWriterPackages.lean:1147`).
* `WelcomePEWriterKindDataResidualsThree` (`WelcomeWriterPackages.lean:1123–1126`)
  contains `WelcomePEL1BMWriterDataNoSingleton`, so it is false
  (`...Three_false`, `:1154`).
* The conditional lower bounds taking these bundles/components are vacuous:
  `welcomeLowerBound_two_of_writerKindData` (`WelcomeAssemblyFinal.lean:370`),
  `welcomeLowerBound_two_of_writerKindDataResiduals` (`:379`),
  `welcomeLowerBound_two_of_plainReadL1` (`WelcomeWriterPackages.lean:1162`).
* `welcomeLowerBound_two_of_plainReadL1MultiDest` (`WelcomeL1MultiDest.lean:1330`)
  avoids the false singleton component (it takes only the plain and `.matrixRead`
  packages) and is a live conditional, not vacuous.

The final `welcomeLowerBound_two` (`WelcomeOptimalFinal.lean:159`) uses
`WelcomePELm1WriteShapeObligation`, which is proved (`:141`) by a different route. So
the Welcome headline result is **not** vacuous; only the old conditional routes are.

### 4.2 `WelcomePEMixedPlainInertFlagAgreement`

`WelcomePEMixedPlainInertFlagAgreement` (`WelcomeMixedStructure.lean:597`) is false:
`welcomePEMixedPlainInertFlagAgreement_false` (`WelcomeFlagAgreement.lean:331`) gives an
accepted mixed plain/inert witness whose line flag differs from the plain row flag.
Conditional theorems taking `(flag : WelcomePEMixedPlainInertFlagAgreement)` in
`WelcomeMixedStructure.lean:753`, `:839`, `:870` are therefore vacuous. The final
Welcome theorem bypasses this bundle.

### 4.3 The plus-two read-coverage residual

Discussed in §1.6: `PlusTwoLineFootprintCoversPreparedReads` is false and its
conditional theorems are vacuous. The repaired `.alu`-only version is proved.

---

## 5. Full theorem scan

The scan covered every declaration in `ProofsLean/*.lean` whose statement mentions
`LowerBound` or `¬ Correct` (198 declarations; 66 mention `LowerBound`, 142 are
`¬ Correct` refutations, with the equivalences overlapping). The important distinction
is:

* **Conditional on a named open/false residual** — potentially vacuous, listed below.
* **Unconditional refutation of a concrete line/state** — live; its hypotheses are
  step/check facts, not open universal Props.
* **Equivalence theorem** — live; it is a logical equivalence, not a residual.

### 5.1 `LowerBound`-conclusion theorems

#### Closed / live

| Theorem | Location | Hypotheses | Status |
|---|---|---|---|
| `welcomeLowerBound_two` | `WelcomeOptimalFinal.lean:159` | none | **closed**, uses proved `welcomePELm1WriteShapeObligation` |
| `welcomeWholeMachine_lowerBound_two` | `WelcomeWholeMachineOptimal.lean:732` | none | closed |
| `welcomeWhole_partialLowerBound` | `WelcomeWholeMachineOptimal.lean:865` | none | closed |
| `welcomeLowerBound_one` | `WelcomeLowerBound.lean:424` | none | closed |
| `two_line_lower_bound` | `PlusOne.lean:335` | none | closed |
| `BoundCertificate.sound` | `Optimality.lean:19` | certificate data | live (certificate consumer) |
| `SymbolicBoundCertificate.sound` | `Optimality.lean:38` | certificate data | live (certificate consumer) |

There is **no unconditional `LowerBound` theorem** in the tree for:
`abSealedMachine` (AB), `cendSealedMachine` (Cend), `plusTwoSealedMachine` at bound
`≥ 3`, `mul7SealedMachine`, or `aplusbSealedMachine`. (`plusTwo_lowerBound_two`,
`PlusTwoCompose.lean:1238`, is a `2 ≤ score` theorem, not a `LowerBound` conclusion, and
is unconditional only on `DischargedALULine`.)

#### Conditional on open residuals (live but conditional)

| Theorem | Location | Residual hypothesis | Status |
|---|---|---|---|
| `abLowerBound_two_of_residual` | `ABLowerBound.lean:702` | `AbPEUnrefuted` one-line residual | open |
| `abLowerBound_two_of_residuals` | `ABUnconditional.lean:607` | `ABPlainDoubleResidual`, `ABNonPlainResidual` | open |
| `abLowerBound_two_of_rightWindowData` | `ABUnconditional.lean:637` | `ABRightWindowData` | open |
| `abResiduals_of_rightWindowData` | `ABUnconditional.lean:666` | `ABRightWindowData` | open |
| `abNonPlainResidual_of_matrixReadFamily` | `FamilyDestinationCongruence.lean:761` | `rest` (all other non-plain lines) | open |
| `cendLowerBound_two_of_peLines` | `ConvertEndianLowerBound.lean:344` | `CendPELinesRefuted` | open |
| `cendLowerBound_two_of_unrefuted` | `ConvertEndianLowerBound.lean:377` | `CendPEUnrefuted` residual | open |
| `cendLowerBound_two_of_nonClosed` | `CendUnconditional.lean:1037` | `CendPENonClosedRefuted` | open |
| `cendLowerBound_two_of_residual` | `CendUnconditional.lean:1055` | `CendValueResidual` | open |
| `cendLowerBound_two_of_nonConstant` | `ProgramWitness.lean:846` | `CendPENonConstantRefuted` | open |
| `cendLowerBound_two_of_lineWitness` | `ProgramWitness.lean:865` | `CendLineWitnessObligation` | open |
| `cendLowerBound_two_of_witnessValueResidual` | `ProgramWitness.lean:884` | `CendWitnessValueResidual` | open |
| `cendLowerBound_three_of_residuals` | `ConvertEndianLowerBound.lean:470` | `CendPELinesRefuted`, `CendTwoLinesRefuted` | open |
| `plusTwoLowerBound_two_of_determinationChan` | `PlusTwoCompose.lean:1231` | `PlusTwoWriteDeterminationChan` | open generally, discharged on `DischargedALULine` |
| `plusTwoLowerBound_three_of_coverage` | `PlusTwoCompose.lean:1266` | `PlusTwoInitialFootprintCoverage` universal | **semantically false, formal lift missing** |
| `plusTwoLowerBound_four_of_lineBudgets` | `PlusTwoBoundSix.lean:420` | `PlusTwoLineWriteBudget`, `PlusTwoFirstLineCorrectBudget` | open |
| `plusTwoLowerBound_four_of_writeBudgets` | `PlusTwoCompose.lean:1280` | same two | open |
| `mul7LowerBound_two_of_peFootprint` | `Mul7LowerBound.lean:231` | `Mul7PELineFootprint` | open |
| `aplusbLowerBound_two_of_residual` | `AplusBLowerBound.lean:1036` | `AplusBPEUnrefuted` one-line residual | open |
| `welcomeLowerBound_two_of_lm1WriteShapes` | `WelcomeValueBound.lean:694` | `WelcomePELm1WriteShapeObligation` | **proved** hypothesis; discharged |
| `welcomeLowerBound_two_of_dispatch` | `WelcomeFinalShape.lean:806` | `WelcomePEDispatchResiduals` | superseded; not used by the unconditional theorem |
| `welcomeLowerBound_two_of_components` | `WelcomeFinalShape.lean:897` | five component packages | superseded; some components false |
| `welcomeLowerBound_two_of_allWordsChanged` | `WelcomeBoundTwo.lean:518` | `WelcomePEUnrefuted` residual | superseded |
| `welcomeLowerBound_two_of_residual` | `WelcomeBoundTwo.lean:591` | `WelcomePEResidual` residual | superseded |
| `welcomeLowerBound_two_of_unrefuted` | `WelcomeLowerBoundTwo.lean:527` | `WelcomePEUnrefuted` residual | superseded |
| `welcomeLowerBound_two_of_writerKindData` | `WelcomeAssemblyFinal.lean:370` | contains false `WelcomePEL1BMWriterData` | **vacuous** |
| `welcomeLowerBound_two_of_writerKindDataResiduals` | `WelcomeAssemblyFinal.lean:379` | `WelcomePEWriterKindDataResiduals` false | **vacuous** |
| `welcomeLowerBound_two_of_plainReadL1` | `WelcomeWriterPackages.lean:1162` | contains false `WelcomePEL1BMWriterDataNoSingleton` | **vacuous** |
| `welcomeLowerBound_two_of_plainReadL1MultiDest` | `WelcomeL1MultiDest.lean:1330` | plain + matrixRead packages | live conditional (avoids false L1 package) |
| `welcomeLowerBound_two_of_twoShapeObligations` | `WelcomeProvenance.lean:593` | double/narrow shape obligations | superseded |
| `welcomeLowerBound_two_of_residualDoubleShape` | `WelcomeProvenance.lean:371` | double-shape residual | superseded |

#### Vacuous by a false residual

* `plusTwoLowerBound_five_of_coverage` (`PlusTwoLowerBound.lean:604`) — assumes
  `PlusTwoLineCoverage`, false (§1.4).
* `welcomeLowerBound_two_of_writerKindDataResiduals` and
  `welcomeLowerBound_two_of_writerKindData` — false L1 component (§4.1).
* `welcomeLowerBound_two_of_plainReadL1` — false singleton L1 component (§4.1).
* `plusTwo_execute_coverage` (`PlusTwoLowerBound.lean:567`) — same `PlusTwoLineCoverage`.

### 5.2 Conditional `¬ Correct` theorems

The audit found only a small set of `¬ Correct` theorems whose hypothesis is a named
residual (as opposed to a concrete state/step/check fact or a line-shape case that the
proof itself splits):

| Theorem | Location | Residual hypothesis | Status |
|---|---|---|---|
| `abPE_not_correct_of_rightWindowData` | `ABUnconditional.lean:542` | `ABRightWindowData` | open; conditional/live |
| `plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` | `ChannelResiduals.lean:2298` | `PlusTwoLineFootprintCoversPreparedReads` | **vacuous** (§1.6) |
| `plusTwo_not_correct_of_determinationChan` | `ChannelResiduals.lean:2351` | `PlusTwoWriteDeterminationChan` | open generally; discharged on class |
| `plusTwo_not_correct_of_footprint_avoids_chan` | `InputDependenceChannels.lean:835` | `determined : ∀ line ∈ program, LineDeterminedAtChan ...` | open generally; discharged on class |
| `plusTwo_not_correct_of_footprint_avoids` | `InputDependence.lean:995` | `determined : ∀ line ∈ program, LineDeterminedAt ...` | open generally; discharged on class |
| `mul7PELine_not_correct` | `Mul7LowerBound.lean:214` | `Mul7PELineFootprint` | open; conditional/live |
| `mul7ShortLine_not_correct` | `Mul7LowerBound.lean:220` | `Mul7PELineFootprint` | open; conditional/live |
| `welcomePE_not_correct_of_noLm1Destination` | `WelcomeAssembly.lean:1077` | `WelcomePEIntegerStageLm1Frame`, `WelcomePEStageLm1Frame` | live if frames proved; not a residual of the named kind |
| `aplusbPENotUnrefuted_not_correct` | `AplusBLowerBound.lean:948` | `¬ AplusBPEUnrefuted` (outside class) | live refutation, not a residual |

Everything else with a `¬ Correct` conclusion (roughly 130 theorems) is a refutation of
a concrete class: empty program, `nop`, `mv`, rejected/waiting/unsupported `.pe`,
all-`.noforward`, narrow window, `ABNarrowAtOnes`, `matrixRead` all-read, inert lines,
constant `.zero`/`.immediate`, etc. Their hypotheses are state/step/check facts or
shape data that the proof constructs or splits; they are **not** unproved universal
residuals and are live. The per-file counts are large:
`ABLowerBound` 17, `ConvertEndianLowerBound` 15, `WelcomeLowerBoundTwo` 13,
`WelcomeLowerBound` 10, `ProgramWitness` 18, `AplusBLowerBound` 16,
`GenericLowerBound` 17, `WelcomeValueBound` 6, etc.

### 5.3 The “proved negation” question

| Hypothesis | Negation proved in tree? | Where |
|---|---|---|
| `PlusTwoLineCoverage` | **No named `¬`; refuted in substance** | `PlusTwoSuffix.lean:249–320`, `:312`; prose `PlusTwoBoundSix.lean:478` |
| `PlusTwoLineFootprintCoversPreparedReads` | **No named `¬`; refuted in substance** | `FootprintCoverage.lean:7–18`, `:565`; repair at `ALUReadSetBound.lean:1120` |
| `PlusTwoSuffixPreservesWitness` | **No named `¬`; per-PE false theorem only** | `PlusTwoSuffix.lean:327`; corrected frame `:418`; unconditional `PlusTwoSuffixFrame.lean:787` |
| `WelcomePEL1BMWriterData` | **Yes** | `WelcomeWriterPackages.lean:885` |
| `WelcomePEL1BMWriterDataNoSingleton` | **Yes** | `WelcomeWriterPackages.lean:1032` |
| `WelcomePEWriterKindDataResiduals` | **Yes** | `WelcomeWriterPackages.lean:1147` |
| `WelcomePEWriterKindDataResidualsThree` | **Yes** | `WelcomeWriterPackages.lean:1154` |
| `WelcomePEMixedPlainInertFlagAgreement` | **Yes** | `WelcomeFlagAgreement.lean:331` |
| `PlusTwoInitialFootprintCoverage` | **No** (only the semantic counterexample in §1.1) | — |
| `ABPlainDoubleResidual`, `ABNonPlainResidual`, `ABRightWindowData` | **No** | — |
| `CendPENonClosedRefuted`, `CendPENonConstantRefuted`, `CendValueResidual`, `CendTwoLinesRefuted` | **No** | — |
| `PlusTwoLineWriteBudget`, `PlusTwoFirstLineCorrectBudget`, `PlusTwoWriteDeterminationChan` | **No** | — |
| `Mul7PELineFootprint`, AplusB residual | **No** | — |

---

## 6. Recommendations

1. **Do not use `plusTwoLowerBound_three_of_coverage` as evidence for `LowerBound 3`.**
   Either (a) formalize the 11-line counterexample’s `Correct` theorem and then state
   `¬ PlusTwoInitialFootprintCoverage` / refute the hypothesis, or (b) replace it by a
   residual that is actually invariant under BAR updates (e.g. “every input word is in
   the footprint of some line at *some* prefix state of the all-zero execution, with a
   prefix-context relation”), and prove that form. The current statement is false in
   the model.
2. **Keep `PlusTwoOutputProvenance` but stop calling it a residual.** It is a theorem;
   it does not record provenance of values and does not support a counting argument.
3. **Retire `PlusTwoLineCoverage` and the old `PlusTwoLineFootprintCoversPreparedReads`.**
   The tree already knows they are false. `plusTwoLowerBound_five_of_coverage`,
   `plusTwo_execute_coverage`, `plusTwoWriteDeterminationChan_of_discharged`, and
   `plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` are vacuous.
   Use the `.alu`-only repaired residual (`ALUReadSetBound.lean:1105`, proved).
4. **Retire the false Welcome L1 bundles.** `WelcomePEWriterKindDataResiduals`,
   `...Three`, `WelcomePEL1BMWriterData`, `...NoSingleton`, and the conditional lower
   bounds taking them are vacuous. Keep the unconditional
   `welcomeLowerBound_two` (`WelcomeOptimalFinal.lean:159`), which does not depend on
   them.
5. **AB and Cend residuals are open, not vacuous.** The `abLowerBound_two_iff_residuals`
   equivalence is genuine; the `.zero` and `.matrixRead` findings do not refute it.
   Cend’s class inclusions are sound, but note that `CendPENonClosedRefuted` and
   `CendPENonConstantRefuted` are coarser than the minimal `CendValueResidual` because
   they include already-refuted lines. This is a documentation mismatch, not a
   soundness problem.
6. **Add a regression check.** Any new `def ... : Prop` used as a theorem hypothesis
   should either be proved inhabited, have a proved negation check, or be marked
   `-- open residual, no satisfiability claim`. The project has already paid for this
   three times (`PlusTwoWriteDetermination`, `PEChannelFrame`,
   `PlusTwoLineFootprintCoversPreparedReads`) and now a fourth
   (`PlusTwoInitialFootprintCoverage`).

---

## Appendix A. Scratch evidence

All scratch files are outside the repository and were run with
`cd proofs_lean && lake env lean <file>`.

* `/tmp/wgkz_audit/output_prov.lean` — proof of `PlusTwoOutputProvenance`
  (`plusTwoOutputProvenance_proved`), `#print axioms` = standard three.
* `/tmp/wgkz_audit/eval_bar.lean` — `#eval` of the BAR line and the 11-line
  counterexample at PE 0; outputs `input + 2` and high word `0` for a concrete test
  input. This is evidence, not a theorem.
* `/tmp/wgkz_audit/widezero_legal.lean`, `/tmp/wgkz_audit/widezero_legal2.lean` —
  issue-check proofs for the wide-zero line (used to sanity-check the `PlusTwoLineCoverage`
  counterexample).
* `/tmp/wgkz_audit/covers_false.lean`, `/tmp/wgkz_audit/covers_false2.lean` — partial
  proof of `¬ PlusTwoLineFootprintCoversPreparedReads` from the `.zero` obstruction;
  the remaining goal is the footprint-empty lemma, which is routine but was not
  completed in this audit.

No repository file was modified. The only deliverable is this report.

---

## Appendix B. Scan index (198 declarations)
Every declaration whose statement *mentions* `LowerBound` or `¬ Correct`, with its
file and starting line. Some of these mention the token only in a hypothesis or in a
docstring-adjacent line; the conclusion-level classification is in §5.1–§5.3.
Entries marked there as conditional or vacuous are the exceptions; the remaining
entries are live concrete refutations, equivalences, or parameterized generic
theorems.

### `ProofsLean/ABLowerBound.lean`

```text
  318  ab_not_correct_of_step_none
  332  ab_not_correct_of_step_frame
  376  abEmpty_not_correct
  401  abNop_not_correct
  417  abMv_not_correct
  431  abPE_checkFalse_not_correct
  449  abPE_waitPending_not_correct
  460  abPE_unsupported_not_correct
  473  abPE_notSupported_not_correct
  491  abPE_noforward_not_correct
  514  abPE_singleWelcomeLine_not_correct
  599  abPENotUnrefuted_not_correct
  637  abShortLine_not_correct
  669  abLowerBound_two_iff_rejects_short_lines
  702  abLowerBound_two_of_residual
  714  abLowerBound_two_iff_residual
  755  ab_not_correct_of_narrowAtOnes
```

### `ProofsLean/ABNarrowPlain.lean`

```text
   70  abPE_singleWelcomeLine_not_correct_of_narrow
```

### `ProofsLean/ABUnconditional.lean`

```text
  418  abPE_plain_narrow_not_correct
  496  abPE_plain_not_correct_or_doubleCase
  542  abPE_not_correct_of_rightWindowData
  570  abPE_not_correct_of_plainClosed
  607  abLowerBound_two_of_residuals
  637  abLowerBound_two_of_rightWindowData
  650  abLowerBound_two_iff_residuals
  666  abResiduals_of_rightWindowData
```

### `ProofsLean/ABWidthBound.lean`

```text
  412  ab_not_correct_of_lm1TotalWidth
  482  ab_not_correct_of_lm1WidthNotDouble
```

### `ProofsLean/ALUReadSetBound.lean`

```text
 1187  plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_aluRows
```

### `ProofsLean/AplusBLowerBound.lean`

```text
  761  aplusb_not_correct_of_step_none
  774  aplusb_not_correct_of_step_frame
  820  aplusbEmpty_not_correct
  836  aplusbNop_not_correct
  851  aplusbMv_not_correct
  867  aplusbPE_checkFalse_not_correct
  880  aplusbPE_waitPending_not_correct
  891  aplusbPE_unsupported_not_correct
  904  aplusbPE_notSupported_not_correct
  919  aplusbPE_noforward_not_correct
  948  aplusbPENotUnrefuted_not_correct
  986  aplusbShortLine_not_correct
 1003  aplusbLowerBound_two_iff_rejects_short_lines
 1036  aplusbLowerBound_two_of_residual
 1046  aplusbLowerBound_two_iff_residual
 1265  aplusb_not_correct_of_lm0Narrow
```

### `ProofsLean/CendPlainWitness.lean`

```text
  229  cendPE_plain_not_correct_of_freeHalves
  323  cendPE_plain_not_correct_of_readSet
  337  cendPE_plain_not_correct_of_avoidsHigh
  346  cendPE_plain_not_correct_of_avoidsLow
  380  cendPE_plain_not_correct
```

### `ProofsLean/CendUnconditional.lean`

```text
  234  cend_not_correct_of_lm1_zero
  326  cend_not_correct_of_commit_lm1_zero
  581  cendPE_matrixRead_not_correct
  906  cendPE_allMatrixReadLines_not_correct
  947  cendPE_not_correct_of_allMatrixReadLines
  970  cendPE_inertLines_not_correct
  999  cendPE_closedLines_not_correct
 1037  cendLowerBound_two_of_nonClosed
 1055  cendLowerBound_two_of_residual
 1065  cendLowerBound_two_iff_residual
```

### `ProofsLean/ChannelResiduals.lean`

```text
 2298  plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged
 2351  plusTwo_not_correct_of_determinationChan
```

### `ProofsLean/ConvertEndianLowerBound.lean`

```text
  166  cend_not_correct_of_step_none
  179  cend_not_correct_of_step_frame
  205  cendEmpty_not_correct
  222  cendNop_not_correct
  234  cendMv_not_correct
  256  cendPE_checkFalse_not_correct
  264  cendPE_waitPending_not_correct
  274  cendPE_unsupported_not_correct
  286  cendPE_notSupported_not_correct
  301  cendPE_noforward_not_correct
  344  cendLowerBound_two_of_peLines
  364  cendLowerBound_two_iff_peLines
  377  cendLowerBound_two_of_unrefuted
  470  cendLowerBound_three_of_residuals
  512  cendLowerBound_three_iff_residuals
```

### `ProofsLean/DoubleWindowValue.lean`

```text
 1266  ab_not_correct_of_lm1DoubleWindow
 1342  ab_not_correct_of_lm1WidthNotDouble'
 1400  abPE_not_correct_of_widthOrDoubleWindow
```

### `ProofsLean/FamilyDestinationCongruence.lean`

```text
  640  abPE_matrixRead_narrow_not_correct
  703  abPE_matrixRead_not_correct_of_staticWidth
  743  abPE_not_correct_of_matrixReadNarrowClosed
  761  abNonPlainResidual_of_matrixReadFamily
```

### `ProofsLean/FiniteExample.lean`

```text
   57  rejects_all_short
   96  testcase_correct_does_not_imply_general_correct
  101  one_case_has_no_two_line_lower_bound
```

### `ProofsLean/GenericLowerBound.lean`

```text
  186  lowerBound_two_iff_rejects_unit_lines
  207  lowerBound_two_iff_rejects_short_lines
  220  lowerBound_two_of_residual
  244  lowerBound_two_iff_residual
  276  OneLineRefutation.not_correct
  284  lowerBound_two_of_oneLineRefutations
  294  lowerBound_two_of_residual_oneLineRefutations
  306  sealedLowerBound_two_iff_rejects_unit_lines
  319  sealedLowerBound_two_of_oneLineRefutations
  334  sealed_empty_not_correct
  829  hazardProblem_empty_not_correct
  919  hazardProblem_lowerBound_two_of_sealed
  943  hazardProblem_lowerBound_two_of_sealed_of_nil_pending
  959  symbolicBoundCertificate_sound
  965  boundCertificate_sound
  986  certificate_rejects_short_line
  994  sealedCertificate_rejects_every_short_line
```

### `ProofsLean/InputDependence.lean`

```text
  995  plusTwo_not_correct_of_footprint_avoids
```

### `ProofsLean/InputDependenceChannels.lean`

```text
  475  plusTwo_not_correct_of_footprint_avoids_chan
  835  plusTwo_not_correct_of_concrete_footprint_avoids_chan
```

### `ProofsLean/Mul7LowerBound.lean`

```text
  131  mul7_oneLine_not_correct_of_footprint
  151  mul7Empty_not_correct
  196  mul7NopLine_not_correct
  201  mul7MvLine_not_correct
  214  mul7PELine_not_correct
  220  mul7ShortLine_not_correct
  231  mul7LowerBound_two_of_peFootprint
  252  mul7LowerBound_two_iff_shortLines
```

### `ProofsLean/Optimality.lean`

```text
   19  BoundCertificate.sound
   38  SymbolicBoundCertificate.sound
   67  shorter_correct_refutes_bound
```

### `ProofsLean/PlusOne.lean`

```text
  305  empty_incorrect
  314  one_line_incorrect
  335  two_line_lower_bound
```

### `ProofsLean/PlusTwoBoundSix.lean`

```text
  420  plusTwoLowerBound_four_of_lineBudgets
```

### `ProofsLean/PlusTwoCompose.lean`

```text
 1231  plusTwoLowerBound_two_of_determinationChan
 1266  plusTwoLowerBound_three_of_coverage
 1280  plusTwoLowerBound_four_of_writeBudgets
```

### `ProofsLean/PlusTwoLowerBound.lean`

```text
  512  plusTwoRecorded_not_correct_of_suffixFrame
  604  plusTwoLowerBound_five_of_coverage
```

### `ProofsLean/PlusTwoSuffix.lean`

```text
  442  plusTwoRecorded_not_correct_of_bar1Frame
```

### `ProofsLean/PlusTwoSuffixFrame.lean`

```text
  787  plusTwoRecorded_not_correct
```

### `ProofsLean/ProgramWitness.lean`

```text
  468  not_correct_of_collision
  521  cendPE_not_correct_of_candidatePair
  582  cend_not_correct_of_output_ne
  602  cend_not_correct_of_step_stuck
  615  cendPE_not_correct_of_freeHalves
  661  cendPE_not_correct_of_factorsThrough
  677  cendPE_not_correct_of_signature
  689  cendPE_not_correct_of_inputIndependent
  792  cendPE_constantLine_not_correct
  809  cendPE_constantLines_not_correct
  846  cendLowerBound_two_of_nonConstant
  865  cendLowerBound_two_of_lineWitness
  884  cendLowerBound_two_of_witnessValueResidual
  938  cendPE_plainALUNarrow_not_correct
  966  cendPE_plainALUWide_not_correct
 1002  cendPE_mslMsr_not_correct
 1034  cendPE_floatMAU_not_correct
 1059  cendPE_blockFloat_not_correct
```

### `ProofsLean/Semantics.lean`

```text
   61  refutes_not_correct
```

### `ProofsLean/WelcomeAssembly.lean`

```text
 1077  welcomePE_not_correct_of_noLm1Destination
```

### `ProofsLean/WelcomeAssemblyFinal.lean`

```text
  370  welcomeLowerBound_two_of_writerKindData
  379  welcomeLowerBound_two_of_writerKindDataResiduals
```

### `ProofsLean/WelcomeBoundTwo.lean`

```text
  465  welcome_not_correct_of_word_zero
  491  welcome_not_correct_of_inputIndependentLM1
  518  welcomeLowerBound_two_of_allWordsChanged
  591  welcomeLowerBound_two_of_residual
  604  welcomeLowerBound_two_iff_residual
```

### `ProofsLean/WelcomeFinalShape.lean`

```text
  806  welcomeLowerBound_two_of_dispatch
  897  welcomeLowerBound_two_of_components
```

### `ProofsLean/WelcomeL1MultiDest.lean`

```text
 1330  welcomeLowerBound_two_of_plainReadL1MultiDest
```

### `ProofsLean/WelcomeLowerBound.lean`

```text
  286  welcomeEmpty_not_correct
  314  welcomeWelcomeLine_not_correct_of_preserved
  360  welcomeWelcomeLine_zero_not_correct
  377  welcomeWelcomeLine_eight_not_correct
  393  welcomeWelcomeLine_anyBase_not_correct
  403  welcomeWelcomeLine_not_correct
  411  welcomeAtMostOneWelcome_not_correct
  424  welcomeLowerBound_one
  439  welcomeBoundTwoCertificate_rejects_every_short_line
  500  welcomeLowerBound_two_iff_rejects_short_lines
```

### `ProofsLean/WelcomeLowerBoundTwo.lean`

```text
  115  welcome_not_correct_of_step_none
  131  welcome_not_correct_of_step_frame
  195  welcomeNop_not_correct
  262  welcomeMv_not_correct
  315  welcomePe_checkFalse_not_correct
  323  welcomePe_waitPending_not_correct
  333  welcomePe_unsupported_not_correct
  345  welcomePe_notSupported_not_correct
  373  welcomePe_noforward_not_correct
  468  welcomePE_not_correct_of_not_unrefuted
  509  welcomeShortLine_not_correct
  527  welcomeLowerBound_two_of_unrefuted
  539  welcomeLowerBound_two_iff_unrefuted
```

### `ProofsLean/WelcomeOptimalFinal.lean`

```text
  159  welcomeLowerBound_two
```

### `ProofsLean/WelcomeProvenance.lean`

```text
  352  welcome_not_correct_of_doubleWrites
  371  welcomeLowerBound_two_of_residualDoubleShape
  593  welcomeLowerBound_two_of_twoShapeObligations
  710  welcomeAnswer_optimal_of_lowerBound
```

### `ProofsLean/WelcomeValueBound.lean`

```text
   94  welcome_not_correct_of_word_ne_one
  573  welcome_not_correct_of_lm1Narrow
  642  welcome_not_correct_of_doubleCopyShape
  663  welcome_not_correct_of_narrowShape
  694  welcomeLowerBound_two_of_lm1WriteShapes
  706  welcomeAnswer_optimal_of_lm1WriteShapes
```

### `ProofsLean/WelcomeWholeMachineOptimal.lean`

```text
  690  welcomeWhole_empty_not_correct
  732  welcomeWholeMachine_lowerBound_two
  865  welcomeWhole_partialLowerBound
  929  welcomeWhole_partialOptimal
```

### `ProofsLean/WelcomeWriterPackages.lean`

```text
 1162  welcomeLowerBound_two_of_plainReadL1
```

