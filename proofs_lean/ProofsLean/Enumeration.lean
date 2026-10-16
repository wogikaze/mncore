import ProofsLean.Optimality
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic

namespace ProofsLean

/-- Enumerates all line sequences of length at most `n` over an explicit line
alphabet. Coverage is relative to legality: the alphabet must contain every line
that occurs in a legal program, which is more than knowing the opcode names —
it must cover operands, masks and every legal simultaneous issue. For MN-Core,
whose line AST has Nat/String/Int/List fields and is therefore infinite, the
remaining obligation is a proof of finiteness of `legalLines` (bounded
addresses, immediates, operand ranges and legal parallel issue), NOT finiteness
of the AST type itself. -/
def programsUpTo (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap
      (fun line => (programsUpTo alphabet n).map (line :: ·))

theorem programsUpTo_complete (alphabet : List α) (n : Nat) (p : List α)
    (covered : ∀ line ∈ p, line ∈ alphabet) (length : p.length ≤ n) :
    p ∈ programsUpTo alphabet n := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest => simp at length
  | succ n ih =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest =>
      have head : line ∈ alphabet := covered line List.mem_cons_self
      have tail : rest ∈ programsUpTo alphabet n := by
        apply ih
        · intro line' mem
          exact covered line' (List.mem_cons_of_mem line mem)
        · simpa using length
      simp only [programsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨line, head, rest, tail, rfl⟩

/-- A duplicate-free finite enumeration of all lists of length at most `n`
whose elements come from `alphabet`. The finite set representation is useful
when the alphabet is obtained from a `Fintype`, and avoids materializing
duplicate programs from different recursion paths. -/
def programsUpToFinset [DecidableEq α] (alphabet : Finset α) : Nat → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] (alphabet.biUnion fun line =>
      (programsUpToFinset alphabet n).image (fun program => line :: program))

theorem programsUpToFinset_complete [DecidableEq α] (alphabet : Finset α)
    (n : Nat) (p : List α) (covered : ∀ line ∈ p, line ∈ alphabet)
    (length : p.length ≤ n) : p ∈ programsUpToFinset alphabet n := by
  induction n generalizing p with
  | zero =>
      cases p with
      | nil => simp [programsUpToFinset]
      | cons line rest => simp at length
  | succ n ih =>
      cases p with
      | nil => simp [programsUpToFinset]
      | cons line rest =>
          have head : line ∈ alphabet := covered line List.mem_cons_self
          have tail : rest ∈ programsUpToFinset alphabet n := by
            apply ih
            · intro line' mem
              exact covered line' (List.mem_cons_of_mem line mem)
            · simpa using length
          simp only [programsUpToFinset, Finset.mem_insert, Finset.mem_biUnion,
            Finset.mem_image]
          right
          refine ⟨line, head, rest, tail, ?_⟩
          rfl

/-- Finite-type specialization of `programsUpToFinset`. -/
def programsUpToFintype [Fintype α] [DecidableEq α] (n : Nat) : Finset (List α) :=
  programsUpToFinset Finset.univ n

/-- Finset of values in a finite subtype, embedded into its ambient type. This
turns a proof-bounded carrier into an alphabet accepted by
`finiteAlphabetCertificate`. -/
noncomputable def finiteSubtypeAlphabet (predicate : α → Prop)
    [Fintype {value : α // predicate value}] [DecidableEq α] : Finset α :=
  Finset.univ.image fun value : {value : α // predicate value} => value.1

theorem mem_finiteSubtypeAlphabet (predicate : α → Prop)
    [Fintype {value : α // predicate value}] [DecidableEq α] (value : α) :
    value ∈ finiteSubtypeAlphabet predicate ↔ predicate value := by
  classical
  simp [finiteSubtypeAlphabet]

theorem programsUpToFintype_complete [Fintype α] [DecidableEq α]
    (n : Nat) (p : List α) (length : p.length ≤ n) :
    p ∈ programsUpToFintype (α := α) n := by
  apply programsUpToFinset_complete
  · intro line _
    exact Finset.mem_univ line
  · exact length

def shortPrograms (m : Machine) (alphabet : List m.Line) (bound : Nat) :
    List (Program m) :=
  (programsUpTo alphabet (bound - 1)).filter (fun p => decide (score m p < bound))

/-- Lines that actually occur in at least one legal program. For machines with
an infinite line type this set may still be finite. -/
def legalLines (m : Machine) : Set m.Line := {line | ∃ p, m.legal p ∧ line ∈ p}

/-- An alphabet covers a machine when it lists every line occurring in a legal
program. Lines that can never legally issue place no obligation on enumeration. -/
def LegalLinesCovered (m : Machine) (alphabet : List m.Line) : Prop :=
  ∀ p, m.legal p → ∀ line ∈ p, line ∈ alphabet

/-- A bound-specific alphabet only needs to cover lines of legal programs
whose total score is below that bound. This matters for unbounded-cost lines
such as `nop/n`: a single finite alphabet cannot cover every possible count. -/
def LegalLinesCoveredBelow (m : Machine) (alphabet : List m.Line) (bound : Nat) : Prop :=
  ∀ p, m.legal p → score m p < bound → ∀ line ∈ p, line ∈ alphabet

theorem legalLinesCoveredBelow_of_covered {m : Machine} {alphabet : List m.Line}
    {bound : Nat} (covers : LegalLinesCovered m alphabet) :
    LegalLinesCoveredBelow m alphabet bound :=
  fun p legal _ => covers p legal

/-- A cost-bounded universe of legal lines. This is the target finite set for
MN-Core: unbounded `nop/n` lines are excluded at each fixed bound. -/
def legalLinesCostBelow (m : Machine) (bound : Nat) : Set m.Line :=
  {line | ∃ p, m.legal p ∧ line ∈ p ∧ m.lineCost line < bound}

def LegalLinesCostCovered (m : Machine) (alphabet : List m.Line) (bound : Nat) : Prop :=
  ∀ line ∈ legalLinesCostBelow m bound, line ∈ alphabet

theorem lineCost_le_score_of_mem (m : Machine) (p : Program m) (line : m.Line)
    (member : line ∈ p) : m.lineCost line ≤ score m p := by
  induction p generalizing line with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    simp only [score]
    rcases member with same | inTail
    · subst head
      omega
    · have tailBound := ih line inTail
      omega

theorem legalLinesCoveredBelow_of_costCovered {m : Machine}
    {alphabet : List m.Line} {bound : Nat}
    (covers : LegalLinesCostCovered m alphabet bound) :
    LegalLinesCoveredBelow m alphabet bound := by
  intro p legal short line member
  apply covers line
  exact ⟨p, legal, member, lt_of_le_of_lt
    (lineCost_le_score_of_mem m p line member) short⟩

theorem legalLinesCostCovered_of_finite {m : Machine} {bound : Nat}
    (finite : (legalLinesCostBelow m bound).Finite) :
    LegalLinesCostCovered m finite.toFinset.toList bound := by
  intro line member
  exact Finset.mem_toList.mpr
    (finite.mem_toFinset.mpr member)

theorem legalLinesCostBelow_finite_of_covered {m : Machine} {alphabet : List m.Line}
    {bound : Nat} (covers : LegalLinesCostCovered m alphabet bound) :
    (legalLinesCostBelow m bound).Finite := by
  apply Set.Finite.subset (List.finite_toSet alphabet)
  intro line member
  exact covers line member

theorem legalLinesCostBelow_finite_iff {m : Machine} (bound : Nat) :
    (legalLinesCostBelow m bound).Finite ↔
      ∃ alphabet : List m.Line, LegalLinesCostCovered m alphabet bound := by
  constructor
  · intro finite
    exact ⟨finite.toFinset.toList, legalLinesCostCovered_of_finite finite⟩
  · rintro ⟨alphabet, covers⟩
    exact legalLinesCostBelow_finite_of_covered covers

theorem shortPrograms_complete {m : Machine} {alphabet : List m.Line} {bound : Nat}
    (covers : LegalLinesCoveredBelow m alphabet bound) (p : Program m) (legal : m.legal p)
    (short : score m p < bound) : p ∈ shortPrograms m alphabet bound := by
  have member := programsUpTo_complete alphabet (bound - 1) p (covers p legal short) (by
    have length := length_le_score m p
    omega)
  simp [shortPrograms, List.mem_filter, member, short]

def enumerationCertificate (m : Machine) (spec : Problem m) (alphabet : List m.Line)
    (bound : Nat) (covers : LegalLinesCoveredBelow m alphabet bound)
    (rejected : ∀ p ∈ shortPrograms m alphabet bound, ¬ Correct m spec p) :
    BoundCertificate m spec bound where
  candidates := shortPrograms m alphabet bound
  complete := fun p legal short => shortPrograms_complete covers p legal short
  rejected := rejected

theorem legalLinesCovered_of_total {m : Machine} {alphabet : List m.Line}
    (covers : ∀ line : m.Line, line ∈ alphabet) : LegalLinesCovered m alphabet :=
  fun _ _ line _ => covers line

theorem legalLinesCovered_univ {m : Machine} [Fintype m.Line] :
    LegalLinesCovered m Finset.univ.toList :=
  legalLinesCovered_of_total
    (fun line => Finset.mem_toList.mpr (Finset.mem_univ line))

theorem legalLinesCovered_of_finite {m : Machine} (h : (legalLines m).Finite) :
    LegalLinesCovered m h.toFinset.toList := by
  intro p legal line mem
  exact Finset.mem_toList.mpr (h.mem_toFinset.mpr ⟨p, legal, mem⟩)

theorem legalLines_finite_of_covered {m : Machine} {alphabet : List m.Line}
    (h : LegalLinesCovered m alphabet) : (legalLines m).Finite :=
  Set.Finite.subset (List.finite_toSet alphabet)
    (fun _ ⟨p, legal, mem⟩ => h p legal _ mem)

theorem legalLines_finite_iff {m : Machine} :
    (legalLines m).Finite ↔ ∃ alphabet, LegalLinesCovered m alphabet :=
  ⟨fun h => ⟨h.toFinset.toList, legalLinesCovered_of_finite h⟩,
    fun ⟨_, h⟩ => legalLines_finite_of_covered h⟩

/-- Score-bounded programs over a finite alphabet, represented as a `Finset`.
The alphabet may be the image of a `Fintype` subtype of an otherwise infinite
machine line type. -/
noncomputable def shortProgramsFinset (m : Machine) (alphabet : Finset m.Line)
    (bound : Nat) : Finset (Program m) := by
  classical
  exact (programsUpToFinset alphabet (bound - 1)).filter
    (fun p => decide (score m p < bound))

theorem shortProgramsFinset_complete (m : Machine) (alphabet : Finset m.Line)
    (bound : Nat) (covers : ∀ p, m.legal p → score m p < bound →
      ∀ line ∈ p, line ∈ alphabet) (p : Program m) (legal : m.legal p)
    (short : score m p < bound) : p ∈ shortProgramsFinset m alphabet bound := by
  classical
  have length : p.length ≤ bound - 1 := by
    have scoreLength := length_le_score m p
    omega
  have enumerated : p ∈ programsUpToFinset alphabet (bound - 1) :=
    programsUpToFinset_complete alphabet (bound - 1) p (covers p legal short) length
  unfold shortProgramsFinset
  exact Finset.mem_filter.mpr ⟨enumerated, by simpa using short⟩

/-- A finite alphabet certificate suitable for MN-Core's bound-specific
finite carriers. -/
noncomputable def finiteAlphabetCertificate (m : Machine) (spec : Problem m)
    (alphabet : Finset m.Line) (bound : Nat)
    (covers : ∀ p, m.legal p → score m p < bound →
      ∀ line ∈ p, line ∈ alphabet)
    (rejected : ∀ p ∈ shortProgramsFinset m alphabet bound,
      ¬ Correct m spec p) : BoundCertificate m spec bound := by
  classical
  refine ⟨(shortProgramsFinset m alphabet bound).toList, ?_, ?_⟩
  · intro p legal short
    exact Finset.mem_toList.mpr
      (shortProgramsFinset_complete m alphabet bound covers p legal short)
  · intro p member
    apply rejected p
    exact Finset.mem_toList.mp member

/-- Fintype convenience: when the line type itself is finite, no separate
coverage argument is needed. -/
noncomputable def shortProgramsFintype (m : Machine) [Fintype m.Line] (bound : Nat) :
    List (Program m) := by
  classical
  exact ((programsUpToFintype (α := m.Line) (bound - 1)).filter
    (fun p => decide (score m p < bound))).toList

theorem shortProgramsFintype_complete (m : Machine) [Fintype m.Line]
    (bound : Nat) (p : Program m) (_legal : m.legal p) (short : score m p < bound) :
    p ∈ shortProgramsFintype m bound := by
  classical
  have length : p.length ≤ bound - 1 := by
    have scoreLength := length_le_score m p
    omega
  have enumerated : p ∈ programsUpToFintype (α := m.Line) (bound - 1) :=
    programsUpToFintype_complete (bound - 1) p length
  unfold shortProgramsFintype
  apply Finset.mem_toList.mpr
  exact Finset.mem_filter.mpr ⟨enumerated, by simpa using short⟩

noncomputable def fintypeCertificate (m : Machine) [Fintype m.Line]
    (spec : Problem m) (bound : Nat)
    (rejected : ∀ p ∈ shortProgramsFinset m Finset.univ bound,
      ¬ Correct m spec p) :
    BoundCertificate m spec bound :=
  finiteAlphabetCertificate m spec Finset.univ bound
    (fun _ _ _ line _ => Finset.mem_univ line) rejected

end ProofsLean
