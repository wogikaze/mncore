import ProofsLean.Enumeration
import ProofsLean.IntegerALU
import ProofsLean.PEMemory

/- A source-level model of the two long-word `iinc` lines in Welcome.
This model deliberately has only these two lines.  Its optimality theorem is
therefore restricted; it is not a claim about all legal MN-Core programs. -/
namespace ProofsLean.MNCore.PlusOne

abbrev Words := Fin 16 → BitVec 32

structure State where
  lm0 : Words
  lm1 : Words

abbrev Line := Fin 2

/-- `$lm0v` or `$lm8v` / `$ln0v` or `$ln8v`: four long-word accesses. -/
def schedule (line : Line) : PEMemory.Schedule :=
  .auto (8 * line.val) 2

theorem schedule_well_formed (line : Line) (bank : PEMemory.Bank)
    (hbank : bank = .lm0 ∨ bank = .lm1) :
    (schedule line).WellFormed bank .long := by
  rcases hbank with rfl | rfl
  all_goals simp [schedule, PEMemory.Schedule.WellFormed, PEMemory.Bank.capacity,
    PEMemory.Width.words]; omega

theorem address_at (line : Line) (bank : PEMemory.Bank)
    (hbank : bank = .lm0 ∨ bank = .lm1) (cycle : Fin 4) :
    (PEMemory.address bank .long (schedule line) 0 .direct 0 cycle).val =
      8 * line.val + 2 * cycle.val := by
  rcases hbank with rfl | rfl
  all_goals simp [PEMemory.address, PEMemory.count, PEMemory.baseOffset,
    PEMemory.Schedule.at, PEMemory.Adjustment.offset, schedule,
    PEMemory.Bank.capacity, PEMemory.Width.words]
  all_goals have hline := line.isLt
  all_goals have hcycle := cycle.isLt
  all_goals omega

def increment (x : BitVec 32) : BitVec 32 :=
  (IntegerALU.evaluateLane (.arith .inc false) x 0).value

theorem increment_eq_add_one (x : BitVec 32) : increment x = x + 1 := rfl

theorem increment_numerical (x : BitVec 32) (bounded : x.toNat ≤ 50) :
    (increment x).toNat = x.toNat + 1 := by
  rw [increment_eq_add_one, BitVec.toNat_add]
  have below : x.toNat + 1 < 2 ^ 32 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]

def incrementPair (high low : BitVec 32) : BitVec 64 :=
  (IntegerALU.evaluateBus .word (.arith .inc false)
    ⟨high ++ low, 0⟩ ⟨0, 0⟩ false).value.high

theorem increment_pair_spec (high low : BitVec 32) :
    incrementPair high low = increment high ++ increment low := by
  simp [incrementPair, IntegerALU.evaluateBus, IntegerALU.lane,
    IntegerALU.Precision.lanes, IntegerALU.Precision.width,
    IntegerALU.evaluateLane, IntegerALU.arithmetic, increment,
    List.range, List.range.loop]
  rw [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
  change (low + 1#32).setWidth 64 ||| ((high + 1#32).setWidth 64 <<< 32) =
    (high + 1#32) ++ (low + 1#32)
  calc
    _ = ((high + 1#32).setWidth 64 <<< 32) ||| (low + 1#32).setWidth 64 :=
      BitVec.or_comm _ _
    _ = ((high + 1#32) ++ (low + 1#32)).setWidth 64 :=
      (BitVec.setWidth_append_eq_shiftLeft_setWidth_or).symm
    _ = _ := by simp

def highAddress (address : Fin 16) : Fin 16 :=
  ⟨2 * (address.val / 2), by have := address.isLt; omega⟩

def lowAddress (address : Fin 16) : Fin 16 :=
  ⟨2 * (address.val / 2) + 1, by have := address.isLt; omega⟩

def busWord (state : State) (address : Fin 16) : BitVec 32 :=
  let result := incrementPair (state.lm0 (highAddress address))
    (state.lm0 (lowAddress address))
  if address.val % 2 = 0 then result.extractLsb' 32 32
  else result.extractLsb' 0 32

theorem bus_word_eq_increment (state : State) (address : Fin 16) :
    busWord state address = increment (state.lm0 address) := by
  by_cases even : address.val % 2 = 0
  · have same : highAddress address = address := by
      apply Fin.ext
      simp [highAddress]
      omega
    simp [busWord, even, increment_pair_spec, same]
    exact BitVec.extractLsb'_append_eq_left
  · have same : lowAddress address = address := by
      apply Fin.ext
      simp [lowAddress]
      omega
    simp [busWord, even, increment_pair_spec, same]
    exact BitVec.extractLsb'_append_eq_right

def cycleHigh (line : Line) (cycle : Fin 4) : Fin 16 :=
  ⟨8 * line.val + 2 * cycle.val, by
    have hl := line.isLt
    have hc := cycle.isLt
    omega⟩

def cycleLow (line : Line) (cycle : Fin 4) : Fin 16 :=
  ⟨8 * line.val + 2 * cycle.val + 1, by
    have hl := line.isLt
    have hc := cycle.isLt
    omega⟩

theorem cycle_high_address (line : Line) (cycle : Fin 4) :
    (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle).val =
      (cycleHigh line cycle).val := by
  simpa [cycleHigh] using address_at line .lm0 (Or.inl rfl) cycle

def sourceMemory (state : State) : PEMemory.Memory .lm0 := fun address =>
  if h : address.val < 16 then state.lm0 ⟨address.val, h⟩ else 0

theorem cycle_read_high (state : State) (line : Line) (cycle : Fin 4) :
    PEMemory.readWords .lm0 .long (sourceMemory state)
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 0 =
      state.lm0 (cycleHigh line cycle) := by
  change sourceMemory state
    (PEMemory.advance .lm0
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 0) = _
  have same : PEMemory.advance .lm0
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 0 =
      ⟨(cycleHigh line cycle).val, Nat.lt_trans (cycleHigh line cycle).isLt (by decide)⟩ := by
    apply Fin.ext
    change ((PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle).val + 0) %
      4096 = (cycleHigh line cycle).val
    rw [cycle_high_address]
    have h := (cycleHigh line cycle).isLt
    omega
  rw [same]
  simp [sourceMemory]

theorem cycle_read_low (state : State) (line : Line) (cycle : Fin 4) :
    PEMemory.readWords .lm0 .long (sourceMemory state)
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 1 =
      state.lm0 (cycleLow line cycle) := by
  change sourceMemory state
    (PEMemory.advance .lm0
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 1) = _
  have same : PEMemory.advance .lm0
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 1 =
      ⟨(cycleLow line cycle).val, Nat.lt_trans (cycleLow line cycle).isLt (by decide)⟩ := by
    apply Fin.ext
    change ((PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle).val + 1) %
      4096 = (cycleLow line cycle).val
    rw [cycle_high_address]
    have h := (cycleLow line cycle).isLt
    simp only [cycleHigh, cycleLow, Fin.val_mk] at *
    omega
  rw [same]
  simp [sourceMemory]

def cycleInput (state : State) (line : Line) (cycle : Fin 4) : IntegerALU.Bus :=
  PEMemory.pack (PEMemory.readWords .lm0 .long (sourceMemory state)
    (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle))

theorem cycle_input_high (state : State) (line : Line) (cycle : Fin 4) :
    (cycleInput state line cycle).high =
      state.lm0 (cycleHigh line cycle) ++ state.lm0 (cycleLow line cycle) := by
  change PEMemory.readWords .lm0 .long (sourceMemory state)
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 0 ++
    PEMemory.readWords .lm0 .long (sourceMemory state)
      (PEMemory.address .lm0 .long (schedule line) 0 .direct 0 cycle) 1 =
    state.lm0 (cycleHigh line cycle) ++ state.lm0 (cycleLow line cycle)
  congr 1
  · exact cycle_read_high state line cycle
  · exact cycle_read_low state line cycle

theorem cycle_pair_bus (state : State) (line : Line) (cycle : Fin 4) :
    incrementPair (state.lm0 (cycleHigh line cycle))
      (state.lm0 (cycleLow line cycle)) =
      busWord state (cycleHigh line cycle) ++ busWord state (cycleLow line cycle) := by
  rw [increment_pair_spec, bus_word_eq_increment, bus_word_eq_increment]

theorem cycle_alu_output (state : State) (line : Line) (cycle : Fin 4) :
    (IntegerALU.evaluateBus .word (.arith .inc false)
      ⟨(cycleInput state line cycle).high, 0⟩ ⟨0, 0⟩ false).value.high =
      busWord state (cycleHigh line cycle) ++ busWord state (cycleLow line cycle) := by
  rw [cycle_input_high]
  exact cycle_pair_bus state line cycle

def cycleOutput (state : State) (line : Line) (cycle : Fin 4) : BitVec 64 :=
  (IntegerALU.evaluateBus .word (.arith .inc false)
    ⟨(cycleInput state line cycle).high, 0⟩ ⟨0, 0⟩ false).value.high

theorem cycle_output_high (state : State) (line : Line) (cycle : Fin 4) :
    (cycleOutput state line cycle).extractLsb' 32 32 =
      busWord state (cycleHigh line cycle) := by
  change BitVec.extractLsb' 32 32
    (IntegerALU.evaluateBus .word (.arith .inc false)
      ⟨(cycleInput state line cycle).high, 0⟩ ⟨0, 0⟩ false).value.high = _
  rw [cycle_alu_output]
  exact BitVec.extractLsb'_append_eq_left

theorem cycle_output_low (state : State) (line : Line) (cycle : Fin 4) :
    (cycleOutput state line cycle).extractLsb' 0 32 =
      busWord state (cycleLow line cycle) := by
  change BitVec.extractLsb' 0 32
    (IntegerALU.evaluateBus .word (.arith .inc false)
      ⟨(cycleInput state line cycle).high, 0⟩ ⟨0, 0⟩ false).value.high = _
  rw [cycle_alu_output]
  exact BitVec.extractLsb'_append_eq_right

/-- One long-word line handles four cycles, with two 32-bit lanes per cycle. -/
def step (line : Line) (state : State) : State :=
  { state with lm1 := fun address =>
      if address.val / 8 = line.val then busWord state address
      else state.lm1 address }

theorem step_writes_cycle_output_high (line : Line) (state : State) (cycle : Fin 4) :
    (step line state).lm1 (cycleHigh line cycle) =
      (cycleOutput state line cycle).extractLsb' 32 32 := by
  have inLine : (cycleHigh line cycle).val / 8 = line.val := by
    simp [cycleHigh]
    have hl := line.isLt
    have hc := cycle.isLt
    omega
  simp [step, inLine]
  exact (cycle_output_high state line cycle).symm

theorem step_writes_cycle_output_low (line : Line) (state : State) (cycle : Fin 4) :
    (step line state).lm1 (cycleLow line cycle) =
      (cycleOutput state line cycle).extractLsb' 0 32 := by
  have inLine : (cycleLow line cycle).val / 8 = line.val := by
    simp [cycleLow]
    have hl := line.isLt
    have hc := cycle.isLt
    omega
  simp [step, inLine]
  exact (cycle_output_low state line cycle).symm

def machine : Machine where
  Line := Line
  State := State
  Input := Words
  step := fun line state => some (step line state)
  legal := fun _ => True
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

def problem : Problem machine where
  admissible := fun input => ∀ i, (input i).toNat ≤ 50
  initial := fun input => ⟨input, fun _ => 0⟩
  post := fun input state => ∀ i, (state.lm1 i).toNat = (input i).toNat + 1

def answer : Program machine := [⟨0, by decide⟩, ⟨1, by decide⟩]

theorem answer_correct : Correct machine problem answer := by
  refine ⟨True.intro, ?_⟩
  intro input admissible
  refine ⟨step 1 (step 0 ⟨input, fun _ => 0⟩), rfl, ?_⟩
  intro i
  have hi := i.isLt
  by_cases h : i.val / 8 = 1
  · simpa [step, h, bus_word_eq_increment] using increment_numerical (input i) (admissible i)
  · have h0 : i.val / 8 = 0 := by omega
    have hlt : i.val < 8 := by omega
    simpa [step, h0, hlt, bus_word_eq_increment] using increment_numerical (input i) (admissible i)

def zeroInput : Words := fun _ => 0

theorem zero_admissible : problem.admissible zeroInput := by
  intro i
  simp [zeroInput]

theorem empty_incorrect : ¬ Correct machine problem [] := by
  intro h
  obtain ⟨result, run, post⟩ := h.2 zeroInput zero_admissible
  have eq : result = problem.initial zeroInput := by
    exact Option.some.inj (by simpa [execute] using run.symm)
  subst result
  have wrong := post (⟨0, by decide⟩ : Fin 16)
  simp [problem, zeroInput] at wrong

theorem one_line_incorrect (line : Line) : ¬ Correct machine problem [line] := by
  intro h
  obtain ⟨result, run, post⟩ := h.2 zeroInput zero_admissible
  have eq : result = step line (problem.initial zeroInput) := by
    exact Option.some.inj (by simpa [execute, machine] using run.symm)
  subst result
  have cases : line.val = 0 ∨ line.val = 1 := by omega
  rcases cases with h0 | h1
  · have wrong := post (⟨8, by decide⟩ : Fin 16)
    simp [problem, step, zeroInput, h0] at wrong
  · have wrong := post (⟨0, by decide⟩ : Fin 16)
    simp [problem, step, zeroInput, h1] at wrong

theorem score_eq_length (p : Program machine) : score machine p = p.length := by
  induction p with
  | nil => rfl
  | cons line rest ih =>
    simp only [score, List.length_cons]
    change 1 + score machine rest = rest.length + 1
    omega

theorem two_line_lower_bound : LowerBound machine problem 2 := by
  intro p correct
  by_cases enough : 2 ≤ score machine p
  · exact enough
  have short : score machine p < 2 := by omega
  have hlen : p.length < 2 := by
    rw [score_eq_length] at short
    omega
  cases p with
  | nil => exact False.elim (empty_incorrect correct)
  | cons line rest =>
    cases rest with
    | nil => exact False.elim (one_line_incorrect line correct)
    | cons next tail =>
      simp only [List.length_cons] at hlen
      omega

theorem answer_optimal_in_restricted_model : Optimal machine problem answer := by
  have answer_score : score machine answer = 2 := by decide
  exact ⟨answer_correct, by rw [answer_score]; exact two_line_lower_bound⟩

end ProofsLean.MNCore.PlusOne
