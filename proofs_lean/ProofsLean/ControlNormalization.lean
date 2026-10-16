import ProofsLean.Semantics

/- Source control directives have no scored instruction word.  They update a
control context used by later atomic instruction words, while the issue step
owns all data and forwarding state.  A multiword source construct such as
`nop/n` must first be expanded into atomic issue entries.  This construction
shows how to retain their effects
when enumerating positive-cost issue lines.  An actual VSM connection still
has to prove that each zero-cost directive fits this interface. -/
namespace ProofsLean.ControlNormalization

inductive Statement (Directive Line : Type) where
  | directive (value : Directive)
  | issue (line : Line)

def compile (update : Directive → Control → Control) :
    List (Statement Directive Line) → Control → List (Control × Line)
  | [], _ => []
  | .directive d :: rest, control => compile update rest (update d control)
  | .issue line :: rest, control => (control, line) :: compile update rest control

def runSource (update : Directive → Control → Control)
    (step : Control → Line → State → Option State) :
    List (Statement Directive Line) → Control → State → Option State
  | [], _, state => some state
  | .directive d :: rest, control, state =>
      runSource update step rest (update d control) state
  | .issue line :: rest, control, state =>
      (step control line state).bind (runSource update step rest control)

def runCompiled (step : Control → Line → State → Option State) :
    List (Control × Line) → State → Option State
  | [], state => some state
  | (control, line) :: rest, state =>
      (step control line state).bind (runCompiled step rest)

def cost : List (Statement Directive Line) → Nat
  | [] => 0
  | .directive _ :: rest => cost rest
  | .issue _ :: rest => 1 + cost rest

theorem compile_length (update : Directive → Control → Control)
    (source : List (Statement Directive Line)) (control : Control) :
    (compile update source control).length = cost source := by
  induction source generalizing control with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | directive d => simpa [compile, cost] using ih (update d control)
    | issue line => simp [compile, cost, ih control, Nat.add_comm]

theorem run_compiles (update : Directive → Control → Control)
    (step : Control → Line → State → Option State)
    (source : List (Statement Directive Line)) (control : Control) (state : State) :
    runSource update step source control state =
      runCompiled step (compile update source control) state := by
  induction source generalizing control state with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | directive d => simpa [runSource, compile] using ih (update d control) state
    | issue line =>
      simp only [runSource, compile, runCompiled]
      cases h : step control line state with
      | none => simp
      | some next => simpa [h] using ih control next

/-- Variant used when each scored issue word advances the control clock as well
as applying zero-cost directive updates. -/
def compileAdvancing (update : Directive → Control → Control)
    (advance : Control → Line → Control) :
    List (Statement Directive Line) → Control → List (Control × Line)
  | [], _ => []
  | .directive d :: rest, control =>
      compileAdvancing update advance rest (update d control)
  | .issue line :: rest, control =>
      (control, line) :: compileAdvancing update advance rest (advance control line)

def runSourceAdvancing (update : Directive → Control → Control)
    (advance : Control → Line → Control)
    (step : Control → Line → State → Option State) :
    List (Statement Directive Line) → Control → State → Option State
  | [], _, state => some state
  | .directive d :: rest, control, state =>
      runSourceAdvancing update advance step rest (update d control) state
  | .issue line :: rest, control, state =>
      (step control line state).bind
        (runSourceAdvancing update advance step rest (advance control line))

theorem compileAdvancing_length (update : Directive → Control → Control)
    (advance : Control → Line → Control)
    (source : List (Statement Directive Line)) (control : Control) :
    (compileAdvancing update advance source control).length = cost source := by
  induction source generalizing control with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | directive d => simpa [compileAdvancing, cost] using ih (update d control)
      | issue line =>
          simp [compileAdvancing, cost, ih (advance control line)]
          omega

theorem run_compiles_advancing (update : Directive → Control → Control)
    (advance : Control → Line → Control)
    (step : Control → Line → State → Option State)
    (source : List (Statement Directive Line)) (control : Control) (state : State) :
    runSourceAdvancing update advance step source control state =
      runCompiled step (compileAdvancing update advance source control) state := by
  induction source generalizing control state with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | directive d =>
          simpa [runSourceAdvancing, compileAdvancing] using ih (update d control) state
      | issue line =>
          simp only [runSourceAdvancing, compileAdvancing, runCompiled]
          cases h : step control line state with
          | none => simp
          | some next =>
              simpa [h] using ih (advance control line) next

/-- The normalized lines use the ordinary positive-cost proof interface. -/
def normalizedMachine (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type) : Machine where
  Line := Control × Line
  State := State
  Input := Input
  step := fun pair state => step pair.1 pair.2 state
  legal := legal
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

theorem compiled_execution (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type)
    (lines : List (Control × Line)) (state : State) :
    runCompiled step lines state =
      execute (normalizedMachine step legal Input) lines state := by
  induction lines generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    cases pair with
    | mk control line =>
      simp only [runCompiled, execute, normalizedMachine]
      cases h : step control line state with
      | none => simp
      | some next => simpa [h, normalizedMachine] using ih next

theorem source_execution_advancing (update : Directive → Control → Control)
    (advance : Control → Line → Control)
    (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type)
    (source : List (Statement Directive Line)) (control : Control) (state : State) :
    runSourceAdvancing update advance step source control state =
      execute (normalizedMachine step legal Input)
        (compileAdvancing update advance source control) state := by
  rw [run_compiles_advancing, compiled_execution]

theorem source_score_advancing (update : Directive → Control → Control)
    (advance : Control → Line → Control)
    (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type)
    (source : List (Statement Directive Line)) (control : Control) :
    score (normalizedMachine step legal Input)
      (compileAdvancing update advance source control) = cost source := by
  have length := compileAdvancing_length update advance source control
  suffices score (normalizedMachine step legal Input)
      (compileAdvancing update advance source control) =
        (compileAdvancing update advance source control).length by omega
  induction compileAdvancing update advance source control with
  | nil => rfl
  | cons pair rest ih =>
      simp only [score, List.length_cons]
      change 1 + score (normalizedMachine step legal Input) rest = rest.length + 1
      omega


theorem source_execution (update : Directive → Control → Control)
    (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type)
    (source : List (Statement Directive Line)) (control : Control) (state : State) :
    runSource update step source control state =
      execute (normalizedMachine step legal Input) (compile update source control) state := by
  rw [run_compiles, compiled_execution]

theorem source_score (update : Directive → Control → Control)
    (step : Control → Line → State → Option State)
    (legal : List (Control × Line) → Prop) (Input : Type)
    (source : List (Statement Directive Line)) (control : Control) :
    score (normalizedMachine step legal Input) (compile update source control) =
      cost source := by
  have length := compile_length update source control
  suffices score (normalizedMachine step legal Input) (compile update source control) =
      (compile update source control).length by omega
  induction compile update source control with
  | nil => rfl
  | cons pair rest ih =>
    simp only [score, List.length_cons]
    change 1 + score (normalizedMachine step legal Input) rest = rest.length + 1
    omega

end ProofsLean.ControlNormalization
