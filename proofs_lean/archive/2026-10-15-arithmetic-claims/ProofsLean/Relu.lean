import ProofsLean.LowerBound

/-- 1ステップ(1行)あたりの MAU 上限: 4サイクル x 2 Float = 8 -/
def floatsPerStepMAU : Nat := 4 * 2

theorem floatsPerStepMAU_eq : floatsPerStepMAU = 8 := rfl

/-- 1行に含められる MAU 式は最大 1 (3.6.4 グループ排他) -/
def maxMAUPerStep : Nat := 1

/-- 必要 MAU 発行回数: 天井割り算 -/
def mauIssuesNeeded (elems : Nat) : Nat :=
  (elems + floatsPerStepMAU - 1) / floatsPerStepMAU

/-- 行数下限: MAU 発行回数 (1行1発行のため) -/
def mauLineLowerBound (elems : Nat) : Nat :=
  mauIssuesNeeded elems / maxMAUPerStep

/-- ReLU 系の出力要素数: 16 Float -/
def reluElems : Nat := 16

/-- 現1位行数 Top: 3.relu = 2, 4.relu-grad = 3 -/
def reluTop : Nat := 2
def reluGradTop : Nat := 3

/-- relu-grad の定数 1.0f 準備コスト: `imm ... $t` 1行 -/
def reluGradConstLines : Nat := 1

/-- relu-grad 下限 = MAU下限 2 + 定数1 = 3 -/
def reluGradLower : Nat :=
  mauLineLowerBound reluElems + reluGradConstLines

theorem relu_mau_needed : mauIssuesNeeded reluElems = 2 := rfl

theorem relu_lower : mauLineLowerBound reluElems = 2 := rfl

theorem relu_optimal : mauLineLowerBound reluElems = reluTop := rfl

theorem relu_no_one_line :
    ∀ lines : Nat, lines < reluTop → lines < mauLineLowerBound reluElems := by
  intro lines h
  have h2 : mauLineLowerBound reluElems = 2 := rfl
  simp [reluTop] at h
  omega

theorem reluGrad_mau_lower : mauLineLowerBound reluElems = 2 := rfl

theorem reluGrad_lower : reluGradLower = 3 := rfl

theorem reluGrad_optimal : reluGradLower = reluGradTop := rfl

theorem reluGrad_no_two_lines :
    ∀ lines : Nat, lines < reluGradTop → lines < reluGradLower := by
  intro lines h
  have h3 : reluGradLower = 3 := rfl
  simp [reluGradTop] at h
  omega
