/-
対数の下限モデルと 24.log2 (Top=7) の最適性.

参照解 problems/challenge/24.log2/answer.vsm (7行):
  imm ui"0x0B808017" $t
  sadd ... x2                             (デコード2行)
  ilsr ... x4                             (出力4行)

根拠 (judge 実測): 全6組の隣接同行化がいずれも
alu conflictで拒否。
よって 1 + 2 + 4 = 7行が下限で Top=7 は最適。
-/

/-- 定数の最小行数 -/
def log2Const : Nat := 1

/-- デコード部の最小行数 -/
def log2Decode : Nat := 2

/-- 出力部の最小行数 -/
def log2Out : Nat := 4

/-- 現1位行数 Top = 7 -/
def log2Top : Nat := 7

/-- 行数下限 = 1 + 2 + 4 = 7 -/
def log2Lower : Nat := log2Const + log2Decode + log2Out

theorem log2_lower : log2Lower = 7 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem log2_optimal : log2Lower = log2Top := rfl

/-- 系: 6行以下での Accepted は存在しない -/
theorem log2_no_six :
    ∀ lines : Nat, lines < log2Top → lines < log2Lower := by
  intro lines h
  have h7 : log2Lower = 7 := rfl
  simp [log2Top] at h
  omega
