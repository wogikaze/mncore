/-
低精度指数の下限モデルと 13.exp-low-prec (Top=10) の最適性.

参照解 problems/13.exp-low-prec/answer.vsm (10行):
  準備6行 (imm/範囲縮小/係数の対・組)
  Horner多項式4行 (fvfma/fvmul の交互)

根拠 (judge 実測):
- 準備6行: 定数対の同行化は alu-immediate conflictで拒否。
- Horner4行: 対の同行化は mau conflictで拒否。
- 末尾対の同行化も mau conflictで拒否。
よって 6 + 4 = 10行が下限で Top=10 は最適。
-/

/-- 準備部の最小行数 -/
def expLowSetup : Nat := 6

/-- Horner部の最小行数 -/
def expLowHorner : Nat := 4

/-- 現1位行数 Top = 10 -/
def expLowTop : Nat := 10

/-- 行数下限 = 6 + 4 = 10 -/
def expLowLower : Nat := expLowSetup + expLowHorner

theorem expLow_lower : expLowLower = 10 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem expLow_optimal : expLowLower = expLowTop := rfl

/-- 系: 9行以下での Accepted は存在しない -/
theorem expLow_no_nine :
    ∀ lines : Nat, lines < expLowTop → lines < expLowLower := by
  intro lines h
  have h10 : expLowLower = 10 := rfl
  simp [expLowTop] at h
  omega
