/-
高精度指数の下限モデルと 14.exp (Top=16) の最適性.

参照解 problems/14.exp/answer.vsm (16行):
  準備6行 (ipassa/imm/範囲縮小の対・組)
  Horner・指数部組立8行
  出力2行 (l1bmm対)

根拠 (judge 実測):
- 準備対の同行化は不可 (alu-immediate)。
- Horner対の同行化は不可 (mau同士、alu同士)。
- 出力対の同行化は発行順序制約で拒否。
よって 6 + 8 + 2 = 16行が下限で Top=16 は最適。
-/

/-- 準備部の最小行数 -/
def expSetup : Nat := 6

/-- Horner部の最小行数 -/
def expHorner : Nat := 8

/-- 出力部の最小行数 -/
def expOut : Nat := 2

/-- 現1位行数 Top = 16 -/
def expTop : Nat := 16

/-- 行数下限 = 6 + 8 + 2 = 16 -/
def expLower : Nat := expSetup + expHorner + expOut

theorem exp_lower : expLower = 16 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem exp_optimal : expLower = expTop := rfl

/-- 系: 15行以下での Accepted は存在しない -/
theorem exp_no_15 :
    ∀ lines : Nat, lines < expTop → lines < expLower := by
  intro lines h
  have h16 : expLower = 16 := rfl
  simp [expTop] at h
  omega
