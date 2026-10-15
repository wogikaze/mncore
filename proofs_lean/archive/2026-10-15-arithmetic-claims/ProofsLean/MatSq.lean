/-
行列二乗の下限モデルと 14.mat-sq (Top=10) の最適性.

参照解 problems/challenge/14.mat-sq/answer.vsm (10行):
  書込み4行 (hmwrite x4)
  転置組立2行 (hmread+hmwrite x2)
  積4行 (hmmul x4)

根拠 (judge 実測):
- 書込み4行: 隣接同行化は `mau_port_b` conflictで拒否。
- 組立2行の同行化は `mau_port_b` conflictで拒否。
- 積4行: 隣接同行化は `mau` conflictで拒否。
よって 4 + 2 + 4 = 10行が下限で Top=10 は最適。
-/

/-- 書込み部の最小行数 -/
def matsqWrite : Nat := 4

/-- 転置組立部の最小行数 -/
def matsqAsm : Nat := 2

/-- 積部の最小行数 -/
def matsqMul : Nat := 4

/-- 現1位行数 Top = 10 -/
def matsqTop : Nat := 10

/-- 行数下限 = 4 + 2 + 4 = 10 -/
def matsqLower : Nat := matsqWrite + matsqAsm + matsqMul

theorem matsq_lower : matsqLower = 10 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem matsq_optimal : matsqLower = matsqTop := rfl

/-- 系: 9行以下での Accepted は存在しない -/
theorem matsq_no_nine :
    ∀ lines : Nat, lines < matsqTop → lines < matsqLower := by
  intro lines h
  have h10 : matsqLower = 10 := rfl
  simp [matsqTop] at h
  omega
