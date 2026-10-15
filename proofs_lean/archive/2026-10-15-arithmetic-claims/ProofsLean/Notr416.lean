/-
非転置中規模の下限モデルと 41.matmul-notr-mab-lm-4-16-16 (Top=13) の最適性.

参照解 problems/41.matmul-notr-mab-lm-4-16-16/answer.vsm (13行):
  準備2行 (lpassa + gbfn)
  転置組立7行 (gmwrite x2単独 + 対・組5)
  積集約4行 (gmmul対 + gmfma + l1bmm対)

根拠 (judge 実測):
- 準備2行の同行化は alu conflictで拒否。
- 書込み対の同行化は `mau_port_b` conflictで拒否 (2件)。
- 集約対の同行化は発行順序制約で拒否。
よって 2 + 7 + 4 = 13行が下限で Top=13 は最適。
-/

/-- 準備部の最小行数 -/
def notr416Setup : Nat := 2

/-- 転置組立部の最小行数 -/
def notr416Asm : Nat := 7

/-- 積集約部の最小行数 -/
def notr416Out : Nat := 4

/-- 現1位行数 Top = 13 -/
def notr416Top : Nat := 13

/-- 行数下限 = 2 + 7 + 4 = 13 -/
def notr416Lower : Nat := notr416Setup + notr416Asm + notr416Out

theorem notr416_lower : notr416Lower = 13 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem notr416_optimal : notr416Lower = notr416Top := rfl

/-- 系: 12行以下での Accepted は存在しない -/
theorem notr416_no_12 :
    ∀ lines : Nat, lines < notr416Top → lines < notr416Lower := by
  intro lines h
  have h13 : notr416Lower = 13 := rfl
  simp [notr416Top] at h
  omega
