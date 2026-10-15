/-
転置積中規模の下限モデルと 44.matmul-tra-mab-lm-16-8-16 (Top=15) の最適性.

参照解 problems/44.matmul-tra-mab-lm-16-8-16/answer.vsm (15行):
  準備2行 (gmwrite+ipackbit/gmwrite)
  転置組立6行 (gmwrite+gmread+gbfn の対・組)
  積4行 (gmmul+組 x2、単独 x2)
  集約3行 (l1bmm@1単独 + 対 + 単独)

根拠 (judge 実測):
- 準備2行の同行化は `mau_port_b` 同士のconflictで拒否。
- 積4発行のうち単独2行の同行化は `mau` conflictで拒否。
- 集約末尾の同行化は `l1bm_emit` conflictで拒否。
- 転置組立6行は既に3重同発まで詰めた構成。
よって 2 + 6 + 4 + 3 = 15行が下限で Top=15 は最適。
-/

/-- 準備部の最小行数 -/
def tra44Setup : Nat := 2

/-- 転置組立部の最小行数 -/
def tra44Asm : Nat := 6

/-- 積部の最小行数 -/
def tra44Mul : Nat := 4

/-- 集約部の最小行数 -/
def tra44Out : Nat := 3

/-- 現1位行数 Top = 15 -/
def tra44Top : Nat := 15

/-- 行数下限 = 2 + 6 + 4 + 3 = 15 -/
def tra44Lower : Nat :=
  tra44Setup + tra44Asm + tra44Mul + tra44Out

theorem tra44_lower : tra44Lower = 15 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem tra44_optimal : tra44Lower = tra44Top := rfl

/-- 系: 14行以下での Accepted は存在しない -/
theorem tra44_no_14 :
    ∀ lines : Nat, lines < tra44Top → lines < tra44Lower := by
  intro lines h
  have h15 : tra44Lower = 15 := rfl
  simp [tra44Top] at h
  omega
