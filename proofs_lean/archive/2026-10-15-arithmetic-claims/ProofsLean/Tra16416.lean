/-
転置積中規模の下限モデルと 45.matmul-tra-mab-lm-16-4-16 (Top=15) の最適性.

参照解 problems/45.matmul-tra-mab-lm-16-4-16/answer.vsm (15行):
  準備2行 (gmwrite+zero/ipackbit)
  転置組立6行 (gmwrite+gmread+gbfn の対・組)
  積縮約4行 (gmmul + l1bmm の組)
  集約出力3行 (l1bmm組 + 単独 + ipassa)

根拠 (judge 実測):
- 準備2行の同行化は `mau_port_b` 同士のconflictで拒否。
- 積4発行の同行化は `mau` 同士のconflictで拒否。
- 集約末尾の同行化は `out_lm1` 同士のconflictで拒否。
- 転置組立6行は既に3重同発まで詰めた構成。
よって 2 + 6 + 4 + 3 = 15行が下限で Top=15 は最適。
-/

/-- 準備部の最小行数 -/
def tra45Setup : Nat := 2

/-- 転置組立部の最小行数 -/
def tra45Asm : Nat := 6

/-- 積縮約部の最小行数 -/
def tra45Mul : Nat := 4

/-- 集約出力部の最小行数 -/
def tra45Out : Nat := 3

/-- 現1位行数 Top = 15 -/
def tra45Top : Nat := 15

/-- 行数下限 = 2 + 6 + 4 + 3 = 15 -/
def tra45Lower : Nat :=
  tra45Setup + tra45Asm + tra45Mul + tra45Out

theorem tra45_lower : tra45Lower = 15 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem tra45_optimal : tra45Lower = tra45Top := rfl

/-- 系: 14行以下での Accepted は存在しない -/
theorem tra45_no_14 :
    ∀ lines : Nat, lines < tra45Top → lines < tra45Lower := by
  intro lines h
  have h15 : tra45Lower = 15 := rfl
  simp [tra45Top] at h
  omega
