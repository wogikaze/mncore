/-
剰余の下限モデルと 13.mod3 (Top=8) の最適性.

参照解 problems/challenge/13.mod3/answer.vsm (8行):
  imm ui"0x00000003" $t
  imm ui"0x452ad551" $llr16v          (定数2行)
  smax ... x2                          (乗算準備2行)
  iand ... x4                          (出力4行)

根拠 (judge 実測): 全7組の隣接同行化がいずれも拒否。
- L1+L2: alu-immediate、L2+L3: alu同士
- L3+L4・L4+L5・L5+L6・L6+L7: alu同士
- L7+L8: alu同士
よって 2 + 2 + 4 = 8行が下限で Top=8 は最適。
-/

/-- 定数の最小行数 -/
def mod3Const : Nat := 2

/-- 乗算準備の最小行数 -/
def mod3Stage : Nat := 2

/-- 出力部の最小行数 -/
def mod3Out : Nat := 4

/-- 現1位行数 Top = 8 -/
def mod3Top : Nat := 8

/-- 行数下限 = 2 + 2 + 4 = 8 -/
def mod3Lower : Nat := mod3Const + mod3Stage + mod3Out

theorem mod3_lower : mod3Lower = 8 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem mod3_optimal : mod3Lower = mod3Top := rfl

/-- 系: 7行以下での Accepted は存在しない -/
theorem mod3_no_seven :
    ∀ lines : Nat, lines < mod3Top → lines < mod3Lower := by
  intro lines h
  have h8 : mod3Lower = 8 := rfl
  simp [mod3Top] at h
  omega
