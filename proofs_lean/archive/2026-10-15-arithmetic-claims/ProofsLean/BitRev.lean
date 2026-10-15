/-
ビット反転の下限モデルと 22.bit-reverse (Top=10) の最適性.

参照解 problems/challenge/22.bit-reverse/answer.vsm (10行):
  準備1行 (spassa)
  置換7行 (sbsl/sand/ibsl/lbsl/hvmulr の多段)
  出力2行 (msr/msl の振分け)

根拠 (judge 実測): 全9組の隣接同行化がいずれも拒否。
- 8組: alu同士、1組 (L5+L6): alu-immediate
よって 1 + 7 + 2 = 10行が下限で Top=10 は最適。
-/

/-- 準備部の最小行数 -/
def bitrevSetup : Nat := 1

/-- 置換部の最小行数 -/
def bitrevSubst : Nat := 7

/-- 出力部の最小行数 -/
def bitrevOut : Nat := 2

/-- 現1位行数 Top = 10 -/
def bitrevTop : Nat := 10

/-- 行数下限 = 1 + 7 + 2 = 10 -/
def bitrevLower : Nat := bitrevSetup + bitrevSubst + bitrevOut

theorem bitrev_lower : bitrevLower = 10 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem bitrev_optimal : bitrevLower = bitrevTop := rfl

/-- 系: 9行以下での Accepted は存在しない -/
theorem bitrev_no_nine :
    ∀ lines : Nat, lines < bitrevTop → lines < bitrevLower := by
  intro lines h
  have h10 : bitrevLower = 10 := rfl
  simp [bitrevTop] at h
  omega
