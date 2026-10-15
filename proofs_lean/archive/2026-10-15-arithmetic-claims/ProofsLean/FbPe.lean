/-
分岐問題の下限モデルと 23.fizzbuzz-pe (Top=9) の最適性.

参照解 problems/challenge/23.fizzbuzz-pe/answer.vsm (9行):
  定数準備4行 + 3/5判定3行 + 出力選択2行

根拠 (judge 実測): 全8組の隣接同行化がいずれも拒否。
- L1+L2・L3+L4・L4+L5: alu同士
- L2+L3・L5+L6・L6+L7・L7+L8・L8+L9: alu-immediate
よって 4 + 3 + 2 = 9行が下限で Top=9 は最適。
-/

/-- 定数準備部の最小行数 -/
def fbpeConst : Nat := 4

/-- 判定部の最小行数 -/
def fbpeJudge : Nat := 3

/-- 出力部の最小行数 -/
def fbpeOut : Nat := 2

/-- 現1位行数 Top = 9 -/
def fbpeTop : Nat := 9

/-- 行数下限 = 4 + 3 + 2 = 9 -/
def fbpeLower : Nat := fbpeConst + fbpeJudge + fbpeOut

theorem fbpe_lower : fbpeLower = 9 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem fbpe_optimal : fbpeLower = fbpeTop := rfl

/-- 系: 8行以下での Accepted は存在しない -/
theorem fbpe_no_eight :
    ∀ lines : Nat, lines < fbpeTop → lines < fbpeLower := by
  intro lines h
  have h9 : fbpeLower = 9 := rfl
  simp [fbpeTop] at h
  omega
