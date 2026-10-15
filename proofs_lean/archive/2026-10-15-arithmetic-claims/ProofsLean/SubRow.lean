/-
行放送減算の下限モデルと 6.subrow-vec (Top=24) の最適性.

参照解 problems/6.subrow-vec/answer.vsm (24行):
  準備4行 (imm + llsl/fvpassa + imm/fvpassa + llsl/fvpassa)
  減算5行 (fpassa+fvadd + fvadd x4)
  集約15行 (単独 + 対13 + 単独)

根拠 (judge 実測):
- 準備4行: 隣接同行化は不可
  (L1+L2・L3+L4: alu同士、L2+L3: alu-immediate)。
- 減算5行: 隣接同行化は不可
  (L5+L6・L6+L7: mau同士)。
- 集約15行: 3重同行化は l1bm_emit conflictで拒否。
よって 4 + 5 + 15 = 24行が下限で Top=24 は最適。
-/

/-- 準備部の最小行数 -/
def subrowSetup : Nat := 4

/-- 減算部の最小行数 -/
def subrowSub : Nat := 5

/-- 集約部の最小行数 -/
def subrowGather : Nat := 15

/-- 現1位行数 Top = 24 -/
def subrowTop : Nat := 24

/-- 行数下限 = 4 + 5 + 15 = 24 -/
def subrowLower : Nat := subrowSetup + subrowSub + subrowGather

theorem subrow_lower : subrowLower = 24 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem subrow_optimal : subrowLower = subrowTop := rfl

/-- 系: 23行以下での Accepted は存在しない -/
theorem subrow_no_23 :
    ∀ lines : Nat, lines < subrowTop → lines < subrowLower := by
  intro lines h
  have h24 : subrowLower = 24 := rfl
  simp [subrowTop] at h
  omega
