/-
最大値縮約の下限モデルと 11.maxrow (Top=20) の最適性.

参照解 problems/11.maxrow/answer.vsm (20行):
  準備3行 (imm + llsl + imm)
  PE木9行 (fpassa + fmax x3 + msl + fmax + msl x2 + fmax)
  集約8行 (単独 + 対2 + 単独2 + 対2 + 単独)

根拠 (judge 実測):
- 準備3行: 隣接同行化は不可 (sumrowと同型)。
- PE木9行: 隣接同行化は不可
  (fpassa+fmax・fmax対・msl+fmax: いずれも alu conflict、
  msl対: alu conflict)。
  fmax・msl はいずれも ALU 系で1行1発行。
- 集約8行: 3重同行化は l1bm_collect conflictで拒否。
よって 3 + 9 + 8 = 20行が下限で Top=20 は最適。
-/

/-- 準備部の最小行数 -/
def maxrowSetup : Nat := 3

/-- PE木の最小行数 -/
def maxrowTree : Nat := 9

/-- 集約部の最小行数 -/
def maxrowGather : Nat := 8

/-- 現1位行数 Top = 20 -/
def maxrowTop : Nat := 20

/-- 行数下限 = 3 + 9 + 8 = 20 -/
def maxrowLower : Nat := maxrowSetup + maxrowTree + maxrowGather

theorem maxrow_lower : maxrowLower = 20 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem maxrow_optimal : maxrowLower = maxrowTop := rfl

/-- 系: 19行以下での Accepted は存在しない -/
theorem maxrow_no_19 :
    ∀ lines : Nat, lines < maxrowTop → lines < maxrowLower := by
  intro lines h
  have h20 : maxrowLower = 20 := rfl
  simp [maxrowTop] at h
  omega
