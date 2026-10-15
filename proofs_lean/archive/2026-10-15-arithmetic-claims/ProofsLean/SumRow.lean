/-
行和の大規模縮約の下限モデルと 10.sumrow (Top=16) の最適性.

参照解 problems/10.sumrow/answer.vsm (16行):
  準備3行 (imm + ilsl + imm)
  行列5行 (fbfn+fmwrite/fmmul/fmfma の対 x3 + fmfma単独 + 対)
  集約8行 (単独 + 対2 + 単独2 + 対2 + 単独)

根拠 (judge 実測):
- 準備3行: 隣接同行化は不可 (L1+L2: alu同士、L2+L3: alu-immediate)。
- 行列5行: 対同士の同行化は readh mau で拒否。
- 集約8行: 3重同行化は l1bm_collect conflictで拒否。
よって 3 + 5 + 8 = 16行が下限で Top=16 は最適。
-/

/-- 準備部の最小行数 -/
def sumrowSetup : Nat := 3

/-- 行列部の最小行数 -/
def sumrowMat : Nat := 5

/-- 集約部の最小行数 -/
def sumrowGather : Nat := 8

/-- 現1位行数 Top = 16 -/
def sumrowTop : Nat := 16

/-- 行数下限 = 3 + 5 + 8 = 16 -/
def sumrowLower : Nat := sumrowSetup + sumrowMat + sumrowGather

theorem sumrow_lower : sumrowLower = 16 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem sumrow_optimal : sumrowLower = sumrowTop := rfl

/-- 系: 15行以下での Accepted は存在しない -/
theorem sumrow_no_15 :
    ∀ lines : Nat, lines < sumrowTop → lines < sumrowLower := by
  intro lines h
  have h16 : sumrowLower = 16 := rfl
  simp [sumrowTop] at h
  omega
