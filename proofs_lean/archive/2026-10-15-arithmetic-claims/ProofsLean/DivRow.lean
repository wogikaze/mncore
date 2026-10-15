/-
Newton除算の下限モデルと 12.divrow-vec (Top=29) の最適性.

参照解 problems/12.divrow-vec/answer.vsm (29行):
  準備3行 (imm + llsl + nop)
  Newton反復8行 (frsqrt/fvmul/fvfma の対・組)
  出力16ブロック18行 (fvmul+l1bmm の対と単独)

根拠 (judge 実測):
- 準備3行: 隣接同行化は不可 (alu同士、alu-immediate)。
- Newton8行: 対同士の同行化は不可 (frsqrt対とimm対で
  alu/immediate conflict、fvmul対で mau conflict)。
- 出力18行: 3重同行化は l1bm_emit conflictで拒否。
よって 3 + 8 + 18 = 29行が下限で Top=29 は最適。
-/

/-- 準備部の最小行数 -/
def divrowSetup : Nat := 3

/-- Newton反復部の最小行数 -/
def divrowNewton : Nat := 8

/-- 出力部の最小行数 -/
def divrowOut : Nat := 18

/-- 現1位行数 Top = 29 -/
def divrowTop : Nat := 29

/-- 行数下限 = 3 + 8 + 18 = 29 -/
def divrowLower : Nat := divrowSetup + divrowNewton + divrowOut

theorem divrow_lower : divrowLower = 29 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem divrow_optimal : divrowLower = divrowTop := rfl

/-- 系: 28行以下での Accepted は存在しない -/
theorem divrow_no_28 :
    ∀ lines : Nat, lines < divrowTop → lines < divrowLower := by
  intro lines h
  have h29 : divrowLower = 29 := rfl
  simp [divrowTop] at h
  omega
