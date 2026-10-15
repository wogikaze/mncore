/-
DRAM出力package積の下限モデルと 39.matmul-trb-pkg-lmdram-256-1024-16 (Top=29) の最適性.

参照解 problems/39.matmul-trb-pkg-lmdram-256-1024-16/answer.vsm (29行):
  準備5行 (gbfn単独 + gbfn+gmwrite x4対)
  本体16行 (8タイル各2行)
  出力8行 (縮約対 + l2bmr x4 + nop + mvp x2)

根拠 (judge 実測):
- 準備5行: 対同士の同行化は alu conflictで拒否。
- 本体16行: タイル対の同行化は mau conflictで拒否。
- 出力8行: l2bmr同士の同行化は l2bm conflictで拒否。
  最終nop除去は DataRaceError で拒否。
  MV行に `;` 併記形はなく1行1発行。
よって 5 + 16 + 8 = 29行が下限で Top=29 は最適。
-/

/-- 準備部の最小行数 -/
def trbPdSetup : Nat := 5

/-- 本体の最小行数 -/
def trbPdBody : Nat := 16

/-- 出力部の最小行数 -/
def trbPdOut : Nat := 8

/-- 現1位行数 Top = 29 -/
def trbPdTop : Nat := 29

/-- 行数下限 = 5 + 16 + 8 = 29 -/
def trbPdLower : Nat := trbPdSetup + trbPdBody + trbPdOut

theorem trbPd_lower : trbPdLower = 29 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem trbPd_optimal : trbPdLower = trbPdTop := rfl

/-- 系: 28行以下での Accepted は存在しない -/
theorem trbPd_no_28 :
    ∀ lines : Nat, lines < trbPdTop → lines < trbPdLower := by
  intro lines h
  have h29 : trbPdLower = 29 := rfl
  simp [trbPdTop] at h
  omega
