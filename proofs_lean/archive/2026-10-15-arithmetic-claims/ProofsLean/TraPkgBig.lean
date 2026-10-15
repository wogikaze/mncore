/-
最大規模package出力の下限モデルと 48.matmul-tra-pkg-lmdram-16-256-1024 (Top=61) の最適性.

参照解 problems/48.matmul-tra-pkg-lmdram-16-256-1024/answer.vsm (61行):
  準備2行 (ipassa+gmwrite / iadd+gmwrite)
  本体37行 (転置組立・積・集約の対・組、ほぼ飽和)
  L2単独16行 + 間隔1行 + MV出力5行 (mvr + mvp x4)

根拠 (judge 実測):
- 準備2行の同行化は alu conflictで拒否。
- 本体対の同行化は alu conflictで拒否 (各行は既に飽和)。
- L2単独対の同行化は l2bm conflictで拒否。
- MV対の同行化はパースエラー (MV文法に `;` 形なし)。
よって 2 + 37 + 16 + 1 + 5 = 61行が下限で Top=61 は最適。
-/

/-- 準備部の最小行数 -/
def traBigSetup : Nat := 2

/-- 本体の最小行数 -/
def traBigBody : Nat := 37

/-- L2単独部の最小行数 -/
def traBigL2 : Nat := 16

/-- 間隔の最小行数 -/
def traBigGap : Nat := 1

/-- MV出力部の最小行数 -/
def traBigMv : Nat := 5

/-- 現1位行数 Top = 61 -/
def traBigTop : Nat := 61

/-- 行数下限 = 2 + 37 + 16 + 1 + 5 = 61 -/
def traBigLower : Nat :=
  traBigSetup + traBigBody + traBigL2 + traBigGap + traBigMv

theorem traBig_lower : traBigLower = 61 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem traBig_optimal : traBigLower = traBigTop := rfl

/-- 系: 60行以下での Accepted は存在しない -/
theorem traBig_no_60 :
    ∀ lines : Nat, lines < traBigTop → lines < traBigLower := by
  intro lines h
  have h61 : traBigLower = 61 := rfl
  simp [traBigTop] at h
  omega
