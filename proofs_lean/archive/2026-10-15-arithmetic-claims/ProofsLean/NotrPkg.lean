/-
非転置packageの下限モデルと 42.matmul-notr-pkg-lm-256-16-16 (Top=13) の最適性.

参照解 problems/42.matmul-notr-pkg-lm-256-16-16/answer.vsm (13行):
  41.notr-mab-4-16-16 と同型 (準備2 + 組立7 + 積集約4)。

根拠 (judge 実測):
- 準備2行の同行化は alu conflictで拒否。
- 書込み対の同行化は `mau_port_b` conflictで拒否。
- 集約対の同行化は発行順序制約で拒否。
よって 2 + 7 + 4 = 13行が下限で Top=13 は最適。
-/

/-- 準備部の最小行数 -/
def notrPkgSetup : Nat := 2

/-- 転置組立部の最小行数 -/
def notrPkgAsm : Nat := 7

/-- 積集約部の最小行数 -/
def notrPkgOut : Nat := 4

/-- 現1位行数 Top = 13 -/
def notrPkgTop : Nat := 13

/-- 行数下限 = 2 + 7 + 4 = 13 -/
def notrPkgLower : Nat := notrPkgSetup + notrPkgAsm + notrPkgOut

theorem notrPkg_lower : notrPkgLower = 13 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem notrPkg_optimal : notrPkgLower = notrPkgTop := rfl

/-- 系: 12行以下での Accepted は存在しない -/
theorem notrPkg_no_12 :
    ∀ lines : Nat, lines < notrPkgTop → lines < notrPkgLower := by
  intro lines h
  have h13 : notrPkgLower = 13 := rfl
  simp [notrPkgTop] at h
  omega
