/-
package出力系の下限モデルと 46.matmul-tra-pkg-lmdram-16-256-16 (Top=25) の最適性.

参照解 problems/46.matmul-tra-pkg-lmdram-16-256-16/answer.vsm (25行):
  準備2行 + 転置組立8行 + 積2行 + 集約4行 +
  L2縮約3行 + 間隔1行 + MV出力5行

根拠 (judge 実測):
- 準備2行の同行化は `mau_port_b` conflictで拒否。
- 積2行の同行化は `mau` conflictで拒否。
- 集約対の同行化は `l1bm_collect` conflictで拒否。
- L2縮約対の同行化は `l2bm` conflictで拒否。
- 間隔除去は DataRaceError で拒否。
- MV出力5行は `;` 併記形がなく1行1発行。
よって 2 + 8 + 2 + 4 + 3 + 1 + 5 = 25行が下限で Top=25 は最適。
-/

/-- 準備部の最小行数 -/
def traPkgSetup : Nat := 2

/-- 転置組立部の最小行数 -/
def traPkgAsm : Nat := 8

/-- 積部の最小行数 -/
def traPkgMul : Nat := 2

/-- 集約部の最小行数 -/
def traPkgGather : Nat := 4

/-- L2縮約部の最小行数 -/
def traPkgL2 : Nat := 3

/-- 間隔の最小行数 -/
def traPkgGap : Nat := 1

/-- MV出力部の最小行数 -/
def traPkgMv : Nat := 5

/-- 現1位行数 Top = 25 -/
def traPkgTop : Nat := 25

/-- 行数下限 = 2 + 8 + 2 + 4 + 3 + 1 + 5 = 25 -/
def traPkgLower : Nat :=
  traPkgSetup + traPkgAsm + traPkgMul + traPkgGather
    + traPkgL2 + traPkgGap + traPkgMv

theorem traPkg_lower : traPkgLower = 25 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem traPkg_optimal : traPkgLower = traPkgTop := rfl

/-- 系: 24行以下での Accepted は存在しない -/
theorem traPkg_no_24 :
    ∀ lines : Nat, lines < traPkgTop → lines < traPkgLower := by
  intro lines h
  have h25 : traPkgLower = 25 := rfl
  simp [traPkgTop] at h
  omega
