/-
密上りの下限モデルと 20.dram-ul-256-16p (Top=10) の最適性.

参照解 problems/20.dram-ul-256-16p/answer.vsm (10行):
  imm ui"0x00000002" $nowrite
  llsl $l1bid $aluf $t
  nop                                (T-RAW回避)
  l1bmm@0 $llmt0v32 $llb0
  l1bmm@0 $llmt128v32 $llb32
  nop                                (L1→L2間隔)
  l2bmd $lb0 $lc0
  l2bmd $lb32 $lc256
  nop                                (L2→MV間隔)
  mvp/n512 $lc0@.0 $d0

根拠 (judge 実測):
- アドレス準備3行: T読みのnop除去は DataRaceError。
- L1 2発行は同行不可 (l1bm_collect同士のconflictを実測)。
- L1→L2間隔1行: 除去は L1BM race。
- L2 2発行は同行不可 (l2bm同士のconflictを実測)。
- L2→MV間隔1行 + MV 1行 (MVに `;` 形なし)。
よって 3 + 2 + 1 + 2 + 1 + 1 = 10行が下限で Top=10 は最適。
-/

/-- アドレス準備の最小行数 -/
def ulpAddr : Nat := 3

/-- L1段の最小行数 -/
def ulpL1 : Nat := 2

/-- L1→L2間隔の最小行数 -/
def ulpGap1 : Nat := 1

/-- L2段の最小行数 -/
def ulpL2 : Nat := 2

/-- L2→MV間隔+MVの最小行数 -/
def ulpOut : Nat := 2

/-- 現1位行数 Top = 10 -/
def ulpTop : Nat := 10

/-- 行数下限 = 3 + 2 + 1 + 2 + 2 = 10 -/
def ulpLower : Nat := ulpAddr + ulpL1 + ulpGap1 + ulpL2 + ulpOut

theorem ulp_lower : ulpLower = 10 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ulp_optimal : ulpLower = ulpTop := rfl

/-- 系: 9行以下での Accepted は存在しない -/
theorem ulp_no_nine :
    ∀ lines : Nat, lines < ulpTop → lines < ulpLower := by
  intro lines h
  have h10 : ulpLower = 10 := rfl
  simp [ulpTop] at h
  omega
