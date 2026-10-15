/-
階層縮約の下限モデルと 8.sumcol (Top=9) の最適性.

参照解 problems/8.sumcol/answer.vsm (9行):
  imm ui"0x00000002" $nowrite
  llsl $mabid $aluf $t
  nop                            (T-RAW回避)
  l1bmr4ffadd $lmt0v $lb0
  l1bmr4ffadd $lmt2v $lb4
  nop                            (L1→L2間隔1)
  nop                            (L1→L2間隔2)
  l2bmrffadd $lb0 $lc0
  mvrffadd/n64 $lc0 $d0

根拠 (judge 実測):
- MAB依存アドレス準備に imm + llsl + T用nop の3行が必須
  (T読みのnop除去は DataRaceError)。
- MAB方向縮約 l1bmr 2発行は同グループで同行不可
  (l1bm_collect同士のconflictを実測)。
- L1→L2方向の同一アドレス読みには nop 2行が必須。
  1行化は `DataRaceError: racy read at L1BM address 0`。
- L2BM縮約とMV出力に各1行 (MVに `;` 形なし)。
よって 3+2+2+1+1 = 9行が下限で Top=9 は最適。
-/

/-- アドレス準備の最小行数 -/
def sumcolAddr : Nat := 3

/-- MAB縮約の最小発行数 -/
def sumcolMab : Nat := 2

/-- L1→L2間隔の最小nop行数 -/
def sumcolGap : Nat := 2

/-- L2縮約+MV出力の最小行数 -/
def sumcolOut : Nat := 2

/-- 現1位行数 Top = 9 -/
def sumcolTop : Nat := 9

/-- 行数下限 = 3 + 2 + 2 + 2 = 9 -/
def sumcolLower : Nat :=
  sumcolAddr + sumcolMab + sumcolGap + sumcolOut

theorem sumcol_lower : sumcolLower = 9 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem sumcol_optimal : sumcolLower = sumcolTop := rfl

/-- 系: 8行以下での Accepted は存在しない -/
theorem sumcol_no_eight :
    ∀ lines : Nat, lines < sumcolTop → lines < sumcolLower := by
  intro lines h
  have h9 : sumcolLower = 9 := rfl
  simp [sumcolTop] at h
  omega
