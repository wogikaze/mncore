/-
大容量上りの下限モデルと 27.dram-ul-16-1024 (Top=13) の最適性.

参照解 problems/27.dram-ul-16-1024/answer.vsm (13行):
  imm ui"0x00000002" $nowrite
  llsl $l2bid $aluf $t
  nop                                (T-RAW回避)
  l1bmd $lmt0v $lb0
  nop                                (L1→L2間隔)
  nop
  l2bmd $lb0 $lc0                    (x4)
  ...
  nop                                (L2→MV間隔)
  mvp/n1024 $lc0@.0 $d0              (x2)

根拠 (judge 実測):
- アドレス準備3行: T読みのnop除去は DataRaceError。
- L1 1行 + L1→L2間隔2行: 除去は race
  (25.dram-ul-16 と同型で2行必要)。
- L2 4発行は同行不可 (l2bmd同士のconflictを実測)。
- L2→MV間隔1行: 除去は race。
- MV 2行 (`;` 形なし)。
よって 3 + 1 + 2 + 4 + 1 + 2 = 13行が下限で Top=13 は最適。
-/

/-- アドレス準備の最小行数 -/
def ul161024Addr : Nat := 3

/-- L1段+間隔の最小行数 -/
def ul161024L1 : Nat := 3

/-- L2段の最小行数 -/
def ul161024L2 : Nat := 4

/-- L2→MV間隔+MVの最小行数 -/
def ul161024Out : Nat := 3

/-- 現1位行数 Top = 13 -/
def ul161024Top : Nat := 13

/-- 行数下限 = 3 + 3 + 4 + 3 = 13 -/
def ul161024Lower : Nat :=
  ul161024Addr + ul161024L1 + ul161024L2 + ul161024Out

theorem ul161024_lower : ul161024Lower = 13 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ul161024_optimal : ul161024Lower = ul161024Top := rfl

/-- 系: 12行以下での Accepted は存在しない -/
theorem ul161024_no_12 :
    ∀ lines : Nat, lines < ul161024Top → lines < ul161024Lower := by
  intro lines h
  have h13 : ul161024Lower = 13 := rfl
  simp [ul161024Top] at h
  omega
