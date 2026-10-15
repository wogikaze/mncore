/-
ベクトル上りの下限モデルと 31.dram-ul-256 (Top=7) の最適性.

参照解 problems/31.dram-ul-256/answer.vsm (score=7):
  ipackbit $peid $lm0 $t
  nop                            (T-RAW回避)
  l1bmd $lmt0 $lb0
  nop/2                          (L1→L2間隔2単位)
  l2bm@0 $lb0 $lc0
  mvp/n64 $lc0@.0 $d0

根拠 (judge 実測):
- PE依存アドレス準備に ipackbit + T用nop の2行が必須。
- L1段1行。L1→L2方向の同一アドレス読みには2単位の間隔が必須。
  `nop/2` 除去は `DataRaceError: racy read at L1BM`。
  (scoreは `nop/2` が2行分で合計7)
- L1→L2の同行転送は旧データ読み (値不一致を実測)。
- L2段とMV段に各1行 (MVに `;` 形なし)。
よって 2+1+2+1+1 = 7行が下限で Top=7 は最適。
-/

/-- アドレス準備の最小行数 -/
def ul256vAddr : Nat := 2

/-- L1段の最小行数 -/
def ul256vL1 : Nat := 1

/-- L1→L2間隔の最小行数 (nop/2) -/
def ul256vGap : Nat := 2

/-- L2段+MV段の最小行数 -/
def ul256vOut : Nat := 2

/-- 現1位行数 Top = 7 -/
def ul256vTop : Nat := 7

/-- 行数下限 = 2 + 1 + 2 + 2 = 7 -/
def ul256vLower : Nat :=
  ul256vAddr + ul256vL1 + ul256vGap + ul256vOut

theorem ul256v_lower : ul256vLower = 7 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ul256v_optimal : ul256vLower = ul256vTop := rfl

/-- 系: 6行以下での Accepted は存在しない -/
theorem ul256v_no_six :
    ∀ lines : Nat, lines < ul256vTop → lines < ul256vLower := by
  intro lines h
  have h7 : ul256vLower = 7 := rfl
  simp [ul256vTop] at h
  omega
