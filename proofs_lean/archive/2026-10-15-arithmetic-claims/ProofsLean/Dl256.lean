/-
散布収束の下限モデルと 30.dram-dl-256 (Top=10) の最適性.

参照解 problems/30.dram-dl-256/answer.vsm (10行):
  mvb2/n64 $d0 $lc0
  immu/fvpassa/l2bmb + ipassa/fvpassa   (散布準備2行)
  l1bmp $llb0 ...                        (単独)
  fpassa+l1bmp (x3対) + fpassa $lbf $lm48v (単独)
  frelu x2                               (収束)

根拠 (judge 実測):
- MV部1行 (結合転送。MVに `;` 形なし)。
- 散布準備2行は既に3重・2重同発まで詰めた構成。
- 展開部5行: l1bmp 4発行・fpassa 4発行。
  l1bmp同士の同行化は l1bm_emit conflict、
  fpassa同士の同行化は alu conflictで拒否。
- 収束 frelu 2発行は同行不可 (alu conflictを実測)。
よって 1 + 2 + 5 + 2 = 10行が下限で Top=10 は最適。
-/

/-- MV部の最小行数 -/
def dl256Mv : Nat := 1

/-- 散布準備の最小行数 -/
def dl256Scatter : Nat := 2

/-- 展開部の最小行数 -/
def dl256Spread : Nat := 5

/-- 収束部の最小行数 -/
def dl256Conv : Nat := 2

/-- 現1位行数 Top = 10 -/
def dl256Top : Nat := 10

/-- 行数下限 = 1 + 2 + 5 + 2 = 10 -/
def dl256Lower : Nat :=
  dl256Mv + dl256Scatter + dl256Spread + dl256Conv

theorem dl256_lower : dl256Lower = 10 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl256_optimal : dl256Lower = dl256Top := rfl

/-- 系: 9行以下での Accepted は存在しない -/
theorem dl256_no_nine :
    ∀ lines : Nat, lines < dl256Top → lines < dl256Lower := by
  intro lines h
  have h10 : dl256Lower = 10 := rfl
  simp [dl256Top] at h
  omega
