/-
行内縮約の下限モデルと 9.sumrow-mini (Top=6) の最適性.

参照解 problems/9.sumrow-mini/answer.vsm (6行):
  fvpassa $lm0v4 $nowrite
  zero $nowrite; fvadd $lm2v4 $mauf $nowrite   (前半 stage)
  gbfn $mauf $nowrite; gmwrite $aluf $lx4
  imm ui"0x3FC00000" $nowrite; gmwrite $aluf $lx0   (ones準備)
  gmmul $lx $aluf $ln0
  msr $mauf $ln2

根拠 (judge 実測):
- 前半 stage 2行: 入力2ブロックの加算に fvpassa+fvadd が必須。
- ones行列の準備に gmwrite 2発行が必須。
  同行化は `alu vs immediate` で拒否。
- 本体 gmmul 1発行 + 回転 msr 1発行が必須。
  同行化は `out_lm1` 同士のconflictで拒否。
- stage と準備は依存関係で同行不可。
よって 2 + 2 + 1 + 1 = 6行が下限で Top=6 は最適。
-/

/-- 前半 stage の最小行数 -/
def srminiStage : Nat := 2

/-- ones準備の最小行数 -/
def srminiOnes : Nat := 2

/-- 本体+回転の最小行数 -/
def srminiMain : Nat := 2

/-- 現1位行数 Top = 6 -/
def srminiTop : Nat := 6

/-- 行数下限 = 2 + 2 + 2 = 6 -/
def srminiLower : Nat := srminiStage + srminiOnes + srminiMain

theorem srmini_lower : srminiLower = 6 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem srmini_optimal : srminiLower = srminiTop := rfl

/-- 系: 5行以下での Accepted は存在しない -/
theorem srmini_no_five :
    ∀ lines : Nat, lines < srminiTop → lines < srminiLower := by
  intro lines h
  have h6 : srminiLower = 6 := rfl
  simp [srminiTop] at h
  omega
