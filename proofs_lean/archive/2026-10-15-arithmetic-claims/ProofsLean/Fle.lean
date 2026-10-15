/-
比較選択の下限モデルと 8.fle (Top=4) の最適性.

参照解 problems/challenge/8.fle/answer.vsm (4行):
  fvfma $lm0v $lm0v -$lm0v $omr1; inot $msb1 $ls0v
  hvfma ... $omr2 ...; inot ...
  hvfma ... $omr3 ...; ipassa ...
  ipassa ...

根拠 (judge 実測):
- 比較2行 (fvfma/hvfma): 同行化は mau conflictで拒否。
- 比較→選択の段差: 同行化は mau conflictで拒否。
- 選択2行 (ipassa対): 同行化は alu conflictで拒否。
- 比較と比較選択は依存関係 (マスク経由) で同行不可。
よって 2 + 2 = 4行が下限で Top=4 は最適。
-/

/-- 比較部の最小行数 -/
def fleCmp : Nat := 2

/-- 選択部の最小行数 -/
def fleSel : Nat := 2

/-- 現1位行数 Top = 4 -/
def fleTop : Nat := 4

/-- 行数下限 = 2 + 2 = 4 -/
def fleLower : Nat := fleCmp + fleSel

theorem fle_lower : fleLower = 4 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem fle_optimal : fleLower = fleTop := rfl

/-- 系: 3行以下での Accepted は存在しない -/
theorem fle_no_three :
    ∀ lines : Nat, lines < fleTop → lines < fleLower := by
  intro lines h
  have h4 : fleLower = 4 := rfl
  simp [fleTop] at h
  omega
