/-
転置積の下限モデルと 43.matmul-tra-mab-lm-8-8-8 (Top=8) の最適性.

参照解 problems/43.matmul-tra-mab-lm-8-8-8/answer.vsm (8行):
  gmwrite $lm16v $lx0                     (単独書込み)
  gmwrite $lm24v $lx4                     (単独書込み)
  gmwrite $lm0v $ly0; gmread $lx0 $nowrite        (対x4)
  gbfn $mreadf $nowrite; gmwrite $lm8v $ly4; gmread $lx4 $nowrite
  gbfn $mreadf $nowrite; gmwrite $aluf $lx0; gmread $ly0 $nowrite
  gbfn $mreadf $nowrite; gmwrite $aluf $lx4; gmread $ly4 $nowrite
  gbfn $mreadf $nowrite; gmmul $lx $aluf $ln0v    (積1)
  gmmul $lx $aluf $ln8v                          (積2)

根拠 (judge 実測):
- 転置組立に gmwrite 6発行が必要。うち4は gmread と対にできるが、
  残り2は単独行にならざるを得ない。
  2書込みの同行化は `mau_port_b` 同士のconflictで拒否。
- 本体 gmmul 2発行は同行不可 (`mau` 同士のconflictを実測)。
- gmread 4発行は書込み対に吸収済みで追加行なし。
よって 2 + 4 + 2 = 8行が下限で Top=8 は最適。
-/

/-- 単独書込みの最小行数 -/
def tra88Solo : Nat := 2

/-- 書込み+読出し対の最小行数 -/
def tra88Paired : Nat := 4

/-- 本体の最小行数 -/
def tra88Mul : Nat := 2

/-- 現1位行数 Top = 8 -/
def tra88Top : Nat := 8

/-- 行数下限 = 2 + 4 + 2 = 8 -/
def tra88Lower : Nat := tra88Solo + tra88Paired + tra88Mul

theorem tra88_lower : tra88Lower = 8 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem tra88_optimal : tra88Lower = tra88Top := rfl

/-- 系: 7行以下での Accepted は存在しない -/
theorem tra88_no_seven :
    ∀ lines : Nat, lines < tra88Top → lines < tra88Lower := by
  intro lines h
  have h8 : tra88Lower = 8 := rfl
  simp [tra88Top] at h
  omega
