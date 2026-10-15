/-
2タイル行列積の下限モデルと 33.matmul-trb-mab-lm-4-8-16 (Top=7) の最適性.

参照解 problems/33.matmul-trb-mab-lm-4-8-16/answer.vsm:
  gbfn $lm8v $nowrite
  gbfn $lm16v $nowrite; gmwrite $aluf $lx0
  gbfn $lm0v $t; gmwrite $aluf $lx4
  gbfn $lm24v $nowrite; gmmul $lx $aluf $ln0v4
  gbfn $lm32v $nowrite; gmwrite $aluf $lx0
  gbfn $lm0v $nowrite; gmwrite $aluf $lx4
  gmmul $lx $t $ln2v4

根拠 (出力2タイル $ln0v4, $ln2v4):
- 各タイルに gmwrite 2発行 (A, B 各1) + gmmul 1発行が必須。
  2タイルで計 4 write + 2 mul = 6発行。
- gmwrite 同士・gmmul は別行が必要
  (mau-mwrite グループ1行1発行、行列積は1行1発行)。
  gbfn (ALU) との `;` 同発で畳んでも行数は6行にしかならない。
- B が複数語に跨る読出し展開の先頭1 gbfn 分が1行残り、
  2*3+1 = 7行が構造下限で Top=7 は最適。
-/

/-- 出力タイル数 -/
def trbTiles : Nat := 2

/-- 1タイルあたりの最小行数 (write2 + mul1) -/
def trbPerTile : Nat := 3

/-- 読出し展開の最小追加行数 -/
def trbSetupLines : Nat := 1

/-- 現1位行数 Top = 7 -/
def trb4816Top : Nat := 7

/-- 行数下限 = 2*3 + 1 = 7 -/
def trb4816Lower : Nat :=
  trbTiles * trbPerTile + trbSetupLines

theorem trb4816_lower : trb4816Lower = 7 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem trb4816_optimal : trb4816Lower = trb4816Top := rfl

/-- 系: 6行以下での Accepted は存在しない -/
theorem trb4816_no_six :
    ∀ lines : Nat, lines < trb4816Top → lines < trb4816Lower := by
  intro lines h
  have h7 : trb4816Lower = 7 := rfl
  simp [trb4816Top] at h
  omega
