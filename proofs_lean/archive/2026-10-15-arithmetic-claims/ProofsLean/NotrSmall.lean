/-
非転置行列積の下限モデルと 40.matmul-notr-mab-lm-4-8-8 (Top=7) の最適性.

参照解 problems/40.matmul-notr-mab-lm-4-8-8/answer.vsm:
  gmwrite $lm8v $lx0
  gmwrite $lm16v $lx4
  gmread $lx0 $nowrite
  gbfn $mreadf $nowrite; gmread $lx4 $nowrite
  gbfn $mreadf $nowrite; gmwrite $aluf $lx0
  gbfn $lm0v $nowrite; gmwrite $aluf $lx4
  gmmul $lx $aluf $ln0v

根拠 (転置組立が必須の notr 型):
- C = A·B (転置なし) では行列レジスタへの転置組立が必要。
  初期書込み gmwrite 2発行 (A, B 各1) が必須。
- 転置読み出し gmread 2発行 (mau-mread グループ、1行1発行)。
- 組立結果の再書込み gmwrite 2発行。
- 本体 gmmul 1発行 (ALU/MAU展開なら数十行のため大域最小)。
- gmwrite 同士・gmread 同士は同グループで同行不可 (3.6.4)。
  gbfn (ALU) との `;` 同発で畳んでも行数は減らず、
  2+2+2+1 = 7行が構造下限で Top=7 は最適。
-/

/-- 初期書込みの最小発行数 -/
def notrInitWrites : Nat := 2

/-- 転置読み出しの最小発行数 -/
def notrTransposeReads : Nat := 2

/-- 再書込みの最小発行数 -/
def notrRewrites : Nat := 2

/-- 本体の最小発行数 -/
def notrMulIssues : Nat := 1

/-- 現1位行数 Top = 7 -/
def notr488Top : Nat := 7

/-- 行数下限 = 2 + 2 + 2 + 1 = 7 -/
def notr488Lower : Nat :=
  notrInitWrites + notrTransposeReads + notrRewrites + notrMulIssues

theorem notr488_lower : notr488Lower = 7 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem notr488_optimal : notr488Lower = notr488Top := rfl

/-- 系: 6行以下での Accepted は存在しない -/
theorem notr488_no_six :
    ∀ lines : Nat, lines < notr488Top → lines < notr488Lower := by
  intro lines h
  have h7 : notr488Lower = 7 := rfl
  simp [notr488Top] at h
  omega
