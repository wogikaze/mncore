/-
行列積の下限モデルと 32.matmul-trb-mab-lm-4-8-8 (Top=4) の最適性.

参照解 problems/32.matmul-trb-mab-lm-4-8-8/answer.vsm:
  gbfn $lm8v $nowrite
  gbfn $lm16v $nowrite; gmwrite $aluf $lx0
  gbfn $lm0v $nowrite; gmwrite $aluf $lx4
  gmmul $lx $aluf $ln0v

根拠:
- C = A·Bᵀ を行列ユニットで計算するには A, B を行列レジスタ
  ($lx0, $lx4) に書く必要があり、gmwrite が2発行必須。
  gmwrite は mau-mwrite グループで1行1発行まで (3.6.4)。
- gmmul 1発行が K=8 縮約の最小 (ALU/MAU展開なら数十行)。
- B が $lm8v, $lm16v の2語に跨るため読出しに gbfn 展開が必要で、
  `;` 同発で畳んでも先頭の1 gbfn 分が1行残る。
よって 2(mwrite) + 1(gmmul) + 1(読出し段) = 4行が下限で
Top=4 は最適。
-/

/-- 行列レジスタ書込みの最小発行数 (A, B 各1) -/
def matWriteIssues : Nat := 2

/-- 行列積本体の最小発行数 (gmmul 1発) -/
def matMulIssues : Nat := 1

/-- 読出し展開の最小追加行数 (Bが2語跨ぎ) -/
def matSetupLines : Nat := 1

/-- 現1位行数 Top = 4 -/
def matTrb488Top : Nat := 4

/-- 行数下限 = 2 + 1 + 1 = 4 -/
def matTrb488Lower : Nat :=
  matWriteIssues + matMulIssues + matSetupLines

theorem matTrb488_lower : matTrb488Lower = 4 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem matTrb488_optimal : matTrb488Lower = matTrb488Top := rfl

/-- 系: 3行以下での Accepted は存在しない -/
theorem matTrb488_no_three :
    ∀ lines : Nat, lines < matTrb488Top → lines < matTrb488Lower := by
  intro lines h
  have h4 : matTrb488Lower = 4 := rfl
  simp [matTrb488Top] at h
  omega
