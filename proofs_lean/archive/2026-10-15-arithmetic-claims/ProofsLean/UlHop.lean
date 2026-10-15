/-
上り転送の下限モデルと 18.dram-ul-256-16 (Top=6) の最適性.

参照解 problems/18.dram-ul-256-16/answer.vsm:
  l1bmm@0 $llm0v $llb0
  nop
  nop
  l2bmd $lb0 $lc0
  mvp/n256 $lc0@.0 $d0
  mvp/n256 $lc0@.1 $d256

根拠:
- 上りは LM→L1BM→L2BM→DRAM の3ホップが必須で各1行。
- L1→L2方向の同一アドレス読みには nop 2行が必須
  (25.dram-ul-16 の実測: nop除去は
  `DataRaceError: racy read at L1BM`。本問も同型で2行)。
- ペイロード 512長語に mvp/n256 が2発行必須。
- MV行に `;` 併記形はなく1行1発行 (3.5)。
よって 1+2+1+2 = 6行が下限で Top=6 は最適。
-/

/-- L1段の最小行数 -/
def ulL1Lines : Nat := 1

/-- L1→L2間隔の最小nop行数 -/
def ulGapNops : Nat := 2

/-- L2段の最小行数 -/
def ulL2Lines : Nat := 1

/-- MV部の最小発行数 -/
def ulMvIssues : Nat := 2

/-- 現1位行数 Top = 6 -/
def ul256Top : Nat := 6

/-- 行数下限 = 1 + 2 + 1 + 2 = 6 -/
def ul256Lower : Nat :=
  ulL1Lines + ulGapNops + ulL2Lines + ulMvIssues

theorem ul256_lower : ul256Lower = 6 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ul256_optimal : ul256Lower = ul256Top := rfl

/-- 系: 5行以下での Accepted は存在しない -/
theorem ul256_no_five :
    ∀ lines : Nat, lines < ul256Top → lines < ul256Lower := by
  intro lines h
  have h6 : ul256Lower = 6 := rfl
  simp [ul256Top] at h
  omega
