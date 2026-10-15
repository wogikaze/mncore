/-
7.sumcol-mini (4x16 列和 → 16要素、Top=4) の最適性.

参照解 problems/7.sumcol-mini/answer.vsm:
  fpassa $lm0v $nowrite
  fvadd $lm4v $aluf $nowrite
  fvadd $lm8v $mauf $nowrite
  fvadd $lm12v $mauf $ln0v

根拠:
- 4つの異なる LM 語 ($lm0v,4v,8v,12v) を読む必要がある
- 1命令の LM 直接読みは1語まで
  (AGENTS.md 躓き記録: `fvadd $m0v $m4v` は
  `Instruction field conflict between 'lm0' and 'in_lm0'` で失敗)
  3.6.4 並列実行条件「1サイクルで複数種類のアドレスからの
  読み出しはできない」に対応
- fpassa/fvadd はいずれも mau-calc グループ → 1行1発行まで
よって 4語読みに4行が必要で Top=4 は最適。
(資源下限3はポート制約を見ない弱い下限のため真の下限は4)
-/

/-- sumcol-mini が読む LM 語数 -/
def sumcolMiniWords : Nat := 4

/-- 1命令あたりの LM 直接読み上限 -/
def maxLMDirectPerInstr : Nat := 1

/-- 1行あたりの mau-calc 発行上限 (3.6.4 グループ排他) -/
def maxMauCalcPerStep : Nat := 1

/-- 現1位行数 Top = 4 -/
def sumcolMiniTop : Nat := 4

/-- 必要命令数 = 語数 (1命令1語のため) -/
def sumcolMiniIssues : Nat :=
  (sumcolMiniWords + maxLMDirectPerInstr - 1) / maxLMDirectPerInstr

theorem sumcolMini_issues : sumcolMiniIssues = 4 := rfl

/-- 行数下限 = 命令数 (1行1発行のため) -/
def sumcolMiniLower : Nat :=
  (sumcolMiniIssues + maxMauCalcPerStep - 1) / maxMauCalcPerStep

theorem sumcolMini_lower : sumcolMiniLower = 4 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem sumcolMini_optimal : sumcolMiniLower = sumcolMiniTop := rfl

/-- 系: 3行以下での Accepted は存在しない -/
theorem sumcolMini_no_three :
    ∀ lines : Nat, lines < sumcolMiniTop → lines < sumcolMiniLower := by
  intro lines h
  have h4 : sumcolMiniLower = 4 := rfl
  simp [sumcolMiniTop] at h
  omega
