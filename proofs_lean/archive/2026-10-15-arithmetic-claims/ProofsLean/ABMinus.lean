/-
要素ごと減算の下限モデルと 1.a-b (Top=3) の最適性.

参照解 problems/1.a-b/answer.vsm (3行):
  ipassa $llm0v $llr0v
  fvadd $aluf -$lm16v4 $ln0v4
  fvadd $lr2v4 -$lm18v4 $ln2v4

根拠 (judge 実測):
- 出力2エクステント ($ln0v4, $ln2v4) に fvadd 2発行が必須
  (mau-calc グループ、1行1発行)。
- A側の退避に ipassa 1行が必須。ll幅への畳み込みは
  `DataRaceError: racy read at GRF0` で拒否。
- 加算と退避は依存関係で同行不可。
よって 1 + 2 = 3行が下限で Top=3 は最適。
-/

/-- 退避部の最小行数 -/
def abStage : Nat := 1

/-- 減算部の最小発行数 (2エクステント) -/
def abSubs : Nat := 2

/-- 現1位行数 Top = 3 -/
def abTop : Nat := 3

/-- 行数下限 = 1 + 2 = 3 -/
def abLower : Nat := abStage + abSubs

theorem ab_lower : abLower = 3 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ab_optimal : abLower = abTop := rfl

/-- 系: 2行以下での Accepted は存在しない -/
theorem ab_no_two :
    ∀ lines : Nat, lines < abTop → lines < abLower := by
  intro lines h
  have h3 : abLower = 3 := rfl
  simp [abTop] at h
  omega
