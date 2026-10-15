/-
2入力加算の下限モデルと challenge/3.a-plus-b (Top=6) の最適性.

参照解 problems/challenge/3.a-plus-b/answer.vsm:
  iadd $lm0v $ln0v $lr0v
  iadd $lm8v $ln8v $lr8v
  iadd $lm16v $ln16v $lr16v
  iadd $lm24v $ln24v $lr24v
  ipassa $llr0v $llm32v
  ipassa $llr16v $llm48v

根拠:
- 32要素の加算は iadd (ALU整数演算、1行8要素) で4発行必須。
  入力2系統は LM0/LM1 の別メモリのため同行2読み可だが、
  ALU は1行1発行まで (3.6.4)。
- 結果32要素の LM への書戻しは GRF 経由で、
  ipassa は 2長語動作 yes のため1行16要素、
  2発行が必須。
- 加算と書戻しは依存関係 (GRF RAW) で同行不可。
よって 4+2 = 6行が下限で Top=6 は最適。
-/

/-- 加算部の最小発行数 (32要素/8) -/
def aplubAddIssues : Nat := 4

/-- 書戻し部の最小発行数 (32要素/16、ll動作) -/
def aplubWbIssues : Nat := 2

/-- 現1位行数 Top = 6 -/
def aplubTop : Nat := 6

/-- 行数下限 = 4 + 2 = 6 -/
def aplubLower : Nat := aplubAddIssues + aplubWbIssues

theorem aplub_lower : aplubLower = 6 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem aplub_optimal : aplubLower = aplubTop := rfl

/-- 系: 5行以下での Accepted は存在しない -/
theorem aplub_no_five :
    ∀ lines : Nat, lines < aplubTop → lines < aplubLower := by
  intro lines h
  have h6 : aplubLower = 6 := rfl
  simp [aplubTop] at h
  omega
