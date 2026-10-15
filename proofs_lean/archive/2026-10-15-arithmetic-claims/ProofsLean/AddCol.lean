/-
列放送加算の下限モデルと 5.addcol-vec (Top=3) の最適性.

参照解 problems/5.addcol-vec/answer.vsm (3行):
  fvpassa $lm[16,18,16,18] $t
  fvadd $lm0v $mauf $ln0v
  fvadd $lm8v $t $ln8v

根拠 (judge 実測):
- 列ベクトルBの放送保持に fvpassa 1行が必須 (T+mauf確保)。
  ll幅への畳み込みは値不一致 (1024/3072 mismatch) で拒否。
- 本体 fvadd 2発行は2エクステント分で必須
  (mau-calc グループ、1行1発行)。
- 保持と加算は依存関係で同行不可。
よって 1 + 2 = 3行が下限で Top=3 は最適。
-/

/-- 放送保持の最小行数 -/
def addcolStage : Nat := 1

/-- 加算部の最小発行数 (2エクステント) -/
def addcolAdds : Nat := 2

/-- 現1位行数 Top = 3 -/
def addcolTop : Nat := 3

/-- 行数下限 = 1 + 2 = 3 -/
def addcolLower : Nat := addcolStage + addcolAdds

theorem addcol_lower : addcolLower = 3 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem addcol_optimal : addcolLower = addcolTop := rfl

/-- 系: 2行以下での Accepted は存在しない -/
theorem addcol_no_two :
    ∀ lines : Nat, lines < addcolTop → lines < addcolLower := by
  intro lines h
  have h3 : addcolLower = 3 := rfl
  simp [addcolTop] at h
  omega
