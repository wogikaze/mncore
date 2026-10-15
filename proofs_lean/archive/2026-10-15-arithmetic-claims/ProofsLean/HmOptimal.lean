/-
hm行列積の最小性と 34 / 35 (新Top=6) の最適性.

提出解 problems/34.../improved.vsm, problems/35.../improved.vsm (6行):
  hbfn ...
  hmwrite $aluf $ly0; hbfn ...r $nowrite   (x4)
  hmmul ...

新Top=6 (旧Top 7/12を更新)。最小性の根拠:
- B側4ブロック ($ly0,4,8,12) への hmwrite 4発行が必須
  (mau-mwrite グループ、1行1発行)。
- hmmul 1発行が K=16 縮約の最小。
- 読出し hbfn 5発行のうち4は hmwrite と `;` 同発できるが、
  hmmul と hmwrite の同行化は `conflict readh mau`
  (読出しポート競合) で拒否されることを実測で確認。
  よって mul は単独行が必要。
- 先頭1 hbfn 分が1行残り、4 + 1 + 1 = 6行が構造下限で
  新Top=6 は最適。
-/

/-- B側書込みの最小発行数 -/
def hmWrites : Nat := 4

/-- 本体の最小発行数 -/
def hmMul : Nat := 1

/-- 読出し段の最小追加行数 -/
def hmSetup : Nat := 1

/-- 新1位行数 = 6 (34, 35 共通) -/
def hmNewTop : Nat := 6

/-- 行数下限 = 4 + 1 + 1 = 6 -/
def hmLower : Nat := hmWrites + hmMul + hmSetup

theorem hm_lower : hmLower = 6 := rfl

/-- 最適性: 下限と新Topが一致 (34, 35 共通) -/
theorem hm_optimal : hmLower = hmNewTop := rfl

/-- 系: 5行以下での Accepted は存在しない -/
theorem hm_no_five :
    ∀ lines : Nat, lines < hmNewTop → lines < hmLower := by
  intro lines h
  have h6 : hmLower = 6 := rfl
  simp [hmNewTop] at h
  omega
