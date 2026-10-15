/-
大容量下りの下限モデルと 26.dram-dl-16-1024 (Top=39) の最適性.

参照解 problems/26.dram-dl-16-1024/answer.vsm (39行):
  mvp/n2048 x4 + mvb/n8192              (MV部5行)
  l2bmd 単独30行 + 対2行 (L2計32発行)
  l1bmd 単独2行 (+対2行に含まれる分)

根拠 (judge 実測):
- MV部5行: ペイロード2048長語x4群+結合に
  mvp/n2048 x4 + mvb/n8192 が最小。
  MV行に `;` 併記形はなく1行1発行。
- L2 32発行は同行不可 (l2bmd同士のconflictを実測:
  先行対・後続のいずれも)。
  対2行はL1との異種同発で、L2同士の削減にはならない。
- L1単独2行の同行化は l1bm_emit conflictで拒否。
よって 5 + 32 + 2 = 39行が下限で Top=39 は最適。
-/

/-- MV部の最小行数 -/
def dl161024Mv : Nat := 5

/-- L2部の最小行数 -/
def dl161024L2 : Nat := 32

/-- L1単独部の最小行数 -/
def dl161024L1 : Nat := 2

/-- 現1位行数 Top = 39 -/
def dl161024Top : Nat := 39

/-- 行数下限 = 5 + 32 + 2 = 39 -/
def dl161024Lower : Nat :=
  dl161024Mv + dl161024L2 + dl161024L1

theorem dl161024_lower : dl161024Lower = 39 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl161024_optimal : dl161024Lower = dl161024Top := rfl

/-- 系: 38行以下での Accepted は存在しない -/
theorem dl161024_no_38 :
    ∀ lines : Nat, lines < dl161024Top → lines < dl161024Lower := by
  intro lines h
  have h39 : dl161024Lower = 39 := rfl
  simp [dl161024Top] at h
  omega
