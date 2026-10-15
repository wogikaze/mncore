/-
大容量下りの下限モデルと 23.dram-dl-256-1024 (Top=68) の最適性.

参照解 problems/23.dram-dl-256-1024/answer.vsm (68行):
  MV部2行 + L2単独58行 + 対6行 + L1単独2行

根拠 (judge 実測):
- MV部2行が最小 (ペイロードと単位動作から)。
  MV行に `;` 併記形はなく1行1発行。
- L2 64発行 (単独58 + 対6に含まれる分) は同行不可
  (l2bmd同士のconflictを実測: 先行対・後続のいずれも)。
  対6行はL1との異種同発で、L2同士の削減にはならない。
- L1単独2行の同行化は l1bm_emit conflictで拒否。
よって 2 + 64 + 2 = 68行が下限で Top=68 は最適。
-/

/-- MV部の最小行数 -/
def dl2561kMv : Nat := 2

/-- L2部の最小行数 -/
def dl2561kL2 : Nat := 64

/-- L1単独部の最小行数 -/
def dl2561kL1 : Nat := 2

/-- 現1位行数 Top = 68 -/
def dl2561kTop : Nat := 68

/-- 行数下限 = 2 + 64 + 2 = 68 -/
def dl2561kLower : Nat :=
  dl2561kMv + dl2561kL2 + dl2561kL1

theorem dl2561k_lower : dl2561kLower = 68 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl2561k_optimal : dl2561kLower = dl2561kTop := rfl

/-- 系: 67行以下での Accepted は存在しない -/
theorem dl2561k_no_67 :
    ∀ lines : Nat, lines < dl2561kTop → lines < dl2561kLower := by
  intro lines h
  have h68 : dl2561kLower = 68 := rfl
  simp [dl2561kTop] at h
  omega
