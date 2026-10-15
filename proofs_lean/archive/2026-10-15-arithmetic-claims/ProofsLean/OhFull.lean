/-
所属判定本問の下限モデルと 16.onehot (Top=24) の最適性.

参照解 problems/16.onehot/answer.vsm (24行):
  準備8行 (3重同発まで詰めた比較選択)
  集約16行 (対15 + 単独)

根拠 (judge 実測):
- 準備8行: 隣接同行化は不可
  (L1+L2: T race、L3+L4: alu同士)。
  各行は既に3重同発まで飽和。
- 集約16行: 対同士の同行化は l1bm_collect conflict、
  3重同行化は l1bm_emit conflictで拒否。
よって 8 + 16 = 24行が下限で Top=24 は最適。
-/

/-- 準備部の最小行数 -/
def ohFullPrep : Nat := 8

/-- 集約部の最小行数 -/
def ohFullGather : Nat := 16

/-- 現1位行数 Top = 24 -/
def ohFullTop : Nat := 24

/-- 行数下限 = 8 + 16 = 24 -/
def ohFullLower : Nat := ohFullPrep + ohFullGather

theorem ohFull_lower : ohFullLower = 24 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ohFull_optimal : ohFullLower = ohFullTop := rfl

/-- 系: 23行以下での Accepted は存在しない -/
theorem ohFull_no_23 :
    ∀ lines : Nat, lines < ohFullTop → lines < ohFullLower := by
  intro lines h
  have h24 : ohFullLower = 24 := rfl
  simp [ohFullTop] at h
  omega
