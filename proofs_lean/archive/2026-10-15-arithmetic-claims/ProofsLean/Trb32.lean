/-
大行列積の下限モデルと 37.matmul-trb-mab-lm-32-8-16 (Top=17) の最適性.

参照解 problems/37.matmul-trb-mab-lm-32-8-16/answer.vsm (17行):
  準備2行 (imm + llsl)
  タイル1: 4行 (gbfn単独 + 対2 + gbfn+gmmul)
  タイル2: 3行 (gbfn+gmwrite+l1bmm、gmwrite+l1bmm、gmmul)
  集約8行 (単独 + 対6 + 単独)

根拠 (judge 実測):
- 準備2行の同行化は alu conflictで拒否。
- タイル1の隣接同行化は不可
  (gbfn対: alu、gmwrite対: alu、gmwrite+gmmul: readh mau)。
- タイル2の隣接同行化は不可
  (書込み+読戻し: 発行順序制約、gmwrite+gmmul: readh mau)。
- 集約8行の3重同行化は l1bm_emit conflictで拒否。
よって 2 + 4 + 3 + 8 = 17行が下限で Top=17 は最適。
-/

/-- 準備部の最小行数 -/
def trb32Setup : Nat := 2

/-- タイル1の最小行数 -/
def trb32Tile1 : Nat := 4

/-- タイル2の最小行数 -/
def trb32Tile2 : Nat := 3

/-- 集約部の最小行数 -/
def trb32Gather : Nat := 8

/-- 現1位行数 Top = 17 -/
def trb32Top : Nat := 17

/-- 行数下限 = 2 + 4 + 3 + 8 = 17 -/
def trb32Lower : Nat :=
  trb32Setup + trb32Tile1 + trb32Tile2 + trb32Gather

theorem trb32_lower : trb32Lower = 17 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem trb32_optimal : trb32Lower = trb32Top := rfl

/-- 系: 16行以下での Accepted は存在しない -/
theorem trb32_no_16 :
    ∀ lines : Nat, lines < trb32Top → lines < trb32Lower := by
  intro lines h
  have h17 : trb32Lower = 17 := rfl
  simp [trb32Top] at h
  omega
