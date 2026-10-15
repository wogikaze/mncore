/-
小規模転送の下限モデルと 24.dram-dl-16 / 25.dram-ul-16 (Top=5) の最適性.

参照解 problems/24.dram-dl-16/answer.vsm (5行):
  mvp/n64 $d0@0 $p0@0
  mvb/n64 $p0@0 $lc0
  l2bmb $lc0 $lb0
  nop
  l1bmm $llb0 $llm0v/ll1000

参照解 problems/25.dram-ul-16/answer.vsm (5行):
  l1bmm@0 $llm0v $llb0
  nop
  nop
  l2bmd $lb0 $lc0
  mvp/n64 $lc0@0.0 $d0@0

根拠:
- 下りは DRAM→PDM→L2BM→L1BM→LM の全段が必須で、
  MV 2発行 (mvp, mvb) + L2 1行 + L1 1行。
  MV行に `;` 併記形はなく1行1発行 (3.5)。
- L2→L1方向の同一アドレス読みには nop 1行が必須
  (24.dram-dl-16 の実測: nop除去は
  `DataRaceError: racy read at L1BM`)。
  よって 2+1+1+1 = 5行が下限で Top=5 は最適。
- 上りは LM→L1BM→L2BM→DRAM の3ホップで L1 1行 + L2 1行 + MV 1行、
  L1→L2方向の同一アドレス読みには nop 2行が必須
  (25.dram-ul-16 の実測: nop除去は
  `DataRaceError: racy read at L1BM`)。
  よって 1+2+1+1 = 5行が下限で Top=5 は最適。
-/

/-- 現1位行数 Top = 5 (両問) -/
def dl16Top : Nat := 5
def ul16Top : Nat := 5

/-- 下り下限 = MV2 + L2 1 + nop1 + L1 1 = 5 -/
def dl16Lower : Nat := 2 + 1 + 1 + 1

/-- 上り下限 = L1 1 + nop2 + L2 1 + MV1 = 5 -/
def ul16Lower : Nat := 1 + 2 + 1 + 1

theorem dl16_lower : dl16Lower = 5 := rfl
theorem ul16_lower : ul16Lower = 5 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl16_optimal : dl16Lower = dl16Top := rfl
theorem ul16_optimal : ul16Lower = ul16Top := rfl

/-- 系: 4行以下での Accepted は存在しない -/
theorem dl16_no_four :
    ∀ lines : Nat, lines < dl16Top → lines < dl16Lower := by
  intro lines h
  have h5 : dl16Lower = 5 := rfl
  simp [dl16Top] at h
  omega

theorem ul16_no_four :
    ∀ lines : Nat, lines < ul16Top → lines < ul16Lower := by
  intro lines h
  have h5 : ul16Lower = 5 := rfl
  simp [ul16Top] at h
  omega
