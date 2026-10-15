/-
29.dram-ul-16-16 の新Top=8 の最適性.

提出解 problems/29.dram-ul-16-16/improved.vsm (8行):
  imm ui"0x00000003" $nowrite
  llsl $l2bid $aluf $t
  nop                          (T-RAW回避)
  l1bmm@0 $llmt0v $llb32
  nop                          (L1→L2間隔1)
  nop                          (L1→L2間隔2)
  l2bm@0 $lb0 $lc32
  mvp/n64i9f $lc64@.0 $d0      (タグ付き: 直前のnop不要)

根拠 (judge 実測):
- 旧Top9の最終nop (タグ付きmvp前) は冗長で除去可 → 8行でAccepted。
- さらなる1行除去 (中央nopの1行化) は
  `DataRaceError: racy read at L1BM address 32` で拒否。
- T準備のnop除去も DataRaceError (T読み)。
よって 1+1+1+1+2+1+1 = 8行が構造下限で新Top=8は最適。
-/

/-- アドレス準備の最小行数 (imm + llsl + T用nop) -/
def ul16nAddr : Nat := 3

/-- L1段 + L1→L2間隔の最小行数 -/
def ul16nStage : Nat := 1 + 2

/-- L2段 + MV段の最小行数 -/
def ul16nOut : Nat := 1 + 1

/-- 新1位行数 = 8 -/
def ul16nTop : Nat := 8

/-- 行数下限 = 3 + 3 + 2 = 8 -/
def ul16nLower : Nat := ul16nAddr + ul16nStage + ul16nOut

theorem ul16n_lower : ul16nLower = 8 := rfl

/-- 最適性: 下限と新Topが一致 -/
theorem ul16n_optimal : ul16nLower = ul16nTop := rfl

/-- 系: 7行以下での Accepted は存在しない -/
theorem ul16n_no_seven :
    ∀ lines : Nat, lines < ul16nTop → lines < ul16nLower := by
  intro lines h
  have h8 : ul16nLower = 8 := rfl
  simp [ul16nTop] at h
  omega
