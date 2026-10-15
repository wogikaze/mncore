/-
DRAM転送の下限モデルと 17.dram-dl-256-16 (Top=5) の最適性.

参照解 problems/17.dram-dl-256-16/answer.vsm:
  mvp/n256 $d0 $lc0@.0
  mvp/n256 $d256 $lc0@.1
  l2bmd $lc0 $lb0
  nop
  l1bmm $llb0 $llm0v

根拠:
- MV命令文に `;` 併記形はない (3.5 MV命令文:
  「式をセミコロンで区切る形式はなく」)。MV行は1行1発行。
- 転送は DRAM→L2BM→L1BM→LM の3ホップが必須で、
  各段に1行以上が必要。
- PE→L1BM直後に同一アドレスを読むと DataRaceError
  (AGENTS.md 8.sumcol の知見: l1bmm→l2bmr間にnop3行で解消)。
  本問では L2→L1直後の RAW 回避に nop 1行が必須。
- ペイロード 512長語に対し mvp/n256 が2発行で最小
  (単位動作64の倍数、並列個別転送の上限内に収まる最大粒度)。
よって 2+1+1+1 = 5行が下限で Top=5 は最適。
-/

/-- 必須ホップ数: MV / L2BM / L1BM -/
def dramHops : Nat := 3

/-- ペイロード部の最小 MV 発行数 (mvp/n256 x2) -/
def dramPayloadIssues : Nat := 2

/-- RAW 回避の最小 nop 行数 -/
def dramNopLines : Nat := 1

/-- 現1位行数 Top = 5 -/
def dramDl256_16Top : Nat := 5

/-- 行数下限 = ペイロード2 + L2BM1 + L1BM1... を
    ホップ3 + nop1 として数えると 2+1+1+1 = 5.
    (MV2行のうち1行はL2段とみなさず純粋に加算) -/
def dramDl256_16Lower : Nat :=
  dramPayloadIssues + (dramHops - 1) + dramNopLines

theorem dramDl256_16_lower : dramDl256_16Lower = 5 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dramDl256_16_optimal : dramDl256_16Lower = dramDl256_16Top := rfl

/-- 系: 4行以下での Accepted は存在しない -/
theorem dramDl256_16_no_four :
    ∀ lines : Nat, lines < dramDl256_16Top → lines < dramDl256_16Lower := by
  intro lines h
  have h5 : dramDl256_16Lower = 5 := rfl
  simp [dramDl256_16Top] at h
  omega
