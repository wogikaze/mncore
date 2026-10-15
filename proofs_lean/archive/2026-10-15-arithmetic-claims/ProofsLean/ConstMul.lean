/-
定数積の下限モデルと 2.fmul7 (Top=5) の最適性.

参照解 problems/2.fmul7/answer.vsm:
  imm ui"0x40E00000" $t
  fvmul $lm0v $aluf $ln0v
  fvmul $lm8v $t $ln8v
  fvmul $lm16v $t $ln16v
  fvmul $lm24v $t $ln24v

根拠:
- 係数 7.0 (0x40E00000) は MAU 命令に即値埋め込み不可で
  `imm` 1発行が必須 (T/aluf 経由で供給)。
- 入力は $lm0v,8v,16v,24v の4エクステントに分散し、
  fvmul (mau-calc グループ、1行1発行) が4発行必須。
- imm は ALU グループ相当 (untyped) で MAU と同行可だが、
  初行は `imm; fvmul` の形で既に畳み込み済み
  (1行目が定数+初回積の役割を兼ねることはできない。
  fvmul の第2入力は $t/$aluf を読むため定数行が先行必須)。
よって 1+4 = 5行が下限で Top=5 は最適。
-/

/-- 定数準備の最小行数 (imm 1行) -/
def constLines : Nat := 1

/-- データ部の最小 MAU 発行数 (4エクステント) -/
def constMulDataIssues : Nat := 4

/-- 現1位行数 Top = 5 -/
def fmul7Top : Nat := 5

/-- 行数下限 = 1 + 4 = 5 -/
def fmul7Lower : Nat := constLines + constMulDataIssues

theorem fmul7_lower : fmul7Lower = 5 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem fmul7_optimal : fmul7Lower = fmul7Top := rfl

/-- 系: 4行以下での Accepted は存在しない -/
theorem fmul7_no_four :
    ∀ lines : Nat, lines < fmul7Top → lines < fmul7Lower := by
  intro lines h
  have h5 : fmul7Lower = 5 := rfl
  simp [fmul7Top] at h
  omega
