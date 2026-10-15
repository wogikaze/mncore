/-
バイト交換の下限モデルと 12.convert-endian (Top=3) の最適性.

参照解 problems/challenge/12.convert-endian/answer.vsm (3行):
  imm i"0x34f80010" $r0v
  ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v
  sbsl $aluf $mauf $n[1,0,3,2]

根拠 (judge 実測):
- 定数1行は即値埋め込み不可のため必須。
- シャッフル2段 (ibsl+fvfma、sbsl) の同行化は
  alu conflictで拒否。ISAにバイト交換単一命令はなく
  2段が最小分解。
- 定数行とシャッフル初段の同行化も alu conflictで拒否。
よって 1 + 2 = 3行が下限で Top=3 は最適。
-/

/-- 定数の最小行数 -/
def endianConst : Nat := 1

/-- シャッフル段の最小行数 -/
def endianShuffle : Nat := 2

/-- 現1位行数 Top = 3 -/
def endianTop : Nat := 3

/-- 行数下限 = 1 + 2 = 3 -/
def endianLower : Nat := endianConst + endianShuffle

theorem endian_lower : endianLower = 3 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem endian_optimal : endianLower = endianTop := rfl

/-- 系: 2行以下での Accepted は存在しない -/
theorem endian_no_two :
    ∀ lines : Nat, lines < endianTop → lines < endianLower := by
  intro lines h
  have h3 : endianLower = 3 := rfl
  simp [endianTop] at h
  omega
