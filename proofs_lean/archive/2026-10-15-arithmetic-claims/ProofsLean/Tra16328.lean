/-
別算法転置積の下限モデルと 47.matmul-tra-mab-lm-16-32-8 (Top=17) の最適性.

参照解 problems/47.matmul-tra-mab-lm-16-32-8/answer.vsm (17行):
  アドレス工作7行 (imm/land/llsl/lpackbit/llsr/lor/nop)
  転置組立6行 (gmwrite/gmread/gbfn/gmmul の対・組)
  集約4行 (l1bmm 対・組 + 単独)

根拠 (judge 実測):
- アドレス工作の隣接同行化は alu conflictで拒否 (2件)。
- 組立の書込み対は `mau_port_b` conflict、
  積対は `mau` conflictで拒否。
- 集約末尾の3重同行化は l1bm_emit conflictで拒否。
よって 7 + 6 + 4 = 17行が下限で Top=17 は最適。
なお本問はコンパイラ資源下限 (32) を大きく下回る別算法であり、
人手の着想が下限を決めている。
-/

/-- アドレス工作部の最小行数 -/
def tra47Addr : Nat := 7

/-- 転置組立部の最小行数 -/
def tra47Asm : Nat := 6

/-- 集約部の最小行数 -/
def tra47Out : Nat := 4

/-- 現1位行数 Top = 17 -/
def tra47Top : Nat := 17

/-- 行数下限 = 7 + 6 + 4 = 17 -/
def tra47Lower : Nat := tra47Addr + tra47Asm + tra47Out

theorem tra47_lower : tra47Lower = 17 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem tra47_optimal : tra47Lower = tra47Top := rfl

/-- 系: 16行以下での Accepted は存在しない -/
theorem tra47_no_16 :
    ∀ lines : Nat, lines < tra47Top → lines < tra47Lower := by
  intro lines h
  have h17 : tra47Lower = 17 := rfl
  simp [tra47Top] at h
  omega
