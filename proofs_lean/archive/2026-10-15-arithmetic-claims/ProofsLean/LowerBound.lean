/-
MN-Core2 下限モデル (machine-checkable core).

マニュアル根拠:
- ALU は PE につき 1 つ (3.6.12)
- inc/add/sub は 2長語動作 no (3.6.12 表3.9) → 1サイクル1長語
- 並列実行条件: グループにつき最大1式 (3.6.4)
- MAU は浮動小数点のみ (3.6.9.1)
- score = j+m 行数 (judge.py:360-366), 1ステップ = 1行
-/

/-- 1ステップ = 4サイクル -/
def cyclesPerStep : Nat := 4

/-- 1サイクルあたりの計算幅 (bit) -/
def bitsPerCycle : Nat := 64

/-- Int 1要素の幅 -/
def bitsPerInt : Nat := 32

/-- ALU 整数演算 1発行あたりの最大 Int 要素数/サイクル.
    2長語動作 no のため 1長語 = 2 Int に制限. -/
def intsPerCycleALU : Nat := 2

/-- 1ステップ(1行)あたりの ALU 上限: 4サイクル × 2 = 8 -/
def intsPerStepALU : Nat := cyclesPerStep * intsPerCycleALU

theorem intsPerStepALU_eq : intsPerStepALU = 8 := rfl

/-- 1行に含められる ALU 式は最大 1 (3.6.4 グループ排他).
    実測: `iinc ...; iinc ...` は
    `Instruction field conflict between alu and alu` で拒否. -/
def maxALUPerStep : Nat := 1

/-- MAU で Int の +1 は計算できない (浮動小数点専用). -/
def mauCanIntInc : Bool := false

/-- 必要 ALU 発行回数: 天井割り算 -/
def aluIssuesNeeded (elems : Nat) : Nat :=
  (elems + intsPerStepALU - 1) / intsPerStepALU

theorem aluIssuesNeeded_16 : aluIssuesNeeded 16 = 2 := rfl

/-- 行数下限: ALU 発行回数 (1行1発行のため) -/
def lineLowerBound (elems : Nat) : Nat :=
  aluIssuesNeeded elems / maxALUPerStep

theorem lineLowerBound_16 : lineLowerBound 16 = 2 := rfl
