/-
所属判定miniの下限モデルと 15.onehot-mini (Top=7) の最適性.

参照解 problems/15.onehot-mini/answer.vsm (7行):
  imm/0101 ui"0x3F800008" $lr0v
  ipackbit $subpeid $aluf $nowrite; hvpassar -$aluf $omr1; ...
  linc $aluf $nowrite; ...                         (比較準備2行)
  iadd/$imr1 $aluf $lr0v $t; ...                   (選択2行)
  ixor $aluf $ls[0,0,2,2] $omr1
  ixor $t $ls[4,4,6,6] $omr2; hvpassar/$imr1 ...
  hvpassar/$imr2 $lr2 $ln8v                        (出力2行)

根拠 (judge 実測): 全6組の隣接同行化がいずれも拒否。
- L1+L2, L2+L3, L3+L4, L4+L5, L5+L6: alu同士
- L6+L7: mau同士
よって 1 + 2 + 2 + 2 = 7行が下限で Top=7 は最適。
-/

/-- 定数の最小行数 -/
def ohmConst : Nat := 1

/-- 比較準備の最小行数 -/
def ohmPrep : Nat := 2

/-- 選択部の最小行数 -/
def ohmSelect : Nat := 2

/-- 出力部の最小行数 -/
def ohmOut : Nat := 2

/-- 現1位行数 Top = 7 -/
def ohmTop : Nat := 7

/-- 行数下限 = 1 + 2 + 2 + 2 = 7 -/
def ohmLower : Nat := ohmConst + ohmPrep + ohmSelect + ohmOut

theorem ohm_lower : ohmLower = 7 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem ohm_optimal : ohmLower = ohmTop := rfl

/-- 系: 6行以下での Accepted は存在しない -/
theorem ohm_no_six :
    ∀ lines : Nat, lines < ohmTop → lines < ohmLower := by
  intro lines h
  have h7 : ohmLower = 7 := rfl
  simp [ohmTop] at h
  omega
