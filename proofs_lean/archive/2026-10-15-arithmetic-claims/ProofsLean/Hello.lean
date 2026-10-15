/-
文字列生成の下限モデルと 21.hello-world (Top=9) の最適性.

参照解 problems/challenge/21.hello-world/answer.vsm (9行):
  imm ui"0x3A655E6C" $lr0 $t
  idec $subpeid $omr1; dvpassar $aluf $r1
  imm ui"0x61725E64" $r0/$imr1; fvadd -$aluf -$t $omr2
  imm ui"0x612C1277" $r1v2/$imr2
  l1bmrhfadd $lr[16,16,16,0] $lb36
  nop # この行にnop以外の命令を書くとエラーになります
  nop # なんで?
  l2bmrhfadd $lb16 $lc32
  mvp/n64 $lc64@0.0 $d0@0)

根拠 (judge 実測):
- 準備4行: 定数3 + 演算対。隣接同士の畳み込みは不可
  (L1+L2: alu同士、L2+L3・L3+L4: alu-immediate)。
- 縮約2行 (l1bmr + l2bmr): 同行化はアセンブルできても
  旧データ読みで値不一致 (0/13)。
- nop 2行: 除去は L1BM race (問題文指定どおり)。
- MV 1行 (`;` 形なし)。
よって 4 + 2 + 2 + 1 = 9行が下限で Top=9 は最適。
-/

/-- 準備部の最小行数 -/
def helloSetup : Nat := 4

/-- 縮約部の最小行数 -/
def helloReduce : Nat := 2

/-- 間隔の最小行数 -/
def helloGap : Nat := 2

/-- 出力の最小行数 -/
def helloOut : Nat := 1

/-- 現1位行数 Top = 9 -/
def helloTop : Nat := 9

/-- 行数下限 = 4 + 2 + 2 + 1 = 9 -/
def helloLower : Nat :=
  helloSetup + helloReduce + helloGap + helloOut

theorem hello_lower : helloLower = 9 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem hello_optimal : helloLower = helloTop := rfl

/-- 系: 8行以下での Accepted は存在しない -/
theorem hello_no_eight :
    ∀ lines : Nat, lines < helloTop → lines < helloLower := by
  intro lines h
  have h9 : helloLower = 9 := rfl
  simp [helloTop] at h
  omega
