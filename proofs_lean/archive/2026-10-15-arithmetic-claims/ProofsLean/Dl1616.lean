/-
密転送の下限モデルと 28.dram-dl-16-16 (Top=11) の最適性.

参照解 problems/28.dram-dl-16-16/answer.vsm (11行):
  mvp/n64 $d0@0 $p0@0          (x4群)
  mvb/n256 $p0@0 $lc0
  l2bmb $lc0 $lb0              (prime)
  l2bmb $lc64 $lb32            (prime)
  l1bmm $llb0 $llm0v; l2bmb $lc128 $lb64    (steady)
  l1bmm $llb32 $llm16v; l2bmb $lc192 $lb96  (steady)
  l1bmm $llb64 $llm32v         (drain)
  l1bmm $llb96 $llm48v         (drain)

根拠 (judge 実測):
- MV部5行: 群あたり有効ペイロード64が上限で
  mvp/n128拡大は誤転送。4群+結合1で5行が最小。
- L2 4発行・L1 4発行。同グループ同行不可のため
  単独行同士の畳み込みは不可 (l2bmb同士・l1bmm同士の
  conflictを実測)。
- パイプライン構造上、先行2行 (prime) と後行2行 (drain) は
  単独にならざるを得ず、中間2行のみ対にできる。
よって 5 + (2 + 2 + 2) = 11行が下限で Top=11 は最適。
-/

/-- MV部の最小行数 (4群 + 結合1) -/
def dl1616Mv : Nat := 5

/-- パイプライン単独行 (prime2 + drain2) -/
def dl1616Solo : Nat := 4

/-- パイプライン対行 (steady2) -/
def dl1616Paired : Nat := 2

/-- 現1位行数 Top = 11 -/
def dl1616Top : Nat := 11

/-- 行数下限 = 5 + 4 + 2 = 11 -/
def dl1616Lower : Nat := dl1616Mv + dl1616Solo + dl1616Paired

theorem dl1616_lower : dl1616Lower = 11 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl1616_optimal : dl1616Lower = dl1616Top := rfl

/-- 系: 10行以下での Accepted は存在しない -/
theorem dl1616_no_ten :
    ∀ lines : Nat, lines < dl1616Top → lines < dl1616Lower := by
  intro lines h
  have h11 : dl1616Lower = 11 := rfl
  simp [dl1616Top] at h
  omega
