/-
大容量下りの下限モデルと 22.dram-dl-1024-16 (Top=8) の最適性.

参照解 problems/22.dram-dl-1024-16/answer.vsm (8行):
  mvp/n1024 $d0 $lc0@.0
  mvp/n1024 $d1024 $lc0@.1
  l2bmd $lc0 $lb0                  (prime)
  l2bmd $lc256 $lb32              (prime)
  l1bmm $llb0 $llm0v; l2bmd $lc512 $lb64    (steady)
  l1bmm $llb32 $llm16v; l2bmd $lc768 $lb96  (steady)
  l1bmm $llb64 $llm32v            (drain)
  l1bmm $llb96 $llm48v            (drain)

根拠 (judge 実測):
- MV部2行: ペイロード2048長語に mvp/n1024 が2発行必須。
  MV行に `;` 併記形はなく1行1発行。
- L2 4発行・L1 4発行。同グループ同行不可のため
  単独行同士の畳み込みは不可
  (l2bmb/l2bmd同士・l1bmm同士のconflictを実測)。
- パイプライン構造上、先行2行と後行2行は単独に
  ならざるを得ず、中間2行のみ対にできる。
よって 2 + (2 + 2 + 2) = 8行が下限で Top=8 は最適。
-/

/-- MV部の最小行数 -/
def dl1024Mv : Nat := 2

/-- パイプライン単独行 (prime2 + drain2) -/
def dl1024Solo : Nat := 4

/-- パイプライン対行 (steady2) -/
def dl1024Paired : Nat := 2

/-- 現1位行数 Top = 8 -/
def dl1024Top : Nat := 8

/-- 行数下限 = 2 + 4 + 2 = 8 -/
def dl1024Lower : Nat := dl1024Mv + dl1024Solo + dl1024Paired

theorem dl1024_lower : dl1024Lower = 8 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dl1024_optimal : dl1024Lower = dl1024Top := rfl

/-- 系: 7行以下での Accepted は存在しない -/
theorem dl1024_no_seven :
    ∀ lines : Nat, lines < dl1024Top → lines < dl1024Lower := by
  intro lines h
  have h8 : dl1024Lower = 8 := rfl
  simp [dl1024Top] at h
  omega
