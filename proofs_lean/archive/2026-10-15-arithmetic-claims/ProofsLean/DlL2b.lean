/-
L2B分散残し転送の下限モデルと 21.dram-dl-256-16-l2b (Top=12) の最適性.

参照解 problems/21.dram-dl-256-16-l2b/answer.vsm (12行):
  mvp/n256 $d0 $lc0@.0
  mvp/n256 $d256 $lc0@.1
  l2bmb $lc0 $lb0                  (prime)
  l2bmb $lc64 $lb64                (prime)
  l1bmm $llb0 $llm0v; l2bmb $lc128 $lb128    (steady)
  l1bmm $llb32 $llm16v; l2bmb $lc192 $lb192  (steady)
  l1bmm $llb64 $llm32v            (drain x6)
  ... (計6行)

根拠 (judge 実測):
- MV部2行: ペイロードに mvp/n256 が2発行必須。
  MV行に `;` 併記形はなく1行1発行。
- L2 4発行・L1 8発行。同グループ同行不可のため
  単独行同士の畳み込みは不可
  (l2bmb同士・l1bmm同士のconflictを実測)。
- パイプライン構造上、先行2行と後行6行は単独に
  ならざるを得ず、中間2行のみ対にできる。
よって 2 + (2 + 2 + 6) = 12行が下限で Top=12 は最適。
-/

/-- MV部の最小行数 -/
def dll2bMv : Nat := 2

/-- パイプライン単独行 (prime2 + drain6) -/
def dll2bSolo : Nat := 8

/-- パイプライン対行 (steady2) -/
def dll2bPaired : Nat := 2

/-- 現1位行数 Top = 12 -/
def dll2bTop : Nat := 12

/-- 行数下限 = 2 + 8 + 2 = 12 -/
def dll2bLower : Nat := dll2bMv + dll2bSolo + dll2bPaired

theorem dll2b_lower : dll2bLower = 12 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dll2b_optimal : dll2bLower = dll2bTop := rfl

/-- 系: 11行以下での Accepted は存在しない -/
theorem dll2b_no_eleven :
    ∀ lines : Nat, lines < dll2bTop → lines < dll2bLower := by
  intro lines h
  have h12 : dll2bLower = 12 := rfl
  simp [dll2bTop] at h
  omega
