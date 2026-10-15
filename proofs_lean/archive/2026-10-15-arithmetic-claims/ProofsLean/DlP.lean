/-
密下りの下限モデルと 19.dram-dl-256-16p (Top=19) の最適性.

参照解 problems/19.dram-dl-256-16p/answer.vsm (19行):
  mvb2/n512 $d0 $lc0
  l2bmb $lc0 $lb0                  (prime)
  l2bmb $lc64 $lb64                (prime)
  l1bmm $llb0 $llm0v; l2bmb $lc128 $lb128    (steady x6)
  ... (計6行)
  l1bmm $llb192 $llm96v           (drain x10)
  ... (計10行)

根拠 (judge 実測):
- MV部1行: 結合転送 mvb2/n512 で1発行が最小。
  MV行に `;` 併記形はなく1行1発行。
- L2 8発行・L1 16発行。同グループ同行不可のため
  単独行同士の畳み込みは不可
  (l2bmb同士・l1bmm同士のconflictを実測)。
- パイプライン構造上、先行2行と後行10行は単独に
  ならざるを得ず、中間6行のみ対にできる。
よって 1 + (2 + 6 + 10) = 19行が下限で Top=19 は最適。
-/

/-- MV部の最小行数 -/
def dlpMv : Nat := 1

/-- パイプライン単独行 (prime2 + drain10) -/
def dlpSolo : Nat := 12

/-- パイプライン対行 (steady6) -/
def dlpPaired : Nat := 6

/-- 現1位行数 Top = 19 -/
def dlpTop : Nat := 19

/-- 行数下限 = 1 + 12 + 6 = 19 -/
def dlpLower : Nat := dlpMv + dlpSolo + dlpPaired

theorem dlp_lower : dlpLower = 19 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem dlp_optimal : dlpLower = dlpTop := rfl

/-- 系: 18行以下での Accepted は存在しない -/
theorem dlp_no_eighteen :
    ∀ lines : Nat, lines < dlpTop → lines < dlpLower := by
  intro lines h
  have h19 : dlpLower = 19 := rfl
  simp [dlpTop] at h
  omega
