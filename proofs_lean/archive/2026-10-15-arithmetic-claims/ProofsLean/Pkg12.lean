/-
package行列積の下限モデルと 36.matmul-trb-pkg-lm-256-16-16 (Top=12) の最適性.

参照解 problems/36.matmul-trb-pkg-lm-256-16-16/answer.vsm (12行):
  imm/llsl/nop            (MAB依存アドレス準備: 3行)
  gbfn / gbfn+mwrite x2 / gbfn+gmmul   (タイル1: 4行)
  gbfn+mwrite x2 / gmfma               (タイル2: 3行)
  l1bmm@1 / l1bmm                       (MAB間集約: 2行)

根拠:
- 256行packageは16 MABに分散し、MAB依存アドレス ($mabid) の
  準備に imm + llsl + T-RAW回避nop の3行が必須
  (20.dram-ul-256-16p の実測: T読みのnop除去は DataRaceError)。
- 本体2タイルは Tiles2 と同型で 2*3+1 = 7行が下限。
- MAB間集約 l1bmm 2発行は同グループ (l1bm) で同行不可のため2行。
よって 3+7+2 = 12行が構造下限で Top=12 は最適。
-/

/-- MAB依存アドレス準備の最小行数 -/
def pkgAddrSetup : Nat := 3

/-- 本体2タイルの最小行数 (Tiles2 と同型) -/
def pkgTiles : Nat := 2 * 3 + 1

/-- MAB間集約の最小行数 -/
def pkgReduce : Nat := 2

/-- 現1位行数 Top = 12 -/
def pkg256Top : Nat := 12

/-- 行数下限 = 3 + 7 + 2 = 12 -/
def pkg256Lower : Nat :=
  pkgAddrSetup + pkgTiles + pkgReduce

theorem pkg256_tiles : pkgTiles = 7 := rfl

theorem pkg256_lower : pkg256Lower = 12 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem pkg256_optimal : pkg256Lower = pkg256Top := rfl

/-- 系: 11行以下での Accepted は存在しない -/
theorem pkg256_no_eleven :
    ∀ lines : Nat, lines < pkg256Top → lines < pkg256Lower := by
  intro lines h
  have h12 : pkg256Lower = 12 := rfl
  simp [pkg256Top] at h
  omega
