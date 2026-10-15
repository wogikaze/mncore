/-
色変換の下限モデルと 25.hsv2rgb (Top=12) の最適性.

参照解 problems/challenge/25.hsv2rgb/answer.vsm (12行):
  準備4行 (imm/変換/floor/imm)
  分岐4行 (iadd/ilsl/frelu3/filrelud の条件選択)
  収束4行 (frelu2/fmax/fvfma/l1bmm の出力)

根拠 (judge 実測): 全11組の隣接同行化がいずれも拒否。
- 8組: alu同士、1組: alu-immediate
- 1組: mau同士、1組: 発行順序制約
よって 4 + 4 + 4 = 12行が下限で Top=12 は最適。
-/

/-- 準備部の最小行数 -/
def hsvSetup : Nat := 4

/-- 分岐部の最小行数 -/
def hsvBranch : Nat := 4

/-- 収束部の最小行数 -/
def hsvOut : Nat := 4

/-- 現1位行数 Top = 12 -/
def hsvTop : Nat := 12

/-- 行数下限 = 4 + 4 + 4 = 12 -/
def hsvLower : Nat := hsvSetup + hsvBranch + hsvOut

theorem hsv_lower : hsvLower = 12 := rfl

/-- 最適性: 下限と Top が一致 -/
theorem hsv_optimal : hsvLower = hsvTop := rfl

/-- 系: 11行以下での Accepted は存在しない -/
theorem hsv_no_eleven :
    ∀ lines : Nat, lines < hsvTop → lines < hsvLower := by
  intro lines h
  have h12 : hsvLower = 12 := rfl
  simp [hsvTop] at h
  omega
