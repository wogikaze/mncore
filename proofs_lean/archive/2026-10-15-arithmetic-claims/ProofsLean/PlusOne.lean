import ProofsLean.LowerBound

/-
challenge/1.plus-one (16 Int に +1) の最適性.

仕様: problems/challenge/1.plus-one/problem.md:14-15
参照解: problems/challenge/1.plus-one/answer.vsm (2行)
検証:
- `iinc $llm0v $lln0v` → 8 correct, 8 mismatch
  (2長語動作 no のため半分が素通し)
- `iinc $lm0v $ln0v; iinc $lm8v $ln8v`
  → Instruction field conflict between `alu` and `alu`
- 2行参照解 → ACCEPTED score=2
-/

/-- plus-one の出力要素数 -/
def plusOneElems : Nat := 16

/-- 現1位行数 Top = 2 -/
def plusOneTop : Nat := 2

/-- 下限 = 2 (計算により確定) -/
theorem plusOne_lower : lineLowerBound plusOneElems = 2 := rfl

/-- 最適性: 下限と Top が一致する -/
theorem plusOne_optimal : lineLowerBound plusOneElems = plusOneTop := rfl

/-- 系: 1行での Accepted は存在しない.
    1行なら最大8要素しか計算できず、16要素中8要素が不一致になる.
    実測の 8 correct / 8 mismatch に対応. -/
theorem plusOne_no_one_line :
    ∀ lines : Nat, lines < plusOneTop → lines < lineLowerBound plusOneElems := by
  intro lines h
  simp [plusOneTop] at h
  simp [lineLowerBound, aluIssuesNeeded, intsPerStepALU,
    cyclesPerStep, intsPerCycleALU, maxALUPerStep, plusOneElems] at h ⊢
  omega
