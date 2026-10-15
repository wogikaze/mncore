/-
全73問の集計 (Table / NegEvidence / GapClass の横断検算).

- 証明済み最適: 14 (Table の optimalProven)
- 新Top最適 (改善提出の最小性まで証明): 2 (34, 35)
- 未証明: 57 = near 11 + alg 26 + far 20
- 負証拠: 10種、証人15件
-/

import ProofsLean.Table
import ProofsLean.NegEvidence
import ProofsLean.GapClass

/-- 解決済み (最適証明または新Top最適) の問題数 -/
def resolved : Nat := 14 + 2

theorem resolved_count : resolved = 16 := rfl

/-- 未解決の問題数 -/
def unresolved : Nat := openProblems

theorem unresolved_count : unresolved = 57 := rfl

/-- 解決 + 未解決 = 全73問 -/
theorem resolved_unresolved : resolved + unresolved = 73 := by
  simp [resolved, unresolved, openProblems,
    nearGap, algGap, farGap]

/-- 負証拠の総数と証人数の再掲 -/
theorem summary_evidence : negEvidence + negWitnesses.length = 87 := by
  simp [negEvidence, rejectedPairs, requiredNops,
    lmWriteConflicts, orderConstraints, immAluConflict,
    mwriteMiscompute, doubleGap, wideMvLimit, negWitnesses]
