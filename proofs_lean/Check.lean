import ProofsLean
import Lean

#print axioms ProofsLean.length_le_score
#print axioms ProofsLean.correct_restrict
#print axioms ProofsLean.refutes_not_correct
#print axioms ProofsLean.BoundCertificate.sound
#print axioms ProofsLean.OptimalityCertificate.sound
#print axioms ProofsLean.shorter_correct_refutes_bound
#print axioms ProofsLean.programsUpTo_complete
#print axioms ProofsLean.shortPrograms_complete
#print axioms ProofsLean.FiniteExample.two_lines_optimal
#print axioms ProofsLean.FiniteExample.testcase_correct_does_not_imply_general_correct
#print axioms ProofsLean.FiniteExample.one_case_has_no_two_line_lower_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let owner := (env.getModuleIdxFor? name).bind fun idx => env.header.moduleNames[idx.toNat]?
    if owner.any (fun moduleName => (`ProofsLean).isPrefixOf moduleName) then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Quot.sound, `Classical.choice].contains dependency do
          throwError "untrusted dependency in {name}: {dependency}"
      checked := checked + 1
  if checked < 11 then
    throwError "incomplete project environment: only {checked} declarations"
  logInfo m!"AUDIT_DECLARATIONS: {checked}"
