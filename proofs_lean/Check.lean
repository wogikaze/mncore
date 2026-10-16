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
#print axioms ProofsLean.MNCore.PlusOne.answer_correct
#print axioms ProofsLean.MNCore.PlusOne.answer_optimal_in_restricted_model
#print axioms ProofsLean.MNCore.PlusOne.increment_pair_spec
#print axioms ProofsLean.MNCore.PlusOne.bus_word_eq_increment
#print axioms ProofsLean.MNCore.PlusOne.cycle_read_high
#print axioms ProofsLean.MNCore.PlusOne.cycle_read_low
#print axioms ProofsLean.MNCore.PlusOne.cycle_alu_output
#print axioms ProofsLean.MNCore.PlusOne.step_writes_cycle_output_high
#print axioms ProofsLean.MNCore.PlusOne.step_writes_cycle_output_low
#print axioms ProofsLean.MNCore.PlusOne.increment_numerical
#print axioms ProofsLean.MNCore.Issue.check_sound
#print axioms ProofsLean.MNCore.Issue.check_complete
#print axioms ProofsLean.MNCore.Issue.duplicate_alu_groups_rejected
#print axioms ProofsLean.MNCore.Issue.projectLine_idsUnique
#print axioms ProofsLean.MNCore.Issue.parsed_check_sound
#print axioms ProofsLean.MNCore.Issue.plusOne_issue_accepts
#print axioms ProofsLean.MNCore.Issue.mismatched_fma_matrix_write_rejected
#print axioms ProofsLean.MNCore.Issue.projected_reads_are_mem_operands
#print axioms ProofsLean.MNCore.Issue.projected_writes_are_mem_operands
#print axioms ProofsLean.MNCore.Issue.projected_group_is_parser_group
#print axioms ProofsLean.MNCore.Issue.projected_mau_is_parser_mau
#print axioms ProofsLean.MNCore.Issue.ParsedPrecision.code_injective
#print axioms ProofsLean.MNCore.Issue.unsupported_parsed_integer_is_unknown
#print axioms ProofsLean.MNCore.Issue.iinc_integer_request
#print axioms ProofsLean.MNCore.Issue.supported_integer_opcode_has_mapping
#print axioms ProofsLean.MNCore.Issue.iinc_evaluation_is_integer_alu
#print axioms ProofsLean.MNCore.Issue.parsed_integer_evaluation_uses_requested_semantics
#print axioms ProofsLean.MNCore.Issue.parsed_float_rsqrt_is_unknown
#print axioms ProofsLean.MNCore.PEMemory.pack_unpackALUBus
#print axioms ProofsLean.MNCore.PEMemory.readRegisterBank_after_write
#print axioms ProofsLean.MNCore.PEMemory.readDirectAccessMasked_after_write
#print axioms ProofsLean.MNCore.PEMemory.direct_access_write_readback
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerRegisterStep_succeeds
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerRegisterStep_readback
#print axioms ProofsLean.MNCore.PEMemory.executeParsedIntegerExpr_readback
#print axioms ProofsLean.MNCore.PEMemory.parsed_iinc_output_eq_incrementPair
#print axioms ProofsLean.MNCore.PEMemory.integerFlagsVector_bit0
#print axioms ProofsLean.MNCore.PEMemory.integerFlagsVector_bit1
#print axioms ProofsLean.MNCore.PEMemory.integerFlagsVector_bit2
#print axioms ProofsLean.MNCore.PEMemory.integerFlagsVector_bit3
#print axioms ProofsLean.MNCore.PEMemory.mask_read_after_writeRegister
#print axioms ProofsLean.MNCore.PEMemory.mask_read_after_selected_write
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskStep_readback
#print axioms ProofsLean.MNCore.PEMemory.executeParsedIntegerMaskExpr_readback
#print axioms ProofsLean.MNCore.PEMemory.selectedWordMask_allOnes
#print axioms ProofsLean.MNCore.PEMemory.writeWordsMasked_allOnes
#print axioms ProofsLean.MNCore.PEMemory.readWordsMasked_after_allOnes
#print axioms ProofsLean.MNCore.PEMemory.selectedWordMask_zero_high
#print axioms ProofsLean.MNCore.PEMemory.selectedWordMask_zero_lowLong
#print axioms ProofsLean.MNCore.PEMemory.writeWordsMasked_at
#print axioms ProofsLean.MNCore.PEMemory.writeWordsMasked_preserves_outside
#print axioms ProofsLean.MNCore.PEMemory.zeroLongMask_on_double_access
#print axioms ProofsLean.MNCore.PEMemory.single_line_mask_cancels_omr_directive
#print axioms ProofsLean.MNCore.PEMemory.own_omr_mask_precedes_multiline_directive
#print axioms ProofsLean.MNCore.PEMemory.own_memory_mask_precedes_multiline_directive
#print axioms ProofsLean.MNCore.PEMemory.single_line_mask_cancels_memory_directive
#print axioms ProofsLean.MNCore.PEMemory.untargeted_memory_uses_unmasked_selection
#print axioms ProofsLean.MNCore.Issue.parsed_topline_check_sound
#print axioms ProofsLean.MNCore.Issue.parsed_topline_check_complete
#print axioms ProofsLean.MNCore.Issue.mask_directive_replaces_state
#print axioms ProofsLean.MNCore.Issue.ordinary_line_preserves_mask_state
#print axioms ProofsLean.ControlNormalization.compile_length
#print axioms ProofsLean.ControlNormalization.run_compiles
#print axioms ProofsLean.ControlNormalization.source_execution
#print axioms ProofsLean.ControlNormalization.source_score

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
