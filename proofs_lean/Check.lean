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
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedRegisterStep_success
#print axioms ProofsLean.MNCore.PEMemory.mask_directive_replaces_selection_preserves_context
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedLineStep_prepares_then_commits
#print axioms ProofsLean.MNCore.PEMemory.parsedMaskedSource_execution
#print axioms ProofsLean.MNCore.PEMemory.parsedMaskedSource_score
#print axioms ProofsLean.MNCore.PEMemory.mask_directive_has_zero_issue_cost
#print axioms ProofsLean.MNCore.PEMemory.parsed_wait_expression_preserves_register_state
#print axioms ProofsLean.MNCore.PEMemory.parsed_noforward_suppresses_forwarding_updates
#print axioms ProofsLean.MNCore.PEMemory.parsed_nop_preserves_register_state
#print axioms ProofsLean.MNCore.PEMemory.parsed_nop_count_has_matching_issue_cost
#print axioms ProofsLean.MNCore.PEMemory.parsed_nop_line_lowers_to_count_issue_words
#print axioms ProofsLean.MNCore.PEMemory.parsed_line_lowering_preserves_issue_words
#print axioms ProofsLean.MNCore.PEMemory.lowered_parsed_masked_source_executes_as_normalized
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
#print axioms ProofsLean.MNCore.Issue.zero_has_execution_request
#print axioms ProofsLean.MNCore.Issue.immediate_has_execution_request
#print axioms ProofsLean.MNCore.Issue.zero_execution_ignores_inputs
#print axioms ProofsLean.MNCore.Issue.integer_request_is_execution_request
#print axioms ProofsLean.MNCore.Issue.immediate_execution_ignores_inputs
#print axioms ProofsLean.MNCore.Issue.parsed_topline_check_sound
#print axioms ProofsLean.MNCore.Issue.parsed_topline_check_complete
#print axioms ProofsLean.MNCore.Issue.mask_directive_replaces_state
#print axioms ProofsLean.MNCore.Issue.ordinary_line_preserves_mask_state
#print axioms ProofsLean.ControlNormalization.compile_length
#print axioms ProofsLean.ControlNormalization.run_compiles
#print axioms ProofsLean.ControlNormalization.source_execution
#print axioms ProofsLean.ControlNormalization.source_score
#print axioms ProofsLean.ControlNormalization.compileAdvancing_length
#print axioms ProofsLean.ControlNormalization.run_compiles_advancing
#print axioms ProofsLean.ControlNormalization.source_execution_advancing
#print axioms ProofsLean.ControlNormalization.source_score_advancing
#print axioms ProofsLean.MNCore.PEMemory.prepareParsedMaskedConstantWrites_preserves_order
#print axioms ProofsLean.MNCore.PEMemory.commit_constant_omr_destination_writes_zero
#print axioms ProofsLean.MNCore.PEMemory.ParsedIntegerContext.linearIndex_lt
#print axioms ProofsLean.MNCore.PEMemory.ParsedIntegerContext.linearIndex_ofLinearIndex
#print axioms ProofsLean.MNCore.PEMemory.parsed_fixed_integerValue_ofLinearIndex
#print axioms ProofsLean.MNCore.Issue.ParsedAluName.inputCount_positive
#print axioms ProofsLean.MNCore.PEMemory.parsed_fixed_integer_input
#print axioms ProofsLean.MNCore.PEMemory.parsed_integer_memory_input_ignores_negation_extension
#print axioms ProofsLean.MNCore.PEMemory.readRegisterBank_t_reads_all_four_words
#print axioms ProofsLean.MNCore.PEMemory.readRegisterBank_t_independent_of_width
#print axioms ProofsLean.MNCore.PEMemory.roundNearestEven_tie_even
#print axioms ProofsLean.MNCore.PEMemory.roundNearestEven_tie_odd
#print axioms ProofsLean.MNCore.PEMemory.roundSingleInputBusToHalf_lane0
#print axioms ProofsLean.MNCore.PEMemory.roundSingleInputBusToHalf_lane1
#print axioms ProofsLean.MNCore.PEMemory.roundSingleInputBusToHalf_lane2
#print axioms ProofsLean.MNCore.PEMemory.roundSingleInputBusToHalf_lane3
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerInput_read_rounded
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerInput_read_unrounded
#print axioms ProofsLean.MNCore.PEMemory.parsed_forward_integer_input
#print axioms ProofsLean.MNCore.PEMemory.parsed_forward_expr_lowering
#print axioms ProofsLean.MNCore.PEMemory.executeParsedMaskedIntegerExprWithForwarding?_uses_lowering
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerInput_forward_known
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerInput_forward_poison_fails
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerInput_forward_unknown_stays_unknown
#print axioms ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding_resolved
#print axioms ProofsLean.MNCore.PEMemory.commitParsedMaskedWrites_single_memory
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedRegisterStepWithForwarding_resolves_to_fixed
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedRegisterStepWithForwarding_success
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedLineStepWithForwarding_prepares_then_commits
#print axioms ProofsLean.MNCore.PEMemory.updateParsedIntegerALUForwardingCycle_reads_back
#print axioms ProofsLean.MNCore.PEMemory.updateParsedIntegerALUForwardingCycle_semantics
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixRead_mreadf_readback
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixReadBus_physical_layout
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixWriteRowWords_high_word
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixWriteRowWords_low_word
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixRead_after_transposed_write
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixStore_write_readback
#print axioms ProofsLean.MNCore.PEMemory.singleMatrixReadBus_physical_layout
#print axioms ProofsLean.MNCore.PEMemory.halfMatrixReadBus_physical_layout
#print axioms ProofsLean.MNCore.PEMemory.writeMatrixReadOutputs_semantics
#print axioms ProofsLean.MNCore.PEMemory.updateParsedMatrixReadForwardingCycle_reads_back
#print axioms ProofsLean.MNCore.PEMemory.parsedMatrixReadCycleStep_output_forwardable
#print axioms ProofsLean.MNCore.PEMemory.parsedIntegerMaskedALUAndForwardingCycleStep_prepares_once
#print axioms ProofsLean.MNCore.PEMemory.parsed_issue_advances_elapsed_word
#print axioms ProofsLean.MNCore.PEMemory.parsed_issue_line_mask_flag_iff
#print axioms ProofsLean.MNCore.PEMemory.parsed_issue_line_mask_cancels_unmasked_memory_target
#print axioms ProofsLean.MNCore.PEMemory.parsed_issue_advances_absolute_cycle
#print axioms ProofsLean.MNCore.PEMemory.parsed_source_clock_matches_issue_cost
#print axioms ProofsLean.MNCore.PEMemory.parsed_source_access_clock_matches_issue_cost
#print axioms ProofsLean.MNCore.PEMemory.lm_pe_hazard_requires_three_issue_words
#print axioms ProofsLean.MNCore.PEMemory.grf_t_pe_hazard_requires_seven_cycles
#print axioms ProofsLean.MNCore.PEMemory.lm_pe_hazard_satisfied_after_three_words
#print axioms ProofsLean.MNCore.PEMemory.grf_t_pe_hazard_satisfied_after_seven_cycles
#print axioms ProofsLean.MNCore.PEMemory.parsed_mask_pattern_controls_hazard_write_cycle
#print axioms ProofsLean.MNCore.PEMemory.parsed_mask_entry_keeps_all_hazard_write_cycles
#print axioms ProofsLean.MNCore.PEMemory.t_indirect_hazard_access_uses_cycle_region
#print axioms ProofsLean.MNCore.PEMemory.pe_hazard_constraint_uses_rule_distance
#print axioms ProofsLean.MNCore.PEMemory.pe_hazard_violation_filter_exact
#print axioms ProofsLean.MNCore.PEMemory.pe_hazard_constraints_between_complete
#print axioms ProofsLean.MNCore.PEMemory.pe_hazard_constraint_violation_matches_pair_safety

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
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixWriteCycle_readback
#print axioms ProofsLean.MNCore.PEMemory.prepareParsedDoubleMatrixWritePEs_all
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixWriteCycle_readback_of_pe_reads
#print axioms ProofsLean.MNCore.PEMemory.doubleMatrixWriteRowAt_injective
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixStore_other_write_preserves_readback
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixStore_four_rows_readback
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixWriteFourCycle_store
#print axioms ProofsLean.MNCore.PEMemory.parsedDoubleMatrixWriteFourCycle_readback
