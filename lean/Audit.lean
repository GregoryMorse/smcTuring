module
import SmcTuring
import Solution

#print axioms SmcTuring.Defaddr.corrected_effect
#print axioms SmcTuring.Defaddr.arbitrary_repetitions_restore_memory
#print axioms SmcTuring.Defaddr.repair_equivalent
#print axioms SmcTuring.Defaddr.original_not_pure
#print axioms SmcTuring.Defaddr.corrected_pure
#print axioms SmcTuring.Defaddr.repair32
#print axioms SmcTuring.Defaddr.repair64
#print axioms SmcTuring.Defaddr.arbitrary_repetitions_pure
#print axioms SmcTuring.Dolan.compare_correct
#print axioms SmcTuring.Dolan.select_correct
#print axioms SmcTuring.Dolan.sentinel_compare_correct
#print axioms SmcTuring.Dolan.halt_address_zero_iff
#print axioms SmcTuring.Dolan.nonmatch_preserves_registers
#print axioms SmcTuring.Dolan.move_left_correct
#print axioms SmcTuring.Dolan.move_right_correct
#print axioms SmcTuring.Dolan.Mov.load_correct
#print axioms SmcTuring.Dolan.Mov.store_correct
#print axioms SmcTuring.Dolan.Mov.offset_dereference_traps
#print axioms SmcTuring.Dolan.Mov.run_composition
#print axioms SmcTuring.Dolan.Mov.comparison_correct
#print axioms SmcTuring.Dolan.Mov.selection_correct
#print axioms SmcTuring.TM.transition_correct
#print axioms SmcTuring.TM.halt_not_diverge
#print axioms SmcTuring.TM.diverges_iff_not_halts
#print axioms SmcTuring.Dolan.Mov.push_program_correct
#print axioms SmcTuring.Dolan.Mov.pop_program_correct
#print axioms SmcTuring.Dolan.Encoding.write_preserves_memory
#print axioms SmcTuring.Dolan.Encoding.move_preserves_memory
#print axioms SmcTuring.Dolan.Encoding.scratch_preserves_memory
#print axioms SmcTuring.Dolan.Encoding.neighbor_link
#print axioms SmcTuring.Dolan.Encoding.move_program_correct
#print axioms SmcTuring.Dolan.Encoding.zigzag_injective
#print axioms SmcTuring.Dolan.Encoding.unzigzag_zigzag
#print axioms SmcTuring.Dolan.Encoding.encoded_memory_correct
#print axioms SmcTuring.Dolan.Encoding.initial_tape_correct
#print axioms SmcTuring.Dolan.Mov.pop_direction_program_correct
#print axioms SmcTuring.Dolan.Encoding.advance_program_correct
#print axioms SmcTuring.Dolan.Mov.write_program_correct
#print axioms SmcTuring.Dolan.Encoding.symbol_result_represents
#print axioms SmcTuring.Dolan.Encoding.selected_write_program_correct
#print axioms SmcTuring.Dolan.Encoding.tape_step_program_correct
#print axioms SmcTuring.Dolan.Mov.run_register_frame
#print axioms SmcTuring.Dolan.Mov.run_read_only
#print axioms SmcTuring.Dolan.Mov.guard_traps_iff
#print axioms SmcTuring.Dolan.Mov.guard_memory_frame
#print axioms SmcTuring.Dolan.Table.entries_sound
#print axioms SmcTuring.Dolan.Table.entries_complete
#print axioms SmcTuring.Dolan.Table.entries_length
#print axioms SmcTuring.Dolan.Table.missing_transition_iff
#print axioms SmcTuring.Dolan.Table.table_memory_correct
#print axioms SmcTuring.Dolan.Table.initial_table_correct
#print axioms SmcTuring.Dolan.Table.initial_memory_tape_correct
#print axioms SmcTuring.Dolan.Mov.load_candidate_correct
#print axioms SmcTuring.Dolan.Mov.load_symbol_correct
#print axioms SmcTuring.Dolan.Mov.load_direction_correct
#print axioms SmcTuring.Dolan.Mov.load_cursor_choices_correct
#print axioms SmcTuring.Dolan.Mov.update_cursor_correct
#print axioms SmcTuring.Dolan.Mov.write_value_correct
#print axioms SmcTuring.Dolan.Mov.write_result_frame
#print axioms SmcTuring.Dolan.Mov.match_candidate_correct
#print axioms SmcTuring.Dolan.Mov.advance_exact
#print axioms SmcTuring.Dolan.Mov.advance_result_frame
#print axioms SmcTuring.Dolan.Mov.guard_runtime
#print axioms SmcTuring.Dolan.Mov.match_runtime
#print axioms SmcTuring.Dolan.Mov.symbol_runtime
#print axioms SmcTuring.Dolan.Mov.write_runtime
#print axioms SmcTuring.Dolan.Mov.direction_runtime
#print axioms SmcTuring.Dolan.Mov.advance_runtime
#print axioms SmcTuring.Dolan.Mov.cursor_runtime
#print axioms SmcTuring.Dolan.Mov.kernel_candidate_correct
#print axioms SmcTuring.Dolan.Mov.kernel_sentinel_traps
#print axioms SmcTuring.Dolan.Mov.scan_iteration
#print axioms SmcTuring.Dolan.Mov.exhausted_halts
#print axioms SmcTuring.Dolan.Mov.scan_rank_decreases
#print axioms SmcTuring.Dolan.Mov.initial_scan_correct
#print axioms SmcTuring.Dolan.Mov.scan_resolves
#print axioms SmcTuring.Dolan.Mov.simulate_step
#print axioms SmcTuring.Dolan.Mov.simulate_halt
#print axioms SmcTuring.Dolan.Mov.scan_success_semantic
#print axioms SmcTuring.Dolan.Mov.kernel_fault_reflects
#print axioms SmcTuring.Dolan.Mov.simulate_run
#print axioms SmcTuring.Dolan.Mov.kernel_halt_reflected
#print axioms SmcTuring.Dolan.Mov.kernel_halting_iff
#print axioms SmcTuring.Dolan.Mov.kernel_divergence_iff
#print axioms SmcTuring.Dolan.Mov.fixed_mov_simulation
#print axioms SmcTuring.Dolan.Four.initial_coherent
#print axioms SmcTuring.Dolan.Four.spill_coherent
#print axioms SmcTuring.Dolan.Four.heap_store_coherent
#print axioms SmcTuring.Dolan.Four.distance_correct
#print axioms SmcTuring.Dolan.Four.ring_loads_correct
#print axioms SmcTuring.Dolan.Four.walk_correct
#print axioms SmcTuring.Dolan.Four.fetch_correct
#print axioms SmcTuring.Dolan.Four.fetch_result_coherent
#print axioms SmcTuring.Dolan.Four.spill_correct
#print axioms SmcTuring.Dolan.Four.spill_result_coherent
#print axioms SmcTuring.Dolan.Four.reset_coherent
#print axioms SmcTuring.Dolan.Four.compile_instruction_correct
#print axioms SmcTuring.Dolan.Four.compile_instruction_fault
#print axioms SmcTuring.Dolan.Four.compile_run
#print axioms SmcTuring.Dolan.Four.compile_fault_iff
#print axioms SmcTuring.Dolan.Four.repeat_compiles
#print axioms SmcTuring.Dolan.Four.compiled_halting_iff
#print axioms SmcTuring.Dolan.Four.compiled_divergence_iff
#print axioms SmcTuring.Dolan.Four.four_register_mov_simulation
#print axioms SmcTuring.Dolan.Four.kernel_length
#print axioms SmcTuring.SMC.every_instruction_writes
#print axioms SmcTuring.SMC.execute_memory_frame
#print axioms SmcTuring.SMC.fetch_storage_current_word
#print axioms SmcTuring.SMC.patched_operand_changes_fetch
#print axioms SmcTuring.SMC.pure_append
#print axioms SmcTuring.SMC.read_correct
#print axioms SmcTuring.SMC.read_pure
#print axioms SmcTuring.SMC.stack_reset_correct
#print axioms SmcTuring.SMC.reset_call_correct
#print axioms SmcTuring.SMC.reset_call_pure
#print axioms SmcTuring.SMC.indexed_address_correct
#print axioms SmcTuring.SMC.flags_below_heap
#print axioms SmcTuring.SMC.metadata_write_frame
#print axioms SmcTuring.SMC.register_write_rep
#print axioms SmcTuring.SMC.heap_write_rep
#print axioms SmcTuring.SMC.select_word
#print axioms SmcTuring.SMC.reset_call_operand_correct
#print axioms SmcTuring.SMC.reset_call_operand_pure
#print axioms SmcTuring.SMC.field_address_injective
#print axioms SmcTuring.SMC.heap_field_injective
#print axioms SmcTuring.SMC.register_field_injective
#print axioms SmcTuring.SMC.encode_word_injective
#print axioms SmcTuring.SMC.copy_correct
#print axioms SmcTuring.SMC.copy_pure
#print axioms SmcTuring.SMC.borrow_mask_correct
#print axioms SmcTuring.SMC.borrow_mask_pure
#print axioms SmcTuring.SMC.xor_program_correct
#print axioms SmcTuring.SMC.and_program_correct
#print axioms SmcTuring.SMC.xor_program_pure
#print axioms SmcTuring.SMC.and_program_pure
#print axioms SmcTuring.SMC.compare_program_correct
#print axioms SmcTuring.SMC.compare_program_pure
#print axioms SmcTuring.SMC.selection_program_correct
#print axioms SmcTuring.SMC.selection_program_pure
#print axioms SmcTuring.SMC.Lowering.static_write_frame
#print axioms SmcTuring.SMC.Lowering.pointer_rep
#print axioms SmcTuring.SMC.Lowering.register_rep
#print axioms SmcTuring.SMC.Lowering.heap_rep
#print axioms SmcTuring.SMC.Lowering.address_program_correct
#print axioms SmcTuring.SMC.Lowering.address_result_rep
#print axioms SmcTuring.SMC.Lowering.address_program_pure
#print axioms SmcTuring.SMC.Lowering.immediate_correct
#print axioms SmcTuring.SMC.Lowering.load_correct
#print axioms SmcTuring.SMC.Lowering.store_correct
#print axioms SmcTuring.SMC.Lowering.instruction_correct
#print axioms SmcTuring.SMC.Lowering.compile_run
#print axioms SmcTuring.SMC.linear_image_execution
#print axioms SmcTuring.SMC.pure_run_mono
#print axioms SmcTuring.SMC.Lowering.compile_non_branching
#print axioms SmcTuring.SMC.Lowering.compile_image_run
#print axioms SmcTuring.SMC.boundary_change_has_instruction_change
#print axioms SmcTuring.SMC.guard_compare_correct
#print axioms SmcTuring.SMC.guard_mask_correct
#print axioms SmcTuring.SMC.guard_selection_correct
#print axioms SmcTuring.SMC.guard_program_correct
#print axioms SmcTuring.SMC.guard_program_pure
#print axioms SmcTuring.SMC.guard_memory_frame
#print axioms SmcTuring.SMC.guard_numeric_rep
#print axioms SmcTuring.SMC.guard_typed_address_correct
#print axioms SmcTuring.SMC.run_image_add
#print axioms SmcTuring.SMC.pure_steps_composition
#print axioms SmcTuring.SMC.image_single
#print axioms SmcTuring.SMC.reset_call_image
#print axioms SmcTuring.SMC.read_routine_correct
#print axioms SmcTuring.SMC.read_routine_store_tail
#print axioms SmcTuring.SMC.store_routine_correct
#print axioms SmcTuring.SMC.encode_word_below_heap_iff
#print axioms SmcTuring.SMC.encode_word_after_heap_iff
#print axioms SmcTuring.SMC.mov_address_none_iff
#print axioms SmcTuring.SMC.guard_offset_tag_correct
#print axioms SmcTuring.SMC.Virtual.register_field_injective
#print axioms SmcTuring.SMC.Virtual.register_heap_separate
#print axioms SmcTuring.SMC.Virtual.metadata_write_frame
#print axioms SmcTuring.SMC.Virtual.register_write_rep
#print axioms SmcTuring.SMC.Virtual.heap_write_rep
#print axioms SmcTuring.SMC.Virtual.field_index_correct
#print axioms SmcTuring.SMC.Virtual.data_state_correct
#print axioms SmcTuring.SMC.Virtual.read_invocation_rep
#print axioms SmcTuring.SMC.Virtual.store_invocation_rep
#print axioms SmcTuring.SMC.Virtual.read_register_routine
#print axioms SmcTuring.SMC.read_then_instruction
#print axioms SmcTuring.SMC.read_copy_correct
#print axioms SmcTuring.SMC.read_copy_frame
#print axioms SmcTuring.SMC.Virtual.read_copy_register_rep
#print axioms SmcTuring.SMC.ReadCallReady.correct
#print axioms SmcTuring.SMC.ReadCallReady.copy
#print axioms SmcTuring.SMC.Virtual.immediate_image_correct
#print axioms SmcTuring.SMC.Virtual.load_image_correct
#print axioms SmcTuring.SMC.Virtual.store_image_correct
#print axioms SmcTuring.SMC.Virtual.mov_address_two_tests
#print axioms SmcTuring.SMC.image_boundary_change_has_instruction_change
#print axioms SmcTuring.SMC.Virtual.represented_register_change
#print axioms SmcTuring.SMC.Concrete.static_reader_label
#print axioms SmcTuring.SMC.Concrete.static_reader_target_code
#print axioms SmcTuring.SMC.Concrete.static_reader_target_separate
#print axioms SmcTuring.SMC.Concrete.call_ready
#print axioms SmcTuring.SMC.Concrete.static_call_ready
#print axioms SmcTuring.SMC.Concrete.read_static_frame
#print axioms SmcTuring.SMC.Concrete.read_source_frame
#print axioms SmcTuring.SMC.Concrete.static_read_image
#print axioms SmcTuring.SMC.Concrete.guard_entry_effect
#print axioms SmcTuring.SMC.Concrete.guard_entry_static
#print axioms SmcTuring.SMC.Concrete.guard_entry_source
#print axioms SmcTuring.SMC.Concrete.guard_entry_execute
#print axioms SmcTuring.SMC.Concrete.guard_invocation_execute
#print axioms SmcTuring.SMC.Concrete.guard_invocation_source
#print axioms SmcTuring.SMC.Concrete.guard_invocation_pc
#print axioms SmcTuring.SMC.Concrete.guard_invocation_terminal_iff
#print axioms SmcTuring.SMC.Concrete.terminal_observation
#print axioms SmcTuring.SMC.Concrete.guard_prefix_selected
#print axioms SmcTuring.SMC.Concrete.guard_target_pc
#print axioms SmcTuring.SMC.Concrete.guard_returns_iff
#print axioms SmcTuring.SMC.Concrete.guard_terminal_iff
#print axioms SmcTuring.SMC.Concrete.Executes.trans
#print axioms SmcTuring.SMC.Concrete.metadata_source_frame
#print axioms SmcTuring.SMC.Concrete.guard_capture_effect
#print axioms SmcTuring.SMC.Concrete.guard_capture_pc
#print axioms SmcTuring.SMC.Concrete.guard_capture_static
#print axioms SmcTuring.SMC.Concrete.guard_capture_source
#print axioms SmcTuring.SMC.Concrete.guard_capture_execute
#print axioms SmcTuring.SMC.Concrete.guard_read_pc
#print axioms SmcTuring.SMC.Concrete.guard_read_static
#print axioms SmcTuring.SMC.Concrete.guard_read_source
#print axioms SmcTuring.SMC.Concrete.guard_read_execute
#print axioms SmcTuring.SMC.Concrete.guard_sbb_pc
#print axioms SmcTuring.SMC.Concrete.guard_sbb_static
#print axioms SmcTuring.SMC.Concrete.guard_sbb_source
#print axioms SmcTuring.SMC.Concrete.guard_sbb_execute
#print axioms SmcTuring.SMC.Concrete.guard_call_effect
#print axioms SmcTuring.SMC.Concrete.guard_call_static
#print axioms SmcTuring.SMC.Concrete.guard_call_source
#print axioms SmcTuring.SMC.Concrete.guard_call_execute
#print axioms SmcTuring.SMC.Concrete.guard_prefix_execute
#print axioms SmcTuring.SMC.Concrete.guard_prefix_source
#print axioms SmcTuring.SMC.Concrete.guard_execute
#print axioms SmcTuring.SMC.Concrete.guard_source_frame
#print axioms SmcTuring.SMC.Concrete.kernel_supported
#print axioms SmcTuring.SMC.Concrete.reader_length
#print axioms SmcTuring.SMC.Concrete.guard_length
#print axioms SmcTuring.SMC.Concrete.reader_header
#print axioms SmcTuring.SMC.Concrete.guard_header
#print axioms SmcTuring.SMC.Concrete.data_owner
#print axioms SmcTuring.SMC.Concrete.metadata_owner
#print axioms SmcTuring.SMC.Concrete.meta_is_code
#print axioms SmcTuring.SMC.Concrete.data_is_code
#print axioms SmcTuring.SMC.Concrete.metadata_outside_data
#print axioms SmcTuring.SMC.Concrete.source_register_field
#print axioms SmcTuring.SMC.Concrete.storage_owner_injective
#print axioms SmcTuring.SMC.Concrete.unbounded_storage
#print axioms SmcTuring.SMC.Concrete.reader_placement
#print axioms SmcTuring.SMC.Concrete.kernel_length_bound
#print axioms SmcTuring.SMC.Concrete.terminal_missing
#print axioms SmcTuring.SMC.Concrete.metadata_field_injective
#print axioms SmcTuring.SMC.Concrete.initialized_metadata
#print axioms SmcTuring.SMC.Concrete.initial_static
#print axioms SmcTuring.SMC.Concrete.data_nonnegative
#print axioms SmcTuring.SMC.Concrete.initial_rep
#print axioms SmcTuring.SMC.Concrete.static_write_frame
#print axioms SmcTuring.SMC.Concrete.static_dynamic_write
#print axioms SmcTuring.SMC.Concrete.static_data_write
#print axioms SmcTuring.SMC.Concrete.static_top
#print axioms SmcTuring.SMC.Concrete.static_capture
#print axioms SmcTuring.SMC.Concrete.initial_register_reader
#print axioms SmcTuring.SMC.linear_at_indexed
#print axioms SmcTuring.SMC.linear_at_append
#print axioms SmcTuring.SMC.Concrete.kernel_header
#print axioms SmcTuring.SMC.Concrete.kernel_subblock
#print axioms SmcTuring.SMC.Concrete.kernel_placement
#print axioms SmcTuring.SMC.Concrete.guard_subblock
#print axioms SmcTuring.SMC.Concrete.guard_read_site
#print axioms SmcTuring.SMC.Concrete.guard_read_bounded
#print axioms SmcTuring.SMC.Concrete.guard_read_code
#print axioms SmcTuring.SMC.Concrete.guard_read_dynamic
#print axioms SmcTuring.SMC.Concrete.guard_read_outside
#print axioms SmcTuring.SMC.Concrete.guard_capture_site
#print axioms SmcTuring.SMC.Concrete.guard_sbb_site
#print axioms SmcTuring.SMC.Concrete.guard_final_call_site
#print axioms SmcTuring.SMC.Concrete.operation_writes
#print axioms SmcTuring.SMC.Concrete.operation_static_frame
#print axioms SmcTuring.SMC.Concrete.read_op_static_frame
#print axioms SmcTuring.SMC.Concrete.read_op_correct
#print axioms SmcTuring.SMC.Concrete.read_op_pc
#print axioms SmcTuring.SMC.Concrete.read_op_acc
#print axioms SmcTuring.SMC.Concrete.read_op_memory_frame
#print axioms SmcTuring.SMC.Concrete.read_op_source_frame
#print axioms SmcTuring.SMC.Concrete.initial_tm_static
#print axioms SmcTuring.SMC.Concrete.initial_tm_rep
#print axioms SmcTuring.SMC.Concrete.guard_invocation_memory_frame
#print axioms SmcTuring.SMC.Concrete.guard_read_memory_frame
#print axioms SmcTuring.SMC.Concrete.guard_capture_memory_frame
#print axioms SmcTuring.SMC.Concrete.guard_sbb_memory_frame
#print axioms SmcTuring.SMC.Concrete.guard_prefix_memory_frame
#print axioms SmcTuring.SMC.Concrete.guard_memory_frame
#print axioms SmcTuring.SMC.Concrete.offset_guard_correct
#print axioms SmcTuring.SMC.Concrete.address_prefix_correct
#print axioms SmcTuring.SMC.Concrete.valid_address_tests
#print axioms SmcTuring.SMC.Concrete.address_success
#print axioms SmcTuring.SMC.Concrete.address_fault
#print axioms SmcTuring.SMC.Concrete.changes_in_steps_event
#print axioms SmcTuring.SMC.Concrete.code_change_after
#print axioms SmcTuring.SMC.Concrete.tm_step_moves_head
#print axioms SmcTuring.SMC.Concrete.configuration_current_changes
#print axioms SmcTuring.SMC.Concrete.divergent_tm_infinitely_changes
#print axioms SmcTuring.SMC.Concrete.pure_infinitely_smc_universality
#print axioms SmcTuring.SMC.Concrete.instruction_count_positive
#print axioms SmcTuring.SMC.Concrete.instruction_success
#print axioms SmcTuring.SMC.Concrete.instruction_fault
#print axioms SmcTuring.SMC.Concrete.source_register_nonnegative
#print axioms SmcTuring.SMC.Concrete.source_register_code
#print axioms SmcTuring.SMC.Concrete.read_op_data_static
#print axioms SmcTuring.SMC.Concrete.immediate_loaded
#print axioms SmcTuring.SMC.Concrete.read_op_assign_register_rep
#print axioms SmcTuring.SMC.Concrete.read_op_dynamic_correct
#print axioms SmcTuring.SMC.Concrete.immediate_success
#print axioms SmcTuring.SMC.Concrete.load_success
#print axioms SmcTuring.SMC.Concrete.kernel_count_positive
#print axioms SmcTuring.SMC.Concrete.kernel_sites
#print axioms SmcTuring.SMC.Concrete.static_loop_target
#print axioms SmcTuring.SMC.Concrete.loop_call_effect
#print axioms SmcTuring.SMC.Concrete.loop_call_static
#print axioms SmcTuring.SMC.Concrete.loop_call_source
#print axioms SmcTuring.SMC.Concrete.loop_call_execute
#print axioms SmcTuring.SMC.Concrete.kernel_success
#print axioms SmcTuring.SMC.Concrete.kernel_fault
#print axioms SmcTuring.SMC.Concrete.static_register_reader
#print axioms SmcTuring.SMC.Concrete.register_reader_value
#print axioms SmcTuring.SMC.Concrete.read_op_metadata_static
#print axioms SmcTuring.SMC.Concrete.read_op_metadata_source
#print axioms SmcTuring.SMC.Concrete.read_op_assign_value
#print axioms SmcTuring.SMC.Concrete.read_op_add_value
#print axioms SmcTuring.SMC.Concrete.guard_candidate_frame
#print axioms SmcTuring.SMC.Concrete.guard_pointer_frame
#print axioms SmcTuring.SMC.Concrete.read_op_length
#print axioms SmcTuring.SMC.Concrete.call_program_length
#print axioms SmcTuring.SMC.Concrete.address_program_length
#print axioms SmcTuring.SMC.Concrete.address_sites
#print axioms SmcTuring.SMC.Concrete.mov_address_two_concrete_tests
#print axioms SmcTuring.SMC.Concrete.valid_address_pointer
#print axioms SmcTuring.SMC.Concrete.static_pointer_reader
#print axioms SmcTuring.SMC.Concrete.guard_invocation_static
#print axioms SmcTuring.SMC.Concrete.compile_program_cons
#print axioms SmcTuring.SMC.Concrete.program_success
#print axioms SmcTuring.SMC.Concrete.program_fault
#print axioms SmcTuring.SMC.Concrete.Executes.prefix
#print axioms SmcTuring.SMC.Concrete.kernel_passes
#print axioms SmcTuring.SMC.Concrete.source_halt_terminal
#print axioms SmcTuring.SMC.Concrete.source_diverges_forever
#print axioms SmcTuring.SMC.Concrete.terminal_not_forever
#print axioms SmcTuring.SMC.Concrete.source_terminal_iff
#print axioms SmcTuring.SMC.Concrete.source_forever_iff
#print axioms SmcTuring.SMC.Concrete.tm_terminal_iff
#print axioms SmcTuring.SMC.Concrete.tm_forever_iff
#print axioms SmcTuring.SMC.Concrete.terminal_later_none
#print axioms SmcTuring.SMC.Concrete.terminal_execution_pure
#print axioms SmcTuring.SMC.Concrete.source_pure
#print axioms SmcTuring.SMC.Concrete.fixed_pure_smc_simulation
#print axioms SmcTuring.SMC.Concrete.store_invocation_static
#print axioms SmcTuring.SMC.Concrete.store_success
#print axioms SmcTuring.SMC.Concrete.source_tm_run_progress
#print axioms SmcTuring.SMC.Concrete.tm_run_correct
#print axioms SmcTuring.SMC.Concrete.configuration_head_word
#print axioms SmcTuring.SMC.Concrete.configuration_tape_words
#print axioms SmcTuring.SMC.Concrete.field_change_is_code_change
#print axioms SmcTuring.SMC.Concrete.field_change_in_run
#print axioms SmcTuring.SMC.Concrete.walker_initial
#print axioms SmcTuring.SMC.Concrete.walker_step
#print axioms SmcTuring.SMC.Concrete.walker_run
#print axioms SmcTuring.SMC.Concrete.walker_diverges
#print axioms SmcTuring.SMC.Concrete.walker_field_bound
#print axioms SmcTuring.SMC.Concrete.walker_unbounded_fields
#print axioms SmcTuring.SMC.Concrete.pure_unbounded_smc_witness
#print axioms SmcTuring.SMC.Concrete.sentinel_prefix_correct
#print axioms SmcTuring.SMC.Concrete.sentinel_prefix_tape
#print axioms SmcTuring.SMC.Concrete.sentinel_prefix_supported
#print axioms SmcTuring.SMC.Concrete.sentinel_kernel_split
#print axioms SmcTuring.SMC.Concrete.compile_program_append
#print axioms SmcTuring.SMC.Concrete.sentinel_sites
#print axioms SmcTuring.SMC.Concrete.represented_tape_words
#print axioms SmcTuring.SMC.Concrete.sentinel_terminal_tape
#print axioms SmcTuring.SMC.Concrete.halted_scan_sentinel
#print axioms SmcTuring.SMC.Concrete.tm_halt_output
#print axioms SmcTuring.SMC.Concrete.terminal_runs_unique
#print axioms SmcTuring.SMC.Concrete.terminal_output_reflects
#print axioms SmcTuring.SMC.Finite.lookup_cons
#print axioms SmcTuring.SMC.Finite.lookup_outside
#print axioms SmcTuring.SMC.Finite.eval_correct
#print axioms SmcTuring.SMC.Finite.decode_correct
#print axioms SmcTuring.SMC.Finite.execute_correct
#print axioms SmcTuring.SMC.Finite.execute_length
#print axioms SmcTuring.SMC.Finite.step_correct
#print axioms SmcTuring.SMC.Finite.step_length
#print axioms SmcTuring.SMC.Finite.run_correct
#print axioms SmcTuring.SMC.Finite.run_length
#print axioms SmcTuring.SMC.Finite.reached_description
#print axioms SmcTuring.TM.freeze_transition
#print axioms SmcTuring.TM.thaw_freeze
#print axioms SmcTuring.TM.freeze_rows
#print axioms SmcTuring.TM.freeze_columns
#print axioms SmcTuring.SMC.Finite.decode_changes_encode
#print axioms SmcTuring.SMC.Finite.encode_changes_length
#print axioms SmcTuring.SMC.Finite.deserialize_serialize
#print axioms SmcTuring.SMC.Finite.serialize_injective
#print axioms SmcTuring.SMC.Finite.serialize_length
#print axioms SmcTuring.SMC.Finite.deserialize_serialize_nat
#print axioms SmcTuring.SMC.Finite.serialize_nat_injective
#print axioms SmcTuring.SMC.Finite.serialize_nat_length
#print axioms SmcTuring.SMC.Concrete.initial_description_correct
#print axioms SmcTuring.SMC.Concrete.finite_run_correct
#print axioms SmcTuring.SMC.Concrete.original_machine_finite_run
#print axioms SmcTuring.SMC.Concrete.every_reached_state_finite
#print axioms SmcTuring.SMC.Concrete.finite_terminal_equivalence
#print axioms SmcTuring.SMC.Concrete.finite_divergence_equivalence
#print axioms SmcTuring.SMC.Concrete.finite_data_computation
#print axioms SmcTuring.SMC.Concrete.encoded_run_roundtrip
#print axioms SmcTuring.SMC.Concrete.every_reached_state_encoded
#print axioms SmcTuring.MathlibTM0.original_transition
#print axioms SmcTuring.MathlibTM0.restoring_transition
#print axioms SmcTuring.MathlibTM0.represented_head
#print axioms SmcTuring.MathlibTM0.initialized_tape_nth
#print axioms SmcTuring.MathlibTM0.initial_rep
#print axioms SmcTuring.MathlibTM0.move_step
#print axioms SmcTuring.MathlibTM0.write_first_step
#print axioms SmcTuring.MathlibTM0.write_second_step
#print axioms SmcTuring.MathlibTM0.write_two_steps
#print axioms SmcTuring.MathlibTM0.move_rep
#print axioms SmcTuring.MathlibTM0.write_rep
#print axioms SmcTuring.MathlibTM0.missing_step_iff
#print axioms SmcTuring.MathlibTM0.simulate_step
#print axioms SmcTuring.MathlibTM0.source_run_reaches
#print axioms SmcTuring.MathlibTM0.source_reaches_run
#print axioms SmcTuring.MathlibTM0.source_halts_eval
#print axioms SmcTuring.MathlibTM0.compiler_respects
#print axioms SmcTuring.MathlibTM0.standard_halts_iff
#print axioms SmcTuring.MathlibTM0.fixed_smc_mathlib_simulation
#print axioms SmcTuring.MathlibTM0.standard_terminal_output
#print axioms SmcTuring.MathlibTM0.Reverse.labels_finite
#print axioms SmcTuring.MathlibTM0.Reverse.labels_card
#print axioms SmcTuring.MathlibTM0.Reverse.represented_head
#print axioms SmcTuring.MathlibTM0.Reverse.initial_rep
#print axioms SmcTuring.MathlibTM0.Reverse.write_step
#print axioms SmcTuring.MathlibTM0.Reverse.move_step
#print axioms SmcTuring.MathlibTM0.Reverse.two_steps
#print axioms SmcTuring.MathlibTM0.Reverse.result_rep
#print axioms SmcTuring.MathlibTM0.Reverse.missing_step_iff
#print axioms SmcTuring.MathlibTM0.Reverse.compiler_respects
#print axioms SmcTuring.MathlibTM0.Reverse.normalized_halts_iff
#print axioms SmcTuring.MathlibTM0.Reverse.normalized_terminal_output
#print axioms SmcTuring.MathlibTM0.Reverse.halts_iff
#print axioms SmcTuring.MathlibTM0.Reverse.terminal_output
#print axioms SmcTuring.SMC.Effective.zigzag_unzigzag
#print axioms SmcTuring.SMC.Effective.journal_decode_code
#print axioms SmcTuring.SMC.Effective.journal_code_decode
#print axioms SmcTuring.SMC.Effective.journal_code_injective
#print axioms SmcTuring.SMC.Effective.journal_code_length
#print axioms SmcTuring.SMC.Effective.read_correct
#print axioms SmcTuring.SMC.Effective.push_correct
#print axioms SmcTuring.SMC.Effective.flatten_correct
#print axioms SmcTuring.SMC.Effective.flatten_length
#print axioms SmcTuring.SMC.Effective.serialize_journal
#print axioms SmcTuring.SMC.Effective.read_primrec
#print axioms SmcTuring.SMC.Effective.push_primrec
#print axioms SmcTuring.SMC.Effective.flatten_primrec
#print axioms SmcTuring.SMC.Effective.zigzag_encode
#print axioms SmcTuring.SMC.Effective.unzigzag_ofNat
#print axioms SmcTuring.SMC.Effective.zigzag_primrec
#print axioms SmcTuring.SMC.Effective.unzigzag_primrec
#print axioms SmcTuring.SMC.Effective.journal_code_primrec
#print axioms SmcTuring.SMC.Effective.journal_decode_primrec
#print axioms SmcTuring.SMC.Effective.unzigzag_injective
#print axioms SmcTuring.SMC.Effective.difference_decode
#print axioms SmcTuring.SMC.Effective.difference_primrec
#print axioms SmcTuring.SMC.Effective.add_decode
#print axioms SmcTuring.SMC.Effective.add_correct
#print axioms SmcTuring.SMC.Effective.add_primrec
#print axioms SmcTuring.SMC.Effective.negate_decode
#print axioms SmcTuring.SMC.Effective.negate_correct
#print axioms SmcTuring.SMC.Effective.negate_primrec
#print axioms SmcTuring.SMC.Effective.subtract_decode
#print axioms SmcTuring.SMC.Effective.subtract_correct
#print axioms SmcTuring.SMC.Effective.subtract_primrec
#print axioms SmcTuring.SMC.Effective.less_decode
#print axioms SmcTuring.SMC.Effective.less_correct
#print axioms SmcTuring.SMC.Effective.less_primrec
#print axioms SmcTuring.SMC.Effective.borrow_correct
#print axioms SmcTuring.SMC.Effective.borrow_primrec
#print axioms SmcTuring.SMC.Effective.subtract_borrow_correct
#print axioms SmcTuring.SMC.Effective.subtract_borrow_primrec
#print axioms SmcTuring.SMC.Effective.boolean_binary_primrec
#print axioms SmcTuring.SMC.Effective.bitwise_children_primrec
#print axioms SmcTuring.SMC.Effective.bitwise_children_decrease
#print axioms SmcTuring.SMC.Effective.bitwise_combine_primrec
#print axioms SmcTuring.SMC.Effective.bitwise_combine_correct
#print axioms SmcTuring.SMC.Effective.nat_bitwise_primrec
#print axioms SmcTuring.SMC.Effective.nat_and_primrec
#print axioms SmcTuring.SMC.Effective.nat_or_primrec
#print axioms SmcTuring.SMC.Effective.nat_xor_primrec
#print axioms SmcTuring.SMC.Effective.xor_correct
#print axioms SmcTuring.SMC.Effective.and_correct
#print axioms SmcTuring.SMC.Effective.xor_decode
#print axioms SmcTuring.SMC.Effective.and_decode
#print axioms SmcTuring.SMC.Effective.xor_primrec
#print axioms SmcTuring.SMC.Effective.and_primrec
#print axioms SmcTuring.SMC.Effective.decode_state_code
#print axioms SmcTuring.SMC.Effective.state_code_decode
#print axioms SmcTuring.SMC.Effective.pack_state_correct
#print axioms SmcTuring.SMC.Effective.pack_state_primrec
#print axioms SmcTuring.SMC.Effective.pair_step_primrec
#print axioms SmcTuring.SMC.Effective.pair_fold_primrec
#print axioms SmcTuring.SMC.Effective.unflatten_primrec
#print axioms SmcTuring.SMC.Effective.pair_fold_flatten
#print axioms SmcTuring.SMC.Effective.unflatten_flatten
#print axioms SmcTuring.SMC.Effective.unflatten_two
#print axioms SmcTuring.SMC.Effective.unflatten_correct
#print axioms SmcTuring.SMC.Effective.word_at_primrec
#print axioms SmcTuring.SMC.Effective.record_state_primrec
#print axioms SmcTuring.SMC.Effective.parse_state_primrec
#print axioms SmcTuring.SMC.Effective.parse_pack_state
#print axioms SmcTuring.SMC.Effective.parse_serialized_state
#print axioms SmcTuring.SMC.Effective.instruction_code_arg
#print axioms SmcTuring.SMC.Effective.instruction_code_valid
#print axioms SmcTuring.SMC.Effective.decode_instruction_code
#print axioms SmcTuring.SMC.Effective.execute_instruction_code_correct
#print axioms SmcTuring.SMC.Effective.execute_invalid_code
#print axioms SmcTuring.SMC.Effective.execute_instruction_code_primrec
#print axioms SmcTuring.SMC.Effective.resolve_address_code_correct
#print axioms SmcTuring.SMC.Effective.resolve_address_code_primrec
#print axioms SmcTuring.SMC.Effective.resolve_invalid_address
#print axioms SmcTuring.SMC.Effective.header_code_valid
#print axioms SmcTuring.SMC.Effective.decode_header_code_correct
#print axioms SmcTuring.SMC.Effective.decode_header_code_primrec
#print axioms SmcTuring.SMC.Effective.decode_invalid_header
#print axioms SmcTuring.SMC.Effective.fixed_control_header_code_correct
#print axioms SmcTuring.SMC.Effective.fixed_control_header_code_primrec
#print axioms SmcTuring.SMC.Effective.meta_field_code
#print axioms SmcTuring.SMC.Effective.fixed_storage_header_code_correct
#print axioms SmcTuring.SMC.Effective.fixed_storage_header_code_primrec
#print axioms SmcTuring.SMC.Effective.fixed_headers_code_correct
#print axioms SmcTuring.SMC.Effective.fixed_headers_code_primrec
#print axioms SmcTuring.SMC.Effective.machine_codec_primrec
#print axioms SmcTuring.SMC.Effective.machine_constructor_primrec
#print axioms SmcTuring.SMC.Effective.frozen_codec_primrec
#print axioms SmcTuring.SMC.Effective.frozen_constructor_primrec
#print axioms SmcTuring.SMC.Effective.entry_codec_primrec
#print axioms SmcTuring.SMC.Effective.entry_constructor_primrec
#print axioms SmcTuring.SMC.Effective.word_codec_primrec
#print axioms SmcTuring.SMC.Effective.word_constructor_primrec
#print axioms SmcTuring.SMC.Effective.word_address_primrec
#print axioms SmcTuring.SMC.Effective.word_offset_primrec
#print axioms SmcTuring.SMC.Effective.machine_blank_primrec
#print axioms SmcTuring.SMC.Effective.machine_start_primrec
#print axioms SmcTuring.SMC.Effective.machine_transition_primrec
#print axioms SmcTuring.SMC.Effective.frozen_blank_primrec
#print axioms SmcTuring.SMC.Effective.frozen_start_primrec
#print axioms SmcTuring.SMC.Effective.frozen_table_primrec
#print axioms SmcTuring.SMC.Effective.frozen_transition_primrec
#print axioms SmcTuring.SMC.Effective.thaw_primrec
#print axioms SmcTuring.SMC.Effective.transition_primrec
#print axioms SmcTuring.SMC.Effective.entries_primrec
#print axioms SmcTuring.SMC.Effective.table_node_primrec
#print axioms SmcTuring.SMC.Effective.table_cursor_primrec
#print axioms SmcTuring.SMC.Effective.table_head_primrec
#print axioms SmcTuring.SMC.Effective.table_record_primrec
#print axioms SmcTuring.SMC.Effective.table_memory_fixed_primrec
#print axioms SmcTuring.SMC.Effective.table_cache_primrec
#print axioms SmcTuring.SMC.Effective.table_from_cache_primrec
#print axioms SmcTuring.SMC.Effective.table_from_cache_correct
#print axioms SmcTuring.SMC.Effective.initial_symbol_primrec
#print axioms SmcTuring.SMC.Effective.initial_symbol_correct
#print axioms SmcTuring.SMC.Effective.zigzag_outward
#print axioms SmcTuring.SMC.Effective.initialized_tape_primrec
#print axioms SmcTuring.SMC.Effective.initialized_tape_correct
#print axioms SmcTuring.SMC.Effective.initialized_heap_primrec
#print axioms SmcTuring.SMC.Effective.initialized_heap_correct
#print axioms SmcTuring.SMC.Effective.word_natural_primrec
#print axioms SmcTuring.SMC.Effective.encode_word_natural
#print axioms SmcTuring.SMC.Effective.int_of_nat_primrec
#print axioms SmcTuring.SMC.Effective.initialized_register_fixed_primrec
#print axioms SmcTuring.SMC.Effective.initial_register_cache_primrec
#print axioms SmcTuring.SMC.Effective.initialized_data_word_primrec
#print axioms SmcTuring.SMC.Effective.initialized_data_word_correct
#print axioms SmcTuring.SMC.Effective.initialized_data_memory_correct
#print axioms SmcTuring.SMC.Effective.initialized_data_code_primrec
#print axioms SmcTuring.SMC.Effective.initialized_data_code_correct
#print axioms SmcTuring.SMC.Effective.metadata_code_primrec
#print axioms SmcTuring.SMC.Effective.metadata_code_correct
#print axioms SmcTuring.SMC.Effective.initial_word_code_primrec
#print axioms SmcTuring.SMC.Effective.initial_word_code_correct
#print axioms SmcTuring.SMC.Effective.address_code_arg
#print axioms SmcTuring.SMC.Effective.header_code_arg
#print axioms SmcTuring.SMC.Effective.step_code_primrec
#print axioms SmcTuring.SMC.Effective.step_code_correct
#print axioms SmcTuring.SMC.Effective.run_code_iterate_option
#print axioms SmcTuring.SMC.Effective.run_code_primrec
#print axioms SmcTuring.SMC.Effective.run_code_correct
#print axioms SmcTuring.SMC.Effective.concrete_finite_run_primrec
#print axioms SmcTuring.SMC.Effective.run_code_iterate
#print axioms SmcTuring.SMC.Effective.terminal_prefix_primrec
#print axioms SmcTuring.SMC.Effective.terminal_prefix_some
#print axioms SmcTuring.SMC.Effective.terminal_prefix_mem
#print axioms SmcTuring.SMC.Effective.terminal_search_partrec
#print axioms SmcTuring.SMC.Effective.terminal_search_domain
#print axioms SmcTuring.SMC.Effective.terminal_search_halts
#print axioms SmcTuring.SMC.Effective.terminal_search_diverges
#print axioms SmcTuring.SMC.Effective.terminal_search_output
#print axioms SmcTuring.SMC.Effective.terminal_search_nat_partrec
#print axioms SmcTuring.SMC.Effective.terminal_search_nat_encoded
#print axioms SmcTuring.SMC.Effective.terminal_search_nat_domain
#print axioms SmcTuring.SMC.Effective.terminal_search_vector_partrec
#print axioms SmcTuring.SMC.Effective.terminal_search_library_code
#print axioms SmcTuring.SMC.Effective.tm2_alphabet_finite
#print axioms SmcTuring.SMC.Effective.tm2_local_storage_finite
#print axioms SmcTuring.SMC.Effective.tm2_stacks_enumerated
#print axioms SmcTuring.SMC.Effective.tm2_control_support_finite
#print axioms SmcTuring.SMC.Effective.terminal_search_tm2
#print axioms SmcTuring.SMC.Effective.tm2_compiler_positive_steps
#print axioms SmcTuring.SMC.Effective.tm2_compiler_initial_progress
#print axioms SmcTuring.SMC.Effective.interpreter_alphabet_finite
#print axioms SmcTuring.SMC.Effective.tm2_code_initial
#print axioms SmcTuring.SMC.Effective.tm2_code_eval
#print axioms SmcTuring.SMC.Effective.terminal_search_tm0
#print axioms SmcTuring.SMC.Effective.tm0_terminal_output
#print axioms SmcTuring.SMC.Effective.terminal_search_positive_progress
#print axioms SmcTuring.SMC.Effective.terminal_search_tm0_with_output
#print axioms SmcTuring.MathlibTM0.FiniteSupport.labels_finite
#print axioms SmcTuring.MathlibTM0.FiniteSupport.labels_card
#print axioms SmcTuring.MathlibTM0.FiniteSupport.step_embedding
#print axioms SmcTuring.MathlibTM0.FiniteSupport.restrict_respects
#print axioms SmcTuring.MathlibTM0.FiniteSupport.configuration_eval
#print axioms SmcTuring.MathlibTM0.FiniteSupport.initial_embedding
#print axioms SmcTuring.MathlibTM0.FiniteSupport.eval_eq
#print axioms SmcTuring.MathlibTM0.Numbering.transport_respects
#print axioms SmcTuring.MathlibTM0.Numbering.configuration_eval
#print axioms SmcTuring.MathlibTM0.Numbering.initial_encoding
#print axioms SmcTuring.MathlibTM0.Numbering.right_output
#print axioms SmcTuring.MathlibTM0.Numbering.eval_eq
#print axioms SmcTuring.SMC.Effective.terminal_search_numbered_tm0
#print axioms SmcTuring.SMC.Effective.terminal_search_pure_smc
#print axioms SmcTuring.Examples.Addition.addition_trace
#print axioms SmcTuring.Examples.Addition.displayed_output
#print axioms SmcTuring.Examples.Addition.addition_halts_with_output
#print axioms SmcTuring.Examples.Addition.addition_pure_smc

#print axioms SmcTuring.Native.LittleEndian.byte_bound

#print axioms SmcTuring.Native.LittleEndian.pack_bound

#print axioms SmcTuring.Native.LittleEndian.pack_encode

#print axioms SmcTuring.Native.LittleEndian.encode_pack

#print axioms SmcTuring.Native.LittleEndian.radix_power

#print axioms SmcTuring.Native.LittleEndian.word_encode_decode

#print axioms SmcTuring.Native.LittleEndian.word_encode_injective

#print axioms SmcTuring.Native.LittleEndian.word_decode_wrong_length

#print axioms SmcTuring.Native.form_roundtrip

#print axioms SmcTuring.Native.form_encode_injective

#print axioms SmcTuring.Native.instruction_length_bound

#print axioms SmcTuring.Native.moffs_operand_bytes

#print axioms SmcTuring.Native.moffs_opcode_bytes

#print axioms SmcTuring.Native.memory_displacement_bytes

#print axioms SmcTuring.Native.ByteMemory.put_at_index

#print axioms SmcTuring.Native.ByteMemory.put_frame

#print axioms SmcTuring.Native.ByteMemory.bytes_at_frame

#print axioms SmcTuring.Native.ByteMemory.patch_payload

#print axioms SmcTuring.Native.ByteMemory.read_put_word

#print axioms SmcTuring.Native.ByteMemory.word_write_nonempty

#print axioms SmcTuring.Native.ByteMemory.moffs_patch

#print axioms SmcTuring.Native.ByteMemory.fetch_written_moffs

#print axioms SmcTuring.Native.ByteMemory.fetch_patched_moffs

#print axioms SmcTuring.Native.Layout.owner_field_address

#print axioms SmcTuring.Native.Layout.fields_and_owners_disjoint

#print axioms SmcTuring.Native.Layout.field_address_injective

#print axioms SmcTuring.Native.Layout.field_alignment

#print axioms SmcTuring.Native.Layout.register_before_heap

#print axioms SmcTuring.Native.Layout.heap_at_or_above_boundary

#print axioms SmcTuring.Native.Layout.boolean_offsets_below_boundary

#print axioms SmcTuring.Native.Layout.heap_second_field

#print axioms SmcTuring.Native.Layout.finite_capacity

#print axioms SmcTuring.Native.Layout.other_field_frame

#print axioms SmcTuring.Native.LittleEndian.encode_length

#print axioms SmcTuring.Native.LittleEndian.word_encode_length

#print axioms SmcTuring.Native.LittleEndian.word_decode_encode

#print axioms SmcTuring.Native.operation_tag_roundtrip

#print axioms SmcTuring.Native.memory_payload_roundtrip

#print axioms SmcTuring.Native.instruction_length

#print axioms SmcTuring.Native.ByteMemory.bytes_at_length

#print axioms SmcTuring.Native.ByteMemory.bytes_at_put

#print axioms SmcTuring.Native.Arithmetic.sbb_zero_mask

#print axioms SmcTuring.Native.Arithmetic.xor_mask_select

#print axioms SmcTuring.Native.Arithmetic.select_sub_borrow

#print axioms SmcTuring.Native.Arithmetic.encode_nat_toNat

#print axioms SmcTuring.Native.Arithmetic.borrow_encode_nat

#print axioms SmcTuring.Native.Arithmetic.offset_below_boundary

#print axioms SmcTuring.Native.Arithmetic.offset_borrow

#print axioms SmcTuring.Native.Arithmetic.heap_borrow

#print axioms SmcTuring.Native.Arithmetic.base_guard_accepts_heap

#print axioms SmcTuring.Native.Arithmetic.base_guard_rejects_offset

#print axioms SmcTuring.Native.Arithmetic.offset_guard_accepts_offset

#print axioms SmcTuring.Native.Arithmetic.offset_guard_rejects_heap

#print axioms SmcTuring.Native.Arithmetic.indexed_heap_address

#print axioms SmcTuring.Native.Arithmetic.indexed_heap_address_toNat

#print axioms SmcTuring.Native.Execution.read_word_total

#print axioms SmcTuring.Native.Execution.load_put_word

#print axioms SmcTuring.Native.Execution.execute_byte_encoding

#print axioms SmcTuring.Native.Execution.execute_preserves_carry

#print axioms SmcTuring.Native.Execution.run_preserves_carry

#print axioms SmcTuring.Native.Execution.execute_byte_carry

#print axioms SmcTuring.Native.Execution.moffs_written_value

#print axioms SmcTuring.Native.Execution.indirect_exchange_accumulator

#print axioms SmcTuring.Native.Execution.indirect_exchange_written_value

#print axioms SmcTuring.Native.Execution.call_accumulator_frame

#print axioms SmcTuring.Native.Execution.call_stack

#print axioms SmcTuring.Native.Execution.call_return_word

#print axioms SmcTuring.Native.Execution.indirect_call_target

#print axioms SmcTuring.Native.Execution.indirect_call_alias

#print axioms SmcTuring.Native.Execution.subtract_carry

#print axioms SmcTuring.Native.Execution.sbb_written_value

#print axioms SmcTuring.Native.Execution.sbb_zero_result

#print axioms SmcTuring.Native.Execution.sbb_zero_carry

#print axioms SmcTuring.Native.Execution.xor_carry_clear

#print axioms SmcTuring.Native.Execution.and_carry_clear

#print axioms SmcTuring.Native.Execution.trace_run_eq

#print axioms SmcTuring.Native.Execution.trace_preserves_carry

#print axioms SmcTuring.Native.Execution.sub_bridge_sbb_mask

#print axioms SmcTuring.Native.Execution.execute_patched_moffs

#print axioms SmcTuring.Native.Fetch.encoded_length

#print axioms SmcTuring.Native.Fetch.length_take_three

#print axioms SmcTuring.Native.Fetch.bytes_at_take

#print axioms SmcTuring.Native.Fetch.fetch_current_encoding

#print axioms SmcTuring.Native.Fetch.fetch_written_encoding

#print axioms SmcTuring.Native.Fetch.fetch_patched_moffs

#print axioms SmcTuring.Native.Fetch.step_current_encoding

#print axioms SmcTuring.Native.Fetch.step_patched_moffs

#print axioms SmcTuring.Native.Fetch.trace_run_eq

#print axioms SmcTuring.Native.Fetch.trace_preserves_carry

#print axioms SmcTuring.Native.Writes.put_bytes_back

#print axioms SmcTuring.Native.Writes.put_bytes_overwrite

#print axioms SmcTuring.Native.Writes.put_word_overwrite

#print axioms SmcTuring.Native.Writes.put_word_back

#print axioms SmcTuring.Native.Writes.execute_memory

#print axioms SmcTuring.Native.Writes.execute_frame

#print axioms SmcTuring.Native.Writes.write_nonempty

#print axioms SmcTuring.Native.Writes.fetched_write

#print axioms SmcTuring.Native.Reader.exchange_effect

#print axioms SmcTuring.Native.Reader.store_effect

#print axioms SmcTuring.Native.Reader.restored_memory

#print axioms SmcTuring.Native.Reader.restored_accumulator

#print axioms SmcTuring.Native.Reader.dereferenced_memory

#print axioms SmcTuring.Native.Reader.dereferenced_accumulator

#print axioms SmcTuring.Native.Reader.finish_memory

#print axioms SmcTuring.Native.Reader.finish_accumulator

#print axioms SmcTuring.Native.Reader.finish_stack

#print axioms SmcTuring.Native.Reader.finish_carry

#print axioms SmcTuring.Native.Reader.fetch_last

#print axioms SmcTuring.Native.Reader.store_write_address

#print axioms SmcTuring.Native.Reader.four_writes_owned

#print axioms SmcTuring.Native.Reader.prefix_length

#print axioms SmcTuring.Native.Reader.operand_offset

#print axioms SmcTuring.Native.Reader.trace_of_fetches

#print axioms SmcTuring.Native.Reader.trace_result

#print axioms SmcTuring.Native.Fetch.trace_head_step

#print axioms SmcTuring.Native.Fetch.step_preserves_carry

#print axioms SmcTuring.Native.Fetch.sub_bridge_sbb_mask

#print axioms SmcTuring.Native.Fetch.trace_append

#print axioms SmcTuring.Native.Writes.load_frame

#print axioms SmcTuring.Native.Writes.owned_run_append

#print axioms SmcTuring.Native.Calls.exchange_effect

#print axioms SmcTuring.Native.Calls.store_effect

#print axioms SmcTuring.Native.Calls.reset_memory

#print axioms SmcTuring.Native.Calls.reset_stack

#print axioms SmcTuring.Native.Calls.reset_accumulator

#print axioms SmcTuring.Native.Calls.reset_carry

#print axioms SmcTuring.Native.Calls.stack_slot

#print axioms SmcTuring.Native.Calls.called_effect

#print axioms SmcTuring.Native.Calls.called_memory

#print axioms SmcTuring.Native.Calls.called_stack

#print axioms SmcTuring.Native.Calls.called_accumulator

#print axioms SmcTuring.Native.Calls.called_carry

#print axioms SmcTuring.Native.Calls.called_return_word

#print axioms SmcTuring.Native.Calls.indirect_target

#print axioms SmcTuring.Native.Calls.aliased_return

#print axioms SmcTuring.Native.Calls.called_frame

#print axioms SmcTuring.Native.Calls.called_top_word

#print axioms SmcTuring.Native.Calls.call_write_address

#print axioms SmcTuring.Native.Calls.three_writes_owned

#print axioms SmcTuring.Native.Calls.owned_run

#print axioms SmcTuring.Native.Calls.trace_of_fetches

#print axioms SmcTuring.Native.Calls.trace_result

#print axioms SmcTuring.Native.Calls.reset_length

#print axioms SmcTuring.Native.Calls.program_length

#print axioms SmcTuring.Native.ReadCallee.target_pc

#print axioms SmcTuring.Native.ReadCallee.memory_effect

#print axioms SmcTuring.Native.ReadCallee.accumulator

#print axioms SmcTuring.Native.ReadCallee.stack

#print axioms SmcTuring.Native.ReadCallee.carry

#print axioms SmcTuring.Native.ReadCallee.return_word

#print axioms SmcTuring.Native.ReadCallee.memory_frame

#print axioms SmcTuring.Native.ReadCallee.top_word

#print axioms SmcTuring.Native.ReadCallee.owned_run

#print axioms SmcTuring.Native.ReadCallee.trace_of_components

#print axioms SmcTuring.Native.ReadCallee.trace_result

#print axioms SmcTuring.Native.ReadCallee.program_length

#print axioms SmcTuring.Native.ReadCallee.invocation_returns

#print axioms SmcTuring.Native.ReadCallee.invocation_memory

#print axioms SmcTuring.Native.ReadCallee.invocation_carry

#print axioms SmcTuring.Native.Protected.bytes_at_append

#print axioms SmcTuring.Native.Protected.word_at_encoded

#print axioms SmcTuring.Native.Protected.word_at_put

#print axioms SmcTuring.Native.Protected.current_moffs

#print axioms SmcTuring.Native.Protected.fetch_moffs

#print axioms SmcTuring.Native.Protected.prefix_frame

#print axioms SmcTuring.Native.Protected.grid_prefix_separate

#print axioms SmcTuring.Native.Protected.grid_store_protected

#print axioms SmcTuring.Native.Protected.grid_fetch_written

#print axioms SmcTuring.Native.Protected.grid_fetch_current

#print axioms SmcTuring.Native.Protected.encoded_address_load

#print axioms SmcTuring.Native.Protected.execute_grid_protected

#print axioms SmcTuring.Native.Protected.run_grid_protected

#print axioms SmcTuring.Native.Protected.trace_grid_protected

#print axioms SmcTuring.Native.GridImage.start_before

#print axioms SmcTuring.Native.GridImage.coordinate

#print axioms SmcTuring.Native.GridImage.coordinate_div

#print axioms SmcTuring.Native.GridImage.coordinate_mod

#print axioms SmcTuring.Native.GridImage.prefix_bytes

#print axioms SmcTuring.Native.GridImage.operand_bytes

#print axioms SmcTuring.Native.GridImage.initially_protected

#print axioms SmcTuring.Native.GridImage.initial_word

#print axioms SmcTuring.Native.GridImage.initial_fetch

#print axioms SmcTuring.Native.ControlImage.apart_symmetric

#print axioms SmcTuring.Native.ControlImage.apart_bytes

#print axioms SmcTuring.Native.ControlImage.separated_tail

#print axioms SmcTuring.Native.ControlImage.image_packet

#print axioms SmcTuring.Native.ControlImage.initialized_intact

#print axioms SmcTuring.Native.ControlImage.fetch_current

#print axioms SmcTuring.Native.ControlImage.owned_packet_length

#print axioms SmcTuring.Native.ControlImage.store_intact

#print axioms SmcTuring.Native.ControlImage.execute_intact

#print axioms SmcTuring.Native.ControlImage.external_store_intact

#print axioms SmcTuring.Native.ControlImage.allowed_store_intact

#print axioms SmcTuring.Native.ControlImage.execute_allowed_intact

#print axioms SmcTuring.Native.ControlImage.run_allowed_intact

#print axioms SmcTuring.Native.ControlImage.run_intact

#print axioms SmcTuring.Native.ControlImage.trace_intact

#print axioms SmcTuring.Native.ControlPacking.placed_lower

#print axioms SmcTuring.Native.ControlPacking.placed_upper

#print axioms SmcTuring.Native.ControlPacking.placed_separated

#print axioms SmcTuring.Native.ControlPacking.initial_packet

#print axioms SmcTuring.Native.ControlPacking.initially_intact

#print axioms SmcTuring.Native.ControlPacking.initial_fetch

#print axioms SmcTuring.Native.ControlPacking.image_frame

#print axioms SmcTuring.Native.ControlPacking.step_at_entry

#print axioms SmcTuring.Native.ControlPacking.above_external

#print axioms SmcTuring.Native.ControlPacking.reached_intact

#print axioms SmcTuring.Native.CombinedImage.initial_grid

#print axioms SmcTuring.Native.CombinedImage.initially_intact

#print axioms SmcTuring.Native.CombinedImage.initial_word

#print axioms SmcTuring.Native.CombinedImage.control_store_grid

#print axioms SmcTuring.Native.CombinedImage.store_intact

#print axioms SmcTuring.Native.CombinedImage.owned_operand

#print axioms SmcTuring.Native.CombinedImage.execute_intact

#print axioms SmcTuring.Native.CombinedImage.run_intact

#print axioms SmcTuring.Native.CombinedImage.trace_intact

#print axioms SmcTuring.Native.ReaderImage.packet_size

#print axioms SmcTuring.Native.ReaderImage.placed_roles

#print axioms SmcTuring.Native.ReaderImage.label_location

#print axioms SmcTuring.Native.ReaderImage.label_owned

#print axioms SmcTuring.Native.ReaderImage.swapped_pc

#print axioms SmcTuring.Native.ReaderImage.restored_pc

#print axioms SmcTuring.Native.ReaderImage.dereferenced_pc

#print axioms SmcTuring.Native.ReaderImage.finish_pc

#print axioms SmcTuring.Native.ReaderImage.finish_position

#print axioms SmcTuring.Native.ReaderImage.first_hits

#print axioms SmcTuring.Native.ReaderImage.second_hits

#print axioms SmcTuring.Native.ReaderImage.reached_positions

#print axioms SmcTuring.Native.ReaderImage.trace

#print axioms SmcTuring.Native.ReaderImage.owned_run

#print axioms SmcTuring.Native.ReaderImage.result

#print axioms SmcTuring.Native.ReaderImage.initially_intact

#print axioms SmcTuring.Native.ReaderImage.initial_pointer

#print axioms SmcTuring.Native.ReaderImage.initialized_trace

#print axioms SmcTuring.Native.ReaderImage.initialized_accumulator

#print axioms SmcTuring.Native.Relocation.relative32_toInt

#print axioms SmcTuring.Native.Relocation.sign_extended_relative32

#print axioms SmcTuring.Native.Relocation.add_relative32

#print axioms SmcTuring.Native.Relocation.memory_hits

#print axioms SmcTuring.Native.Relocation.next_pc

#print axioms SmcTuring.Native.Relocation.memory_length

#print axioms SmcTuring.Native.Relocation.instruction_memory_hits

#print axioms SmcTuring.Native.Relocation.relative_call_pc

#print axioms SmcTuring.Native.Relocation.relative_call_position

#print axioms SmcTuring.Native.Fragment.size_append

#print axioms SmcTuring.Native.Fragment.place_append

#print axioms SmcTuring.Native.Fragment.prefix_within

#print axioms SmcTuring.Native.Fragment.suffix_within

#print axioms SmcTuring.Native.Fragment.within_trans

#print axioms SmcTuring.Native.Fragment.intact_view

#print axioms SmcTuring.Native.Fragment.owned_view

#print axioms SmcTuring.Native.Fragment.initialized_owned_word

#print axioms SmcTuring.Native.Fragment.owned_packet_safe

#print axioms SmcTuring.Native.Fragment.owned_fields_separate

#print axioms SmcTuring.Native.ReaderView.label_owned

#print axioms SmcTuring.Native.ReaderView.trace

#print axioms SmcTuring.Native.ReaderView.owned_run

#print axioms SmcTuring.Native.CallsImage.packet_size

#print axioms SmcTuring.Native.CallsImage.placed_roles

#print axioms SmcTuring.Native.CallsImage.exchange_pc

#print axioms SmcTuring.Native.CallsImage.reset_pc

#print axioms SmcTuring.Native.CallsImage.return_next

#print axioms SmcTuring.Native.CallsImage.reset_ready

#print axioms SmcTuring.Native.CallsImage.stack_ready

#print axioms SmcTuring.Native.CallsImage.indirect_hits

#print axioms SmcTuring.Native.CallsImage.reached_positions

#print axioms SmcTuring.Native.CallsImage.trace

#print axioms SmcTuring.Native.CallsImage.owned_run

#print axioms SmcTuring.Native.CallsImage.target_pc

#print axioms SmcTuring.Native.ReadCalleeImage.packet_size

#print axioms SmcTuring.Native.ReadCalleeImage.reader_within

#print axioms SmcTuring.Native.ReadCalleeImage.call_within

#print axioms SmcTuring.Native.ReadCalleeImage.read_pc

#print axioms SmcTuring.Native.ReadCalleeImage.read_memory

#print axioms SmcTuring.Native.ReadCalleeImage.ready

#print axioms SmcTuring.Native.ReadCalleeImage.return_next

#print axioms SmcTuring.Native.ReadCalleeImage.reader_fits

#print axioms SmcTuring.Native.ReadCalleeImage.call_fits

#print axioms SmcTuring.Native.ReadCalleeImage.trace

#print axioms SmcTuring.Native.ReadCalleeImage.owned_run

#print axioms SmcTuring.Native.ReadCalleeImage.finish_intact

#print axioms SmcTuring.Native.ReadCalleeImage.memory_effect

#print axioms SmcTuring.Native.ReadCalleeImage.boundary_effect

#print axioms SmcTuring.Native.ReadCalleeImage.top_reusable

#print axioms SmcTuring.Native.ReadCalleeImage.initial_pointer

#print axioms SmcTuring.Native.ReadCalleeImage.initialized_ready

#print axioms SmcTuring.Native.ReadCalleeImage.initialized_trace

#print axioms SmcTuring.Native.ReadCalleeImage.initialized_owned_run

#print axioms SmcTuring.Native.ReadInvocationImage.caller_run

#print axioms SmcTuring.Native.ReadInvocationImage.caller_ready

#print axioms SmcTuring.Native.ReadInvocationImage.caller_pc

#print axioms SmcTuring.Native.ReadInvocationImage.caller_memory

#print axioms SmcTuring.Native.ReadInvocationImage.caller_return_word

#print axioms SmcTuring.Native.ReadInvocationImage.label_owned

#print axioms SmcTuring.Native.ReadInvocationImage.caller_label

#print axioms SmcTuring.Native.ReadInvocationImage.caller_top

#print axioms SmcTuring.Native.ReadInvocationImage.caller_trace

#print axioms SmcTuring.Native.ReadInvocationImage.caller_owned_run

#print axioms SmcTuring.Native.ReadInvocationImage.caller_intact

#print axioms SmcTuring.Native.ReadInvocationImage.callee_ready

#print axioms SmcTuring.Native.ReadInvocationImage.callee_trace

#print axioms SmcTuring.Native.ReadInvocationImage.trace

#print axioms SmcTuring.Native.ReadInvocationImage.owned_run

#print axioms SmcTuring.Native.ReadInvocationImage.return_pc

#print axioms SmcTuring.Native.ReadInvocationImage.return_position

#print axioms SmcTuring.Native.ReadInvocationImage.memory_effect

#print axioms SmcTuring.Native.ReadInvocationImage.accumulator

#print axioms SmcTuring.Native.ReadInvocationImage.stack

#print axioms SmcTuring.Native.ReadInvocationImage.carry

#print axioms SmcTuring.Native.ReadInvocationImage.top_reusable

#print axioms SmcTuring.Native.ReadInvocationImage.finish_intact

#print axioms SmcTuring.Native.ReadInvocationImage.memory_frame

#print axioms SmcTuring.Native.ReadInvocationImage.program_count

#print axioms SmcTuring.Native.StoreCalleeImage.store_pc

#print axioms SmcTuring.Native.StoreCalleeImage.store_memory

#print axioms SmcTuring.Native.StoreCalleeImage.store_top

#print axioms SmcTuring.Native.StoreCalleeImage.store_return_word

#print axioms SmcTuring.Native.StoreCalleeImage.store_intact

#print axioms SmcTuring.Native.StoreCalleeImage.call_ready

#print axioms SmcTuring.Native.StoreCalleeImage.return_next

#print axioms SmcTuring.Native.StoreCalleeImage.store_fetch

#print axioms SmcTuring.Native.StoreCalleeImage.call_trace

#print axioms SmcTuring.Native.StoreCalleeImage.trace

#print axioms SmcTuring.Native.StoreCalleeImage.owned_run

#print axioms SmcTuring.Native.StoreCalleeImage.return_pc

#print axioms SmcTuring.Native.StoreCalleeImage.memory_effect

#print axioms SmcTuring.Native.StoreCalleeImage.accumulator

#print axioms SmcTuring.Native.StoreCalleeImage.stack

#print axioms SmcTuring.Native.StoreCalleeImage.carry

#print axioms SmcTuring.Native.StoreCalleeImage.top_reusable

#print axioms SmcTuring.Native.StoreCalleeImage.finish_intact

#print axioms SmcTuring.Native.StoreCalleeImage.program_count
#print axioms SmcTuring.Native.StoreInvocationImage.caller_run
#print axioms SmcTuring.Native.StoreInvocationImage.caller_ready
#print axioms SmcTuring.Native.StoreInvocationImage.caller_pc
#print axioms SmcTuring.Native.StoreInvocationImage.caller_memory
#print axioms SmcTuring.Native.StoreInvocationImage.caller_return_word
#print axioms SmcTuring.Native.StoreInvocationImage.label_owned
#print axioms SmcTuring.Native.StoreInvocationImage.caller_label
#print axioms SmcTuring.Native.StoreInvocationImage.caller_top
#print axioms SmcTuring.Native.StoreInvocationImage.caller_accumulator
#print axioms SmcTuring.Native.StoreInvocationImage.caller_carry
#print axioms SmcTuring.Native.StoreInvocationImage.caller_trace
#print axioms SmcTuring.Native.StoreInvocationImage.caller_owned_run
#print axioms SmcTuring.Native.StoreInvocationImage.caller_intact
#print axioms SmcTuring.Native.StoreInvocationImage.callee_ready
#print axioms SmcTuring.Native.StoreInvocationImage.callee_trace
#print axioms SmcTuring.Native.StoreInvocationImage.trace
#print axioms SmcTuring.Native.StoreInvocationImage.owned_run
#print axioms SmcTuring.Native.StoreInvocationImage.return_pc
#print axioms SmcTuring.Native.StoreInvocationImage.return_position
#print axioms SmcTuring.Native.StoreInvocationImage.memory_effect
#print axioms SmcTuring.Native.StoreInvocationImage.accumulator
#print axioms SmcTuring.Native.StoreInvocationImage.stack
#print axioms SmcTuring.Native.StoreInvocationImage.carry
#print axioms SmcTuring.Native.StoreInvocationImage.top_reusable
#print axioms SmcTuring.Native.StoreInvocationImage.finish_intact
#print axioms SmcTuring.Native.StoreInvocationImage.memory_frame
#print axioms SmcTuring.Native.StoreInvocationImage.program_count
#print axioms SmcTuring.Native.Writes.put_bytes_commute
#print axioms SmcTuring.Native.Writes.put_words_commute
#print axioms SmcTuring.Native.SpacedPacking.adjacent_size
#print axioms SmcTuring.Native.SpacedPacking.adjacent_place
#print axioms SmcTuring.Native.SpacedPacking.size_append
#print axioms SmcTuring.Native.SpacedPacking.place_append
#print axioms SmcTuring.Native.SpacedPacking.placed_lower
#print axioms SmcTuring.Native.SpacedPacking.placed_upper
#print axioms SmcTuring.Native.SpacedPacking.placed_separated
#print axioms SmcTuring.Native.SpacedPacking.initial_packet
#print axioms SmcTuring.Native.SpacedPacking.initially_intact
#print axioms SmcTuring.Native.SpacedPacking.initial_fetch
#print axioms SmcTuring.Native.SpacedPacking.uncovered_frame
#print axioms SmcTuring.Native.SpacedPacking.image_frame
#print axioms SmcTuring.Native.SpacedPacking.above_external
#print axioms SmcTuring.Native.SpacedPacking.adjacent_member
#print axioms SmcTuring.Native.SpacedCombinedImage.initial_grid
#print axioms SmcTuring.Native.SpacedCombinedImage.initially_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.initial_word
#print axioms SmcTuring.Native.SpacedCombinedImage.control_store_grid
#print axioms SmcTuring.Native.SpacedCombinedImage.store_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.owned_operand
#print axioms SmcTuring.Native.SpacedCombinedImage.execute_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.run_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.trace_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.adjacent_image
#print axioms SmcTuring.Native.SpacedCombinedImage.adjacent_intact
#print axioms SmcTuring.Native.SpacedCombinedImage.adjacent_owned
#print axioms SmcTuring.Native.SpacedCombinedImage.padding_byte
#print axioms SmcTuring.Native.AlignedPacking.alignment_small
#print axioms SmcTuring.Native.AlignedPacking.aligned_end
#print axioms SmcTuring.Native.AlignedPacking.reader_extra_constant
#print axioms SmcTuring.Native.AlignedPacking.reader_field_aligned
#print axioms SmcTuring.Native.AlignedPacking.scalar_extra_constant
#print axioms SmcTuring.Native.AlignedPacking.scalar_field_aligned
#print axioms SmcTuring.Native.AlignedPacking.reader_label_aligned
#print axioms SmcTuring.Native.AlignedPacking.scalar_label_location
#print axioms SmcTuring.Native.AlignedPacking.scalar_label_aligned
#print axioms SmcTuring.Native.ScalarImage.form_size
#print axioms SmcTuring.Native.ScalarImage.sbb_size
#print axioms SmcTuring.Native.ScalarImage.hits
#print axioms SmcTuring.Native.ScalarImage.next_pc
#print axioms SmcTuring.Native.ScalarImage.fetch
#print axioms SmcTuring.Native.ScalarImage.trace
#print axioms SmcTuring.Native.ScalarImage.written_address
#print axioms SmcTuring.Native.ScalarImage.owned_run
#print axioms SmcTuring.Native.ScalarImage.pc
#print axioms SmcTuring.Native.ScalarImage.position
#print axioms SmcTuring.Native.ScalarImage.memory_word_effect
#print axioms SmcTuring.Native.ScalarImage.memory_effect
#print axioms SmcTuring.Native.ScalarImage.written_value
#print axioms SmcTuring.Native.ScalarImage.accumulator
#print axioms SmcTuring.Native.ScalarImage.stack
#print axioms SmcTuring.Native.ScalarImage.carry
#print axioms SmcTuring.Native.ScalarImage.store_carry
#print axioms SmcTuring.Native.ScalarImage.memory_frame
#print axioms SmcTuring.Native.ScalarImage.load_frame
#print axioms SmcTuring.Native.ScalarImage.finish_intact
#print axioms SmcTuring.Native.ScalarImage.zero_mask
#print axioms SmcTuring.Native.ScalarImage.zero_carry
#print axioms SmcTuring.Native.ScalarImage.program_count
#print axioms SmcTuring.Native.ScalarImage.run
#print axioms SmcTuring.Native.BorrowMaskImage.zero_owned
#print axioms SmcTuring.Native.BorrowMaskImage.sub_label
#print axioms SmcTuring.Native.BorrowMaskImage.sub_top
#print axioms SmcTuring.Native.BorrowMaskImage.read_ready
#print axioms SmcTuring.Native.BorrowMaskImage.read_zero
#print axioms SmcTuring.Native.BorrowMaskImage.store_ready
#print axioms SmcTuring.Native.BorrowMaskImage.sbb_ready
#print axioms SmcTuring.Native.BorrowMaskImage.stored_zero
#print axioms SmcTuring.Native.BorrowMaskImage.borrow_reaches_sbb
#print axioms SmcTuring.Native.BorrowMaskImage.mask
#print axioms SmcTuring.Native.BorrowMaskImage.trace
#print axioms SmcTuring.Native.BorrowMaskImage.owned_run
#print axioms SmcTuring.Native.BorrowMaskImage.accumulator
#print axioms SmcTuring.Native.BorrowMaskImage.stack
#print axioms SmcTuring.Native.BorrowMaskImage.carry
#print axioms SmcTuring.Native.BorrowMaskImage.position
#print axioms SmcTuring.Native.BorrowMaskImage.finish_intact
#print axioms SmcTuring.Native.BorrowMaskImage.top_reusable
#print axioms SmcTuring.Native.BorrowMaskImage.memory_effect
#print axioms SmcTuring.Native.BorrowMaskImage.memory_frame
#print axioms SmcTuring.Native.BorrowMaskImage.load_frame
#print axioms SmcTuring.Native.BorrowMaskImage.zero_reusable
#print axioms SmcTuring.Native.BorrowMaskImage.pointer_reusable
#print axioms SmcTuring.Native.BorrowMaskImage.program_count
#print axioms SmcTuring.Native.ReadInvocationImage.transport_ready
#print axioms SmcTuring.Native.ReadInvocationImage.load_frame
#print axioms SmcTuring.Native.ScalarImage.transport_ready
#print axioms SmcTuring.Native.ScalarImage.store_size
#print axioms SmcTuring.Native.GuardSetupImage.capture_memory
#print axioms SmcTuring.Native.GuardSetupImage.capture_accumulator
#print axioms SmcTuring.Native.GuardSetupImage.capture_trace
#print axioms SmcTuring.Native.GuardSetupImage.capture_owned_run
#print axioms SmcTuring.Native.GuardSetupImage.resume_ready
#print axioms SmcTuring.Native.GuardSetupImage.resumed_load_frame
#print axioms SmcTuring.Native.GuardSetupImage.candidate_ready
#print axioms SmcTuring.Native.GuardSetupImage.candidate_owned
#print axioms SmcTuring.Native.GuardSetupImage.candidate_accumulator
#print axioms SmcTuring.Native.GuardSetupImage.scratch_ready
#print axioms SmcTuring.Native.GuardSetupImage.scratched_load_frame
#print axioms SmcTuring.Native.GuardSetupImage.boundary_ready
#print axioms SmcTuring.Native.GuardSetupImage.boundary_owned
#print axioms SmcTuring.Native.GuardSetupImage.accumulator
#print axioms SmcTuring.Native.GuardSetupImage.saved_resume
#print axioms SmcTuring.Native.GuardSetupImage.saved_candidate
#print axioms SmcTuring.Native.GuardSetupImage.stack
#print axioms SmcTuring.Native.GuardSetupImage.carry
#print axioms SmcTuring.Native.GuardSetupImage.pc
#print axioms SmcTuring.Native.GuardSetupImage.position
#print axioms SmcTuring.Native.GuardSetupImage.finish_intact
#print axioms SmcTuring.Native.GuardSetupImage.top_reusable
#print axioms SmcTuring.Native.GuardSetupImage.load_frame
#print axioms SmcTuring.Native.GuardSetupImage.trace
#print axioms SmcTuring.Native.GuardSetupImage.owned_run
#print axioms SmcTuring.Native.GuardSetupImage.memory_effect
#print axioms SmcTuring.Native.GuardSetupImage.memory_frame
#print axioms SmcTuring.Native.GuardSetupImage.boundary_value_reusable
#print axioms SmcTuring.Native.GuardSetupImage.boundary_pointer_reusable
#print axioms SmcTuring.Native.GuardSetupImage.run
#print axioms SmcTuring.Native.GuardSetupImage.program_count
#print axioms SmcTuring.Native.ReadScalarImage.transport_ready
#print axioms SmcTuring.Native.ReadScalarImage.scalar_ready
#print axioms SmcTuring.Native.ReadScalarImage.read_value_from
#print axioms SmcTuring.Native.ReadScalarImage.read_accumulator
#print axioms SmcTuring.Native.ReadScalarImage.target_before_scalar
#print axioms SmcTuring.Native.ReadScalarImage.trace
#print axioms SmcTuring.Native.ReadScalarImage.owned_run
#print axioms SmcTuring.Native.ReadScalarImage.written_value
#print axioms SmcTuring.Native.ReadScalarImage.memory_effect
#print axioms SmcTuring.Native.ReadScalarImage.accumulator
#print axioms SmcTuring.Native.ReadScalarImage.stack
#print axioms SmcTuring.Native.ReadScalarImage.carry
#print axioms SmcTuring.Native.ReadScalarImage.xor_carry
#print axioms SmcTuring.Native.ReadScalarImage.and_carry
#print axioms SmcTuring.Native.ReadScalarImage.pc
#print axioms SmcTuring.Native.ReadScalarImage.position
#print axioms SmcTuring.Native.ReadScalarImage.finish_intact
#print axioms SmcTuring.Native.ReadScalarImage.top_reusable
#print axioms SmcTuring.Native.ReadScalarImage.load_frame
#print axioms SmcTuring.Native.ReadScalarImage.memory_frame
#print axioms SmcTuring.Native.ReadScalarImage.run
#print axioms SmcTuring.Native.ReadScalarImage.program_count
#print axioms SmcTuring.Native.GuardSelectionImage.transport_ready
#print axioms SmcTuring.Native.GuardSelectionImage.first_load_frame
#print axioms SmcTuring.Native.GuardSelectionImage.second_ready
#print axioms SmcTuring.Native.GuardSelectionImage.second_load_frame
#print axioms SmcTuring.Native.GuardSelectionImage.third_ready
#print axioms SmcTuring.Native.GuardSelectionImage.third_load_frame
#print axioms SmcTuring.Native.GuardSelectionImage.fourth_ready
#print axioms SmcTuring.Native.GuardSelectionImage.fourth_load_frame
#print axioms SmcTuring.Native.GuardSelectionImage.continuation_owned
#print axioms SmcTuring.Native.GuardSelectionImage.terminal_owned
#print axioms SmcTuring.Native.GuardSelectionImage.mask_owned
#print axioms SmcTuring.Native.GuardSelectionImage.first_read_value
#print axioms SmcTuring.Native.GuardSelectionImage.second_read_value
#print axioms SmcTuring.Native.GuardSelectionImage.third_read_value
#print axioms SmcTuring.Native.GuardSelectionImage.fourth_read_value
#print axioms SmcTuring.Native.GuardSelectionImage.first_selected
#print axioms SmcTuring.Native.GuardSelectionImage.second_selected
#print axioms SmcTuring.Native.GuardSelectionImage.third_selected
#print axioms SmcTuring.Native.GuardSelectionImage.fourth_selected
#print axioms SmcTuring.Native.GuardSelectionImage.selected_slot_separate
#print axioms SmcTuring.Native.GuardSelectionImage.collapse_memory
#print axioms SmcTuring.Native.GuardSelectionImage.first_memory
#print axioms SmcTuring.Native.GuardSelectionImage.second_memory
#print axioms SmcTuring.Native.GuardSelectionImage.third_memory
#print axioms SmcTuring.Native.GuardSelectionImage.fourth_memory
#print axioms SmcTuring.Native.GuardSelectionImage.call_location
#print axioms SmcTuring.Native.GuardSelectionImage.call_top
#print axioms SmcTuring.Native.GuardSelectionImage.call_intact
#print axioms SmcTuring.Native.GuardSelectionImage.call_stack_ready
#print axioms SmcTuring.Native.GuardSelectionImage.call_trace
#print axioms SmcTuring.Native.GuardSelectionImage.call_owned_run
#print axioms SmcTuring.Native.GuardSelectionImage.before_trace
#print axioms SmcTuring.Native.GuardSelectionImage.before_owned_run
#print axioms SmcTuring.Native.GuardSelectionImage.trace
#print axioms SmcTuring.Native.GuardSelectionImage.owned_run
#print axioms SmcTuring.Native.GuardSelectionImage.pc
#print axioms SmcTuring.Native.GuardSelectionImage.selects
#print axioms SmcTuring.Native.GuardSelectionImage.stack
#print axioms SmcTuring.Native.GuardSelectionImage.carry
#print axioms SmcTuring.Native.GuardSelectionImage.accumulator
#print axioms SmcTuring.Native.GuardSelectionImage.call_memory
#print axioms SmcTuring.Native.GuardSelectionImage.memory_effect
#print axioms SmcTuring.Native.GuardSelectionImage.memory_frame
#print axioms SmcTuring.Native.GuardSelectionImage.finish_intact
#print axioms SmcTuring.Native.GuardSelectionImage.load_frame
#print axioms SmcTuring.Native.GuardSelectionImage.top_reusable
#print axioms SmcTuring.Native.GuardSelectionImage.selected_word
#print axioms SmcTuring.Native.GuardSelectionImage.slot_word
#print axioms SmcTuring.Native.GuardSelectionImage.run
#print axioms SmcTuring.Native.GuardSelectionImage.program_count
#print axioms SmcTuring.Native.BorrowMaskImage.transport_ready
#print axioms SmcTuring.Native.GuardSetupImage.transport_ready
#print axioms SmcTuring.Native.GuardImage.transport_ready
#print axioms SmcTuring.Native.GuardImage.different_roles
#print axioms SmcTuring.Native.GuardImage.setup_frame_role
#print axioms SmcTuring.Native.GuardImage.borrow_ready
#print axioms SmcTuring.Native.GuardImage.borrow_frame_role
#print axioms SmcTuring.Native.GuardImage.selection_ready
#print axioms SmcTuring.Native.GuardImage.borrow_carry
#print axioms SmcTuring.Native.GuardImage.mask_value
#print axioms SmcTuring.Native.GuardImage.saved_resume
#print axioms SmcTuring.Native.GuardImage.terminal_owned
#print axioms SmcTuring.Native.GuardImage.terminal_value
#print axioms SmcTuring.Native.GuardImage.pc
#print axioms SmcTuring.Native.GuardImage.trace
#print axioms SmcTuring.Native.GuardImage.owned_run
#print axioms SmcTuring.Native.GuardImage.stack
#print axioms SmcTuring.Native.GuardImage.carry
#print axioms SmcTuring.Native.GuardImage.accumulator
#print axioms SmcTuring.Native.GuardImage.finish_intact
#print axioms SmcTuring.Native.GuardImage.top_reusable
#print axioms SmcTuring.Native.GuardImage.load_frame
#print axioms SmcTuring.Native.GuardImage.selected_word
#print axioms SmcTuring.Native.GuardImage.slot_word
#print axioms SmcTuring.Native.GuardImage.memory_effect
#print axioms SmcTuring.Native.GuardImage.memory_frame
#print axioms SmcTuring.Native.GuardImage.run
#print axioms SmcTuring.Native.GuardImage.program_count
#print axioms SmcTuring.Native.GuardInvocationImage.caller_run
#print axioms SmcTuring.Native.GuardInvocationImage.caller_ready
#print axioms SmcTuring.Native.GuardInvocationImage.caller_pc
#print axioms SmcTuring.Native.GuardInvocationImage.caller_memory
#print axioms SmcTuring.Native.GuardInvocationImage.caller_memory_nat
#print axioms SmcTuring.Native.GuardInvocationImage.caller_return_word
#print axioms SmcTuring.Native.GuardInvocationImage.caller_trace
#print axioms SmcTuring.Native.GuardInvocationImage.caller_owned_run
#print axioms SmcTuring.Native.GuardInvocationImage.caller_intact
#print axioms SmcTuring.Native.GuardInvocationImage.caller_load_frame
#print axioms SmcTuring.Native.GuardInvocationImage.caller_role_frame
#print axioms SmcTuring.Native.GuardInvocationImage.capture_label_owned
#print axioms SmcTuring.Native.GuardInvocationImage.body_ready
#print axioms SmcTuring.Native.GuardInvocationImage.candidate_value
#print axioms SmcTuring.Native.GuardInvocationImage.boundary_value
#print axioms SmcTuring.Native.GuardInvocationImage.borrowed_after_caller
#print axioms SmcTuring.Native.GuardInvocationImage.terminal_value
#print axioms SmcTuring.Native.GuardInvocationImage.pc
#print axioms SmcTuring.Native.GuardInvocationImage.trace
#print axioms SmcTuring.Native.GuardInvocationImage.owned_run
#print axioms SmcTuring.Native.GuardInvocationImage.stack
#print axioms SmcTuring.Native.GuardInvocationImage.carry
#print axioms SmcTuring.Native.GuardInvocationImage.accumulator
#print axioms SmcTuring.Native.GuardInvocationImage.finish_intact
#print axioms SmcTuring.Native.GuardInvocationImage.top_reusable
#print axioms SmcTuring.Native.GuardInvocationImage.load_frame
#print axioms SmcTuring.Native.GuardInvocationImage.selected_word
#print axioms SmcTuring.Native.GuardInvocationImage.slot_word
#print axioms SmcTuring.Native.GuardInvocationImage.memory_effect
#print axioms SmcTuring.Native.GuardInvocationImage.memory_frame
#print axioms SmcTuring.Native.GuardInvocationImage.run
#print axioms SmcTuring.Native.GuardInvocationImage.program_count
#print axioms SmcTuring.Native.SourceValues.natural_injective
#print axioms SmcTuring.Native.SourceValues.word_toNat
#print axioms SmcTuring.Native.SourceValues.word_injective
#print axioms SmcTuring.Native.SourceValues.word_borrow
#print axioms SmcTuring.Native.SourceValues.offset_sum_below_boundary
#print axioms SmcTuring.Native.SourceValues.offset_sum_borrow
#print axioms SmcTuring.Native.SourceValues.address_candidate_borrow
#print axioms SmcTuring.Native.SourceValues.typed_guard_borrow
#print axioms SmcTuring.Native.SourceValues.typed_guard_pc
#print axioms SmcTuring.Native.SourceValues.address_guard_borrow
#print axioms SmcTuring.Native.SourceValues.address_guard_pc
#print axioms SmcTuring.Native.SourceValues.source_address_encoded
#print axioms SmcTuring.Native.SourceValues.source_address_toNat
#print axioms SmcTuring.Native.SourceData.field_fits
#print axioms SmcTuring.Native.SourceData.register_fits
#print axioms SmcTuring.Native.SourceData.heap_index_inside
#print axioms SmcTuring.Native.SourceData.heap_fits
#print axioms SmcTuring.Native.SourceData.register_toNat
#print axioms SmcTuring.Native.SourceData.heap_toNat
#print axioms SmcTuring.Native.SourceData.register_owned
#print axioms SmcTuring.Native.SourceData.heap_owned
#print axioms SmcTuring.Native.SourceData.register_injective
#print axioms SmcTuring.Native.SourceData.heap_address_injective
#print axioms SmcTuring.Native.SourceData.heap_injective
#print axioms SmcTuring.Native.SourceData.register_heap_separate
#print axioms SmcTuring.Native.SourceData.field_not_before
#print axioms SmcTuring.Native.SourceData.register_not_before
#print axioms SmcTuring.Native.SourceData.heap_not_before
#print axioms SmcTuring.Native.SourceData.boundary_fits
#print axioms SmcTuring.Native.SourceData.value_fits
#print axioms SmcTuring.Native.SourceData.address_fits
#print axioms SmcTuring.Native.SourceData.initial_register_value
#print axioms SmcTuring.Native.SourceData.initial_heap_value
#print axioms SmcTuring.Native.SourceData.initial_rep
#print axioms SmcTuring.Native.ImmediateImage.read_value
#print axioms SmcTuring.Native.ImmediateImage.destination_value
#print axioms SmcTuring.Native.ImmediateImage.other_register_frame
#print axioms SmcTuring.Native.ImmediateImage.heap_frame
#print axioms SmcTuring.Native.ImmediateImage.represented
#print axioms SmcTuring.Native.ImmediateImage.source_step
#print axioms SmcTuring.Native.ImmediateImage.memory_effect
#print axioms SmcTuring.Native.ImmediateImage.correct
#print axioms SmcTuring.Native.GuardInvocationImage.metadata_owned
#print axioms SmcTuring.Native.GuardInvocationImage.metadata_not_slot
#print axioms SmcTuring.Native.GuardInvocationImage.transport_ready
#print axioms SmcTuring.Native.SourceData.base_fits
#print axioms SmcTuring.Native.SourceData.metadata_fits
#print axioms SmcTuring.Native.OffsetGuardImage.field_fits
#print axioms SmcTuring.Native.OffsetGuardImage.data_not_field
#print axioms SmcTuring.Native.OffsetGuardImage.metadata_after_read
#print axioms SmcTuring.Native.OffsetGuardImage.guard_ready
#print axioms SmcTuring.Native.OffsetGuardImage.read_value
#print axioms SmcTuring.Native.OffsetGuardImage.candidate_after_read
#print axioms SmcTuring.Native.OffsetGuardImage.boundary_after_read
#print axioms SmcTuring.Native.OffsetGuardImage.terminal_after_read
#print axioms SmcTuring.Native.OffsetGuardImage.after_read_data_frame
#print axioms SmcTuring.Native.OffsetGuardImage.data_frame
#print axioms SmcTuring.Native.OffsetGuardImage.represented
#print axioms SmcTuring.Native.OffsetGuardImage.trace
#print axioms SmcTuring.Native.OffsetGuardImage.owned_run
#print axioms SmcTuring.Native.OffsetGuardImage.pc
#print axioms SmcTuring.Native.OffsetGuardImage.stack
#print axioms SmcTuring.Native.OffsetGuardImage.carry
#print axioms SmcTuring.Native.OffsetGuardImage.accumulator
#print axioms SmcTuring.Native.OffsetGuardImage.finish_intact
#print axioms SmcTuring.Native.OffsetGuardImage.top_reusable
#print axioms SmcTuring.Native.OffsetGuardImage.selected_word
#print axioms SmcTuring.Native.OffsetGuardImage.slot_word
#print axioms SmcTuring.Native.OffsetGuardImage.memory_frame
#print axioms SmcTuring.Native.OffsetGuardImage.run
#print axioms SmcTuring.Native.OffsetGuardImage.program_count
#print axioms SmcTuring.Native.OffsetGuardImage.correct
#print axioms SmcTuring.Native.OffsetGuardImage.load_frame
#print axioms SmcTuring.Native.PointerImage.metadata_owned
#print axioms SmcTuring.Native.PointerImage.transport_ready
#print axioms SmcTuring.Native.PointerImage.base_load_frame
#print axioms SmcTuring.Native.PointerImage.offset_ready
#print axioms SmcTuring.Native.PointerImage.offset_load_frame
#print axioms SmcTuring.Native.PointerImage.word_ready
#print axioms SmcTuring.Native.PointerImage.field_fits
#print axioms SmcTuring.Native.PointerImage.data_not_field
#print axioms SmcTuring.Native.PointerImage.base_value
#print axioms SmcTuring.Native.PointerImage.offset_value
#print axioms SmcTuring.Native.PointerImage.pointer_after_base
#print axioms SmcTuring.Native.PointerImage.pointer_after_offset
#print axioms SmcTuring.Native.PointerImage.word_value
#print axioms SmcTuring.Native.PointerImage.candidate
#print axioms SmcTuring.Native.PointerImage.pointer
#print axioms SmcTuring.Native.PointerImage.load_frame
#print axioms SmcTuring.Native.PointerImage.represented
#print axioms SmcTuring.Native.PointerImage.trace
#print axioms SmcTuring.Native.PointerImage.owned_run
#print axioms SmcTuring.Native.PointerImage.pc
#print axioms SmcTuring.Native.PointerImage.finish_intact
#print axioms SmcTuring.Native.PointerImage.source_address
#print axioms SmcTuring.Native.PointerImage.run
#print axioms SmcTuring.Native.PointerImage.program_count
#print axioms SmcTuring.Native.PointerImage.correct
#print axioms SmcTuring.Native.AddressImage.pointer_metadata_frame
#print axioms SmcTuring.Native.AddressImage.pointer_ready
#print axioms SmcTuring.Native.AddressImage.guard_metadata_frame
#print axioms SmcTuring.Native.AddressImage.guard_ready
#print axioms SmcTuring.Native.AddressImage.candidate
#print axioms SmcTuring.Native.AddressImage.boundary
#print axioms SmcTuring.Native.AddressImage.terminal
#print axioms SmcTuring.Native.AddressImage.accepted_pc
#print axioms SmcTuring.Native.AddressImage.pc
#print axioms SmcTuring.Native.AddressImage.accepted_trace
#print axioms SmcTuring.Native.AddressImage.trace
#print axioms SmcTuring.Native.AddressImage.accepted_owned_run
#print axioms SmcTuring.Native.AddressImage.owned_run
#print axioms SmcTuring.Native.AddressImage.accepted_data_frame
#print axioms SmcTuring.Native.AddressImage.accepted_represented
#print axioms SmcTuring.Native.AddressImage.represented
#print axioms SmcTuring.Native.AddressImage.pointer
#print axioms SmcTuring.Native.AddressImage.finish_intact
#print axioms SmcTuring.Native.AddressImage.carry
#print axioms SmcTuring.Native.AddressImage.load_frame
#print axioms SmcTuring.Native.AddressImage.top_reusable
#print axioms SmcTuring.Native.AddressImage.stack
#print axioms SmcTuring.Native.AddressImage.run
#print axioms SmcTuring.Native.AddressImage.program_count
#print axioms SmcTuring.Native.AddressImage.correct
#print axioms SmcTuring.Native.ReadInvocationImage.transport_ready_pointer
#print axioms SmcTuring.Native.ReadScalarImage.transport_ready_pointer
#print axioms SmcTuring.Native.StoreInvocationImage.transport_ready_pointer
#print axioms SmcTuring.Native.StoreInvocationImage.written_value
#print axioms SmcTuring.Native.StoreInvocationImage.load_frame
#print axioms SmcTuring.Native.SourceWriteImage.register_rep
#print axioms SmcTuring.Native.SourceWriteImage.heap_rep
#print axioms SmcTuring.Native.LoadImage.pointer_inside
#print axioms SmcTuring.Native.LoadImage.read_ready
#print axioms SmcTuring.Native.LoadImage.read_value
#print axioms SmcTuring.Native.LoadImage.source_step
#print axioms SmcTuring.Native.LoadImage.represented
#print axioms SmcTuring.Native.LoadImage.trace
#print axioms SmcTuring.Native.LoadImage.owned_run
#print axioms SmcTuring.Native.LoadImage.pc
#print axioms SmcTuring.Native.LoadImage.finish_intact
#print axioms SmcTuring.Native.LoadImage.top_reusable
#print axioms SmcTuring.Native.LoadImage.stack
#print axioms SmcTuring.Native.LoadImage.carry
#print axioms SmcTuring.Native.LoadImage.load_frame
#print axioms SmcTuring.Native.LoadImage.run
#print axioms SmcTuring.Native.LoadImage.program_count
#print axioms SmcTuring.Native.LoadImage.correct
#print axioms SmcTuring.Native.StoreImage.pointer_inside
#print axioms SmcTuring.Native.StoreImage.source_label_frame
#print axioms SmcTuring.Native.StoreImage.read_ready
#print axioms SmcTuring.Native.StoreImage.read_value
#print axioms SmcTuring.Native.StoreImage.pointer_after_read
#print axioms SmcTuring.Native.StoreImage.store_ready
#print axioms SmcTuring.Native.StoreImage.after_read_represented
#print axioms SmcTuring.Native.StoreImage.source_step
#print axioms SmcTuring.Native.StoreImage.represented
#print axioms SmcTuring.Native.StoreImage.accepted_trace
#print axioms SmcTuring.Native.StoreImage.trace
#print axioms SmcTuring.Native.StoreImage.accepted_owned_run
#print axioms SmcTuring.Native.StoreImage.owned_run
#print axioms SmcTuring.Native.StoreImage.pc
#print axioms SmcTuring.Native.StoreImage.finish_intact
#print axioms SmcTuring.Native.StoreImage.top_reusable
#print axioms SmcTuring.Native.StoreImage.stack
#print axioms SmcTuring.Native.StoreImage.carry
#print axioms SmcTuring.Native.StoreImage.load_frame
#print axioms SmcTuring.Native.StoreImage.run
#print axioms SmcTuring.Native.StoreImage.program_count
#print axioms SmcTuring.Native.StoreImage.correct
#print axioms SmcTuring.Native.BlockImage.address_ready_from_snapshot
#print axioms SmcTuring.Native.BlockImage.ready_from_snapshot
#print axioms SmcTuring.Native.BlockImage.correct
#print axioms SmcTuring.Native.BlockImage.load_frame
#print axioms SmcTuring.Native.BlockImage.load_pointer
#print axioms SmcTuring.Native.BlockImage.store_pointer
#print axioms SmcTuring.Native.ProgramImage.block_ready
#print axioms SmcTuring.Native.ProgramImage.block_frames
#print axioms SmcTuring.Native.ProgramImage.block_selected
#print axioms SmcTuring.Native.ProgramImage.block_invariant
#print axioms SmcTuring.Native.ProgramImage.correct
#print axioms SmcTuring.Native.ProgramImage.successful_boundary
#print axioms SmcTuring.Native.LoopImage.correct
#print axioms SmcTuring.Native.LoopImage.pass_correct
#print axioms SmcTuring.Native.KernelImage.lower_properties
#print axioms SmcTuring.Native.KernelImage.compile_properties
#print axioms SmcTuring.Native.KernelImage.compile_total
#print axioms SmcTuring.Native.KernelImage.kernel_supported
#print axioms SmcTuring.Native.KernelImage.fixed_kernel
#print axioms SmcTuring.Native.KernelPackets.ordered_size
#print axioms SmcTuring.Native.KernelPackets.ordered_placement
#print axioms SmcTuring.Native.KernelPackets.scalar_size
#print axioms SmcTuring.Native.KernelPackets.read_scalar_size
#print axioms SmcTuring.Native.KernelPackets.read_scalar_placement
#print axioms SmcTuring.Native.KernelPackets.source_ordered
#print axioms SmcTuring.Native.KernelPackets.source_continuation
#print axioms SmcTuring.Native.KernelPackets.ordered_append
#print axioms SmcTuring.Native.KernelPackets.program_ordered
#print axioms SmcTuring.Native.KernelPackets.global_placement
#print axioms SmcTuring.Native.KernelPackets.global_read_scalar
#print axioms SmcTuring.Native.KernelPackets.source_packet_count
#print axioms SmcTuring.Native.KernelPackets.program_packet_count
#print axioms SmcTuring.Native.KernelPackets.kernel_packet_count
#print axioms SmcTuring.Native.GuardPackets.ordered
#print axioms SmcTuring.Native.GuardPackets.packet_count
#print axioms SmcTuring.Native.GuardPackets.global_placement
#print axioms SmcTuring.Native.AlignedTemplates.padded_size
#print axioms SmcTuring.Native.AlignedTemplates.padded_place
#print axioms SmcTuring.Native.AlignedTemplates.padded_within
#print axioms SmcTuring.Native.AlignedTemplates.reader_extent
#print axioms SmcTuring.Native.AlignedTemplates.scalar_extent
#print axioms SmcTuring.Native.AlignedTemplates.reader_constructed
#print axioms SmcTuring.Native.AlignedTemplates.scalar_constructed
#print axioms SmcTuring.Native.AlignedPool.pool_extent
#print axioms SmcTuring.Native.AlignedPool.end_cursor
#print axioms SmcTuring.Native.AlignedPool.reader_cursor
#print axioms SmcTuring.Native.AlignedPool.pool_constructed
#print axioms SmcTuring.Native.RoleInitialization.reader_count
#print axioms SmcTuring.Native.RoleInitialization.field_count
#print axioms SmcTuring.Native.RoleInitialization.reader_at_index
#print axioms SmcTuring.Native.RoleInitialization.field_at_index
#print axioms SmcTuring.Native.RoleInitialization.reader_initialized
#print axioms SmcTuring.Native.RoleInitialization.field_initialized
#print axioms SmcTuring.Native.ByteLengths.source_end
#print axioms SmcTuring.Native.ByteLengths.source_size
#print axioms SmcTuring.Native.ByteLengths.guard_end
#print axioms SmcTuring.Native.ByteLengths.guard_size
#print axioms SmcTuring.Native.ByteLengths.program_size
#print axioms SmcTuring.Native.ByteLengths.compile_extent
#print axioms SmcTuring.Native.ByteLengths.kernel_span
#print axioms SmcTuring.Native.MetadataGeometry.scalar_step
#print axioms SmcTuring.Native.MetadataGeometry.scalar_step_aligned
#print axioms SmcTuring.Native.MetadataGeometry.scalar_field_affine
#print axioms SmcTuring.Native.MetadataGeometry.field_affine
#print axioms SmcTuring.Native.MetadataGeometry.field_index_injective
#print axioms SmcTuring.Native.MetadataGeometry.field_position_injective
#print axioms SmcTuring.Native.MetadataGeometry.field_word_injective
#print axioms SmcTuring.Native.LayoutPass.reader_extent
#print axioms SmcTuring.Native.LayoutPass.field_extent
#print axioms SmcTuring.Native.LayoutPass.guard_extent
#print axioms SmcTuring.Native.LayoutPass.prefix_extent
#print axioms SmcTuring.Native.LayoutPass.compiled_extent
#print axioms SmcTuring.Native.LayoutPass.body_extent
#print axioms SmcTuring.Native.LayoutPass.backedge_extent
#print axioms SmcTuring.Native.LayoutPass.grid_aligned
#print axioms SmcTuring.Native.EmittedImage.reserve_size
#print axioms SmcTuring.Native.EmittedImage.reserve_place
#print axioms SmcTuring.Native.EmittedImage.body_extent
#print axioms SmcTuring.Native.EmittedImage.whole_extent
#print axioms SmcTuring.Native.EmittedImage.grid_gap
#print axioms SmcTuring.Native.EmittedImage.grid_enough
#print axioms SmcTuring.Native.EmittedImage.initially_intact
#print axioms SmcTuring.Native.EmittedImage.initially_represented
#print axioms SmcTuring.Native.ImageInitialization.metadata_within
#print axioms SmcTuring.Native.ImageInitialization.reader_initialized
#print axioms SmcTuring.Native.ImageInitialization.field_initialized
#print axioms SmcTuring.Native.Recontext.block_instruction
#print axioms SmcTuring.Native.Recontext.block_start
#print axioms SmcTuring.Native.Recontext.block_continuation
#print axioms SmcTuring.Native.Recontext.block_context
#print axioms SmcTuring.Native.Recontext.block_segments
#print axioms SmcTuring.Native.Recontext.program_segments
#print axioms SmcTuring.Native.Recontext.lower
#print axioms SmcTuring.Native.Recontext.compile
#print axioms SmcTuring.Native.Recontext.layout_roles
#print axioms SmcTuring.Native.Recontext.guard_packets
#print axioms SmcTuring.Native.Recontext.layout_prefix
#print axioms SmcTuring.Native.Recontext.emitted_image
#print axioms SmcTuring.Native.Recontext.constructed_kernel
#print axioms SmcTuring.Native.PoolGeometry.cursor_succ
#print axioms SmcTuring.Native.PoolGeometry.reader_next_start
#print axioms SmcTuring.Native.PoolGeometry.reader_start_affine
#print axioms SmcTuring.Native.PoolGeometry.reader_bound
#print axioms SmcTuring.Native.PoolGeometry.scalar_end
#print axioms SmcTuring.Native.PoolGeometry.scalar_bound
#print axioms SmcTuring.Native.BoundedInitialization.metadata_before_grid
#print axioms SmcTuring.Native.BoundedInitialization.metadata_fits
#print axioms SmcTuring.Native.BoundedInitialization.reader_limit_le
#print axioms SmcTuring.Native.BoundedInitialization.reader_fits
#print axioms SmcTuring.Native.BoundedInitialization.field_fits
#print axioms SmcTuring.Native.BoundedInitialization.field_bound
#print axioms SmcTuring.Native.BoundedInitialization.field_before_grid
#print axioms SmcTuring.Native.BoundedInitialization.readers_initialized
#print axioms SmcTuring.Native.BoundedInitialization.fields_initialized
#print axioms SmcTuring.Native.BoundedInitialization.field_owned
#print axioms SmcTuring.Native.BoundedInitialization.reader_owned
#print axioms SmcTuring.Native.BoundedInitialization.reader_target_owned
#print axioms SmcTuring.Native.BoundedInitialization.stack_top_value
#print axioms SmcTuring.Native.Assembly.exists_image
#print axioms SmcTuring.Native.Assembly.common_context
#print axioms SmcTuring.Native.Assembly.boundary_bound
#print axioms SmcTuring.Native.Assembly.backedge_fits
#print axioms SmcTuring.Native.Assembly.compiled_bounds
#print axioms SmcTuring.Native.Assembly.source_segment_within
#print axioms SmcTuring.Native.Assembly.source_read_scalar_within
#print axioms SmcTuring.Native.Assembly.initially_intact
#print axioms SmcTuring.Native.Assembly.initially_represented
#print axioms SmcTuring.Native.GuardPlacement.guard_within
#print axioms SmcTuring.Native.GuardPlacement.segment_within
#print axioms SmcTuring.Native.GuardPlacement.read_scalar_within
#print axioms SmcTuring.Native.GuardPlacement.capture_within
#print axioms SmcTuring.Native.GuardPlacement.capture_constructed
#print axioms SmcTuring.Native.RoleSeparation.position_injective
#print axioms SmcTuring.Native.RoleSeparation.position_bounds
#print axioms SmcTuring.Native.RoleSeparation.operand_owned
#print axioms SmcTuring.Native.RoleSeparation.position_fits
#print axioms SmcTuring.Native.RoleSeparation.word_injective
#print axioms SmcTuring.Native.RoleSeparation.field_different
#print axioms SmcTuring.Native.RoleSeparation.reader_field_different
#print axioms SmcTuring.Native.RoleSeparation.capture_field_different
#print axioms SmcTuring.Native.RoleSeparation.reader_different
#print axioms SmcTuring.Native.RoleSeparation.guard_role_word
#print axioms SmcTuring.Native.RoleSeparation.guard_roles_injective
#print axioms SmcTuring.Native.ReadinessAtoms.compact_delta
#print axioms SmcTuring.Native.ReadinessAtoms.destination_bounds
#print axioms SmcTuring.Native.ReadinessAtoms.destination_owned
#print axioms SmcTuring.Native.ReadinessAtoms.destination_not_field
#print axioms SmcTuring.Native.ReadinessAtoms.calls_bounds
#print axioms SmcTuring.Native.ReadinessAtoms.calls_ranges
#print axioms SmcTuring.Native.ReadinessAtoms.reader_ready
#print axioms SmcTuring.Native.ReadinessAtoms.destination_fits
#print axioms SmcTuring.Native.ReadinessAtoms.scalar_ready
#print axioms SmcTuring.Native.ReadinessAtoms.read_scalar_ready
#print axioms SmcTuring.Native.GuardReadiness.setup_ready
#print axioms SmcTuring.Native.GuardReadiness.borrow_ready
#print axioms SmcTuring.Native.GuardReadiness.selection_ready
#print axioms SmcTuring.Native.GuardReadiness.guard_ready
#print axioms SmcTuring.Native.LoopInitialization.frozen_owned
#print axioms SmcTuring.Native.LoopInitialization.frozen_not_slot
#print axioms SmcTuring.Native.LoopInitialization.backedge_within
#print axioms SmcTuring.Native.LoopInitialization.initial_invariant
#print axioms SmcTuring.Native.LoopInitialization.loop_setup
#print axioms SmcTuring.Native.CompiledLayout.compile_membership
#print axioms SmcTuring.Native.CompiledLayout.block_lowered
#print axioms SmcTuring.Native.CompiledLayout.offset_field_position
#print axioms SmcTuring.Native.CompiledLayout.pointer_field_position
#print axioms SmcTuring.Native.CompiledLayout.address_field_position
#print axioms SmcTuring.Native.CompiledLayout.guard_metadata_word
#print axioms SmcTuring.Native.CompiledLayout.pointer_metadata_word
#print axioms SmcTuring.Native.CompiledLayout.guard_metadata_frozen
#print axioms SmcTuring.Native.CompiledLayout.pointer_metadata_frozen
#print axioms SmcTuring.Native.CompiledLayout.address_static_frozen
#print axioms SmcTuring.Native.CompiledLayout.static_frozen
#print axioms SmcTuring.Native.CompiledLayout.frozen_not_address_field
#print axioms SmcTuring.Native.CompiledLayout.frozen_before_grid
#print axioms SmcTuring.Native.CompiledLayout.frozen_outside
#print axioms SmcTuring.Native.InvocationReadiness.reader_for
#print axioms SmcTuring.Native.InvocationReadiness.update_for
#print axioms SmcTuring.Native.InvocationReadiness.guard_for
#print axioms SmcTuring.Native.InvocationReadiness.store_for
#print axioms SmcTuring.Native.SourceSeparation.guard_offset_separate
#print axioms SmcTuring.Native.SourceSeparation.guard_pointer_separate
#print axioms SmcTuring.Native.SourceSeparation.pointer_offset_separate
#print axioms SmcTuring.Native.SourceSeparation.pointer_mutable_separate
#print axioms SmcTuring.Native.SourceSeparation.offset_fields_before
#print axioms SmcTuring.Native.SourceSeparation.pointer_fields_before
#print axioms SmcTuring.Native.SourceSeparation.pointer_control_separate
#print axioms SmcTuring.Native.SourceSeparation.register_label_address_separate
#print axioms SmcTuring.Native.SourceReadiness.immediate_ready
#print axioms SmcTuring.Native.SourceReadiness.address_ready
#print axioms SmcTuring.Native.SourceReadiness.load_ready
#print axioms SmcTuring.Native.SourceReadiness.store_ready
#print axioms SmcTuring.Native.SourceReadiness.block_ready
#print axioms SmcTuring.Native.ProgramCertificate.pointer_layout
#print axioms SmcTuring.Native.ProgramCertificate.source_setup
#print axioms SmcTuring.Native.ProgramCertificate.end_word
#print axioms SmcTuring.Native.ProgramCertificate.entry_word
#print axioms SmcTuring.Native.ProgramCertificate.linked
#print axioms SmcTuring.Native.ProgramCertificate.kernel_correct
#print axioms SmcTuring.Native.ProgramCertificate.closed_pass_correct

#print axioms SmcTuring.Native.MemoryRegion.agree_refl
#print axioms SmcTuring.Native.MemoryRegion.agree_symm
#print axioms SmcTuring.Native.MemoryRegion.agree_trans
#print axioms SmcTuring.Native.MemoryRegion.contains_byte
#print axioms SmcTuring.Native.MemoryRegion.bytes_agree
#print axioms SmcTuring.Native.MemoryRegion.load_agree
#print axioms SmcTuring.Native.MemoryRegion.put_bytes_agree
#print axioms SmcTuring.Native.MemoryRegion.put_word_agree
#print axioms SmcTuring.Native.MemoryRegion.put_word_outside
#print axioms SmcTuring.Native.MemoryRegion.expanded_snapshot_agrees
#print axioms SmcTuring.Native.MemoryRegion.snapshot_expand
#print axioms SmcTuring.Native.MemoryRegion.store_agrees

#print axioms SmcTuring.Native.RegionExecution.state_agree_refl
#print axioms SmcTuring.Native.RegionExecution.execute_agrees
#print axioms SmcTuring.Native.RegionExecution.write_address_agrees
#print axioms SmcTuring.Native.RegionExecution.write_value_agrees
#print axioms SmcTuring.Native.RegionExecution.fetch_agrees
#print axioms SmcTuring.Native.RegionExecution.state_agree_symm
#print axioms SmcTuring.Native.RegionExecution.read_address_agrees
#print axioms SmcTuring.Native.RegionExecution.read_within_agrees
#print axioms SmcTuring.Native.RegionExecution.fetch_within_agrees
#print axioms SmcTuring.Native.RegionExecution.safe_agrees
#print axioms SmcTuring.Native.RegionExecution.trace_agrees
#print axioms SmcTuring.Native.RegionExecution.owned_run_agrees
#print axioms SmcTuring.Native.RegionExecution.run_outside

#print axioms SmcTuring.Native.LoadedExecution.snapshot_agrees
#print axioms SmcTuring.Native.LoadedExecution.snapshot_expand
#print axioms SmcTuring.Native.LoadedExecution.step_complete
#print axioms SmcTuring.Native.LoadedExecution.step_sound
#print axioms SmcTuring.Native.LoadedExecution.trace_complete
#print axioms SmcTuring.Native.LoadedExecution.trace_sound

#print axioms SmcTuring.Native.FiniteFootprint.join_left
#print axioms SmcTuring.Native.FiniteFootprint.join_right
#print axioms SmcTuring.Native.FiniteFootprint.contains_widen
#print axioms SmcTuring.Native.FiniteFootprint.safe_widen
#print axioms SmcTuring.Native.FiniteFootprint.safe_run_widen
#print axioms SmcTuring.Native.FiniteFootprint.event_safe
#print axioms SmcTuring.Native.FiniteFootprint.run_safe
#print axioms SmcTuring.Native.FiniteFootprint.loaded_prefix

#print axioms SmcTuring.Native.ProgramLoaded.register_contained
#print axioms SmcTuring.Native.ProgramLoaded.heap_contained
#print axioms SmcTuring.Native.ProgramLoaded.represented_agrees
#print axioms SmcTuring.Native.ProgramLoaded.kernel_prefix
#print axioms SmcTuring.Native.ProgramLoaded.closed_prefix

#print axioms SmcTuring.Native.WindowBounds.contained_slice
#print axioms SmcTuring.Native.WindowBounds.core_length_bound
#print axioms SmcTuring.Native.WindowBounds.classified_length_bound
#print axioms SmcTuring.Native.WindowBounds.fetch_within
#print axioms SmcTuring.Native.WindowBounds.safe
#print axioms SmcTuring.Native.WindowBounds.safe_run_append

#print axioms SmcTuring.Native.ReaderBounds.label_contained
#print axioms SmcTuring.Native.ReaderBounds.safe_run
#print axioms SmcTuring.Native.ReaderBounds.loaded

#print axioms SmcTuring.Native.CallsBounds.safe_run
#print axioms SmcTuring.Native.CallsBounds.loaded

#print axioms SmcTuring.Native.ReadCalleeBounds.safe_run
#print axioms SmcTuring.Native.ReadCalleeBounds.loaded

#print axioms SmcTuring.Native.ReadInvocationBounds.safe_run
#print axioms SmcTuring.Native.ReadInvocationBounds.loaded

#print axioms SmcTuring.Native.ScalarBounds.safe_run
#print axioms SmcTuring.Native.ScalarBounds.loaded

#print axioms SmcTuring.Native.ReadScalarBounds.safe_run
#print axioms SmcTuring.Native.ReadScalarBounds.loaded

#print axioms SmcTuring.Native.Allocation.origin_before_grid
#print axioms SmcTuring.Native.Allocation.capacity
#print axioms SmcTuring.Native.Allocation.control_limit
#print axioms SmcTuring.Native.Allocation.entry_window
#print axioms SmcTuring.Native.Allocation.snippet_bounds
#print axioms SmcTuring.Native.Allocation.snippet_window
#print axioms SmcTuring.Native.Allocation.operand_contained
#print axioms SmcTuring.Native.Allocation.register_contained
#print axioms SmcTuring.Native.Allocation.heap_contained
#print axioms SmcTuring.Native.Allocation.reader_value_contained
#print axioms SmcTuring.Native.Allocation.reader_window
#print axioms SmcTuring.Native.Allocation.reader_invocation_safe
#print axioms SmcTuring.Native.Allocation.reader_invocation_loaded
#print axioms SmcTuring.Native.Allocation.destination_contained
#print axioms SmcTuring.Native.Allocation.scalar_safe
#print axioms SmcTuring.Native.Allocation.scalar_loaded
#print axioms SmcTuring.Native.Allocation.read_scalar_safe
#print axioms SmcTuring.Native.Allocation.read_scalar_loaded

#print axioms SmcTuring.Native.PlacedBounds.snippet_bounds
#print axioms SmcTuring.Native.PlacedBounds.snippet_window
#print axioms SmcTuring.Native.PlacedBounds.entry_window
#print axioms SmcTuring.Native.PlacedBounds.scalar_safe
#print axioms SmcTuring.Native.PlacedBounds.calls_safe
#print axioms SmcTuring.Native.PlacedBounds.reader_invocation_safe
#print axioms SmcTuring.Native.PlacedBounds.read_scalar_safe
#print axioms SmcTuring.Native.PlacedBounds.safe_trace_append

#print axioms SmcTuring.Native.BorrowMaskBounds.safe_run
#print axioms SmcTuring.Native.BorrowMaskBounds.loaded

#print axioms SmcTuring.Native.GuardSetupBounds.safe_run
#print axioms SmcTuring.Native.GuardSetupBounds.loaded

#print axioms SmcTuring.Native.GuardSelectionBounds.safe_run
#print axioms SmcTuring.Native.GuardSelectionBounds.loaded

#print axioms SmcTuring.Native.GuardBounds.safe_run
#print axioms SmcTuring.Native.GuardBounds.loaded

#print axioms SmcTuring.Native.GuardInvocationBounds.safe_run
#print axioms SmcTuring.Native.GuardInvocationBounds.loaded

#print axioms SmcTuring.Native.GuardAllocation.safe_run
#print axioms SmcTuring.Native.GuardAllocation.loaded
#print axioms SmcTuring.Native.GuardAllocation.invocation_safe
#print axioms SmcTuring.Native.GuardAllocation.invocation_loaded

#print axioms SmcTuring.Native.Allocation.control_contained

#print axioms SmcTuring.Native.SourceAccess.guard_safe
#print axioms SmcTuring.Native.SourceAccess.invocation_safe

#print axioms SmcTuring.Native.OffsetGuardBounds.safe_run
#print axioms SmcTuring.Native.OffsetGuardBounds.loaded

#print axioms SmcTuring.Native.PointerBounds.safe_run
#print axioms SmcTuring.Native.PointerBounds.loaded

#print axioms SmcTuring.Native.AddressBounds.safe_run
#print axioms SmcTuring.Native.AddressBounds.loaded

#print axioms SmcTuring.Native.StoreCalleeBounds.safe_run
#print axioms SmcTuring.Native.StoreCalleeBounds.loaded

#print axioms SmcTuring.Native.StoreInvocationBounds.safe_run
#print axioms SmcTuring.Native.StoreInvocationBounds.loaded

#print axioms SmcTuring.Native.ImmediateBounds.safe_run
#print axioms SmcTuring.Native.ImmediateBounds.loaded

#print axioms SmcTuring.Native.LoadBounds.safe_run
#print axioms SmcTuring.Native.LoadBounds.loaded

#print axioms SmcTuring.Native.StoreBounds.safe_run
#print axioms SmcTuring.Native.StoreBounds.loaded

#print axioms SmcTuring.Native.BlockBounds.safe_run
#print axioms SmcTuring.Native.BlockBounds.loaded

#print axioms SmcTuring.Native.SourceAllocation.data_within
#print axioms SmcTuring.Native.SourceAllocation.guard_fields
#print axioms SmcTuring.Native.SourceAllocation.block_static
#print axioms SmcTuring.Native.SourceAllocation.block_safe
#print axioms SmcTuring.Native.SourceAllocation.block_loaded

#print axioms SmcTuring.Native.ProgramBounds.safe_run
#print axioms SmcTuring.Native.ProgramBounds.loaded

#print axioms SmcTuring.Native.ProgramAllocation.kernel_safe
#print axioms SmcTuring.Native.ProgramAllocation.closed_safe
#print axioms SmcTuring.Native.ProgramAllocation.kernel_loaded
#print axioms SmcTuring.Native.ProgramAllocation.closed_loaded
#print axioms SmcTuring.Native.AddressSpace.region_valid
#print axioms SmcTuring.Native.AddressSpace.contains_valid
#print axioms SmcTuring.Native.AddressSpace.x86_fits
#print axioms SmcTuring.Native.AddressSpace.x64_low_fits
#print axioms SmcTuring.Native.AddressSpace.x64_high_fits
#print axioms SmcTuring.Native.AddressSpace.x64_gap_invalid
#print axioms SmcTuring.Native.MappedExecution.window_of_contains
#print axioms SmcTuring.Native.MappedExecution.accesses_of_safe
#print axioms SmcTuring.Native.MappedExecution.step_complete
#print axioms SmcTuring.Native.MappedExecution.step_sound
#print axioms SmcTuring.Native.MappedExecution.step_execute_denied
#print axioms SmcTuring.Native.MappedExecution.step_invalid_pc
#print axioms SmcTuring.Native.MappedExecution.trace_complete
#print axioms SmcTuring.Native.MappedExecution.access_run_of_safe
#print axioms SmcTuring.Native.MappedExecution.trace_loaded
#print axioms SmcTuring.Native.MappedExecution.trace_sound
#print axioms SmcTuring.Native.ProgramMapped.mapped
#print axioms SmcTuring.Native.ProgramMapped.x86_mapped
#print axioms SmcTuring.Native.ProgramMapped.x64_low_mapped
#print axioms SmcTuring.Native.ProgramMapped.x64_high_mapped
#print axioms SmcTuring.Native.ProgramMapped.kernel_checked
#print axioms SmcTuring.Native.ProgramMapped.closed_checked
#print axioms SmcTuring.Native.ControlBounds.pc_valid_of_safe
#print axioms SmcTuring.Native.ControlBounds.targets_of_safe
#print axioms SmcTuring.Native.ControlBounds.targets_of_trace
#print axioms SmcTuring.Native.ProgramControl.closed_targets
#print axioms SmcTuring.Native.ProgramControl.closed_checked
#print axioms SmcTuring.Native.ProgramEndpoint.failure_target
#print axioms SmcTuring.Native.ProgramEndpoint.endpoint
#print axioms SmcTuring.Native.SourceEndpoint.host_contained
#print axioms SmcTuring.Native.SourceEndpoint.backedge_contained
#print axioms SmcTuring.Native.SourceEndpoint.contained_word_valid
#print axioms SmcTuring.Native.SourceEndpoint.terminal_word
#print axioms SmcTuring.Native.SourceEndpoint.block_snapshot
#print axioms SmcTuring.Native.SourceEndpoint.kernel_pc
#print axioms SmcTuring.Native.SourceEndpoint.kernel_targets
#print axioms SmcTuring.Native.SourceEndpoint.kernel_checked
#print axioms SmcTuring.Native.CheckedExecution.target_valid_agrees
#print axioms SmcTuring.Native.CheckedExecution.step_complete
#print axioms SmcTuring.Native.CheckedExecution.step_sound
#print axioms SmcTuring.Native.CheckedExecution.step_target_denied
#print axioms SmcTuring.Native.CheckedExecution.trace_complete
#print axioms SmcTuring.Native.CheckedExecution.trace_loaded
#print axioms SmcTuring.Native.CheckedExecution.trace_targets
#print axioms SmcTuring.Native.CheckedExecution.trace_sound
#print axioms SmcTuring.Native.SourceChecked.kernel
#print axioms SmcTuring.Native.SourceChecked.closed
#print axioms SmcTuring.Native.LoopBounds.pass_safe
#print axioms SmcTuring.Native.ProgramIteration.correct
#print axioms SmcTuring.Native.ProgramIteration.accepted_length
#print axioms SmcTuring.Native.ProgramIteration.targets
#print axioms SmcTuring.Native.SourceIteration.entry_contained
#print axioms SmcTuring.Native.SourceIteration.static
#print axioms SmcTuring.Native.SourceIteration.correct
#print axioms SmcTuring.Native.SourceIteration.checked
#print axioms SmcTuring.X64.HalfWords.low_pack
#print axioms SmcTuring.X64.HalfWords.high_pack
#print axioms SmcTuring.X64.HalfWords.pack_halves
#print axioms SmcTuring.X64.HalfWords.split_xor
#print axioms SmcTuring.X64.HalfWords.split_and
#print axioms SmcTuring.X64.HalfWords.split_or
#print axioms SmcTuring.X64.HalfWords.split_not
#print axioms SmcTuring.X64.HalfWords.split_mov
#print axioms SmcTuring.X64.HalfWords.broadcast_as_repeated
#print axioms SmcTuring.X64.HalfWords.broadcast_xor
#print axioms SmcTuring.X64.HalfWords.broadcast_and
#print axioms SmcTuring.X64.HalfWords.broadcast_or
#print axioms SmcTuring.X64.HalfWords.broadcast_mov
#print axioms SmcTuring.X64.HalfWords.pack_toNat
#print axioms SmcTuring.X64.HalfWords.add_carry
#print axioms SmcTuring.X64.HalfWords.sub_borrow
#print axioms SmcTuring.X64.HalfWords.split_add_no_carry
#print axioms SmcTuring.X64.HalfWords.split_sub_no_borrow
#print axioms SmcTuring.X64.HalfWords.split_add_counterexample
#print axioms SmcTuring.X64.HalfWords.split_sub_counterexample
#print axioms SmcTuring.X64.HalfWords.repeated_one_counterexample
#print axioms SmcTuring.X64.HalfWords.repeated_masks
#print axioms SmcTuring.Appendix.Machine32.every_instruction_writes
#print axioms SmcTuring.Appendix.Machine32.execute_memory_frame
#print axioms SmcTuring.Appendix.Machine32.run_append
#print axioms SmcTuring.Appendix.Machine32.run_memory_frame
#print axioms SmcTuring.Appendix.Machine32.pure_of_destinations
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_involution
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_injective
#print axioms SmcTuring.Appendix.BranchAlgebra.one_bit_cases
#print axioms SmcTuring.Appendix.BranchAlgebra.append_toNat
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_append
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_append_toNat
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_toNat
#print axioms SmcTuring.Appendix.BranchAlgebra.flip_order
#print axioms SmcTuring.Appendix.BranchAlgebra.normalized_eq
#print axioms SmcTuring.Appendix.BranchAlgebra.difference_ne_zero
#print axioms SmcTuring.Appendix.BranchAlgebra.raw_gt
#print axioms SmcTuring.Appendix.BranchAlgebra.raw_ne
#print axioms SmcTuring.Appendix.BranchAlgebra.all_relations
#print axioms SmcTuring.Appendix.BranchAlgebra.sbb_mask
#print axioms SmcTuring.Appendix.BranchAlgebra.complement_mask
#print axioms SmcTuring.Appendix.BranchAlgebra.and_mask
#print axioms SmcTuring.Appendix.Branching.comparison_accumulator
#print axioms SmcTuring.Appendix.Branching.comparison_memory
#print axioms SmcTuring.Appendix.Branching.accumulator
#print axioms SmcTuring.Appendix.Branching.memory
#print axioms SmcTuring.Appendix.Branching.carry
#print axioms SmcTuring.Appendix.Branching.displacement
#print axioms SmcTuring.Appendix.Branching.program_length
#print axioms SmcTuring.Appendix.Branching.owned_destinations
#print axioms SmcTuring.Appendix.Branching.pure
#print axioms SmcTuring.Appendix.Branching.alias_counterexample
#print axioms SmcTuring.Appendix.Branching.swap_separate
#print axioms SmcTuring.Appendix.Branching.relation_memory
#print axioms SmcTuring.Appendix.Branching.relation_displacement
#print axioms SmcTuring.Appendix.Branching.relation_target
#print axioms SmcTuring.Appendix.Branching.relation_accumulator
#print axioms SmcTuring.Appendix.Branching.relation_carry
#print axioms SmcTuring.Appendix.Branching.relation_frame
#print axioms SmcTuring.Appendix.Branching.relation_pure
#print axioms SmcTuring.Appendix.BranchTail.tail_effect
#print axioms SmcTuring.Appendix.BranchTail.tail_pc
#print axioms SmcTuring.Appendix.BranchTail.tail_stack
#print axioms SmcTuring.Appendix.BranchTail.tail_accumulator
#print axioms SmcTuring.Appendix.BranchTail.tail_carry
#print axioms SmcTuring.Appendix.BranchTail.tail_return
#print axioms SmcTuring.Appendix.BranchTail.tail_frame
#print axioms SmcTuring.Appendix.BranchTail.tail_pure
#print axioms SmcTuring.Appendix.BranchTail.restore_effect
#print axioms SmcTuring.Appendix.BranchTail.restore_accumulator
#print axioms SmcTuring.Appendix.BranchTail.restore_frame
#print axioms SmcTuring.Appendix.BranchTail.restoration_count
#print axioms SmcTuring.Appendix.BranchTail.restoration_pure
#print axioms SmcTuring.Appendix.BranchTail.continued_effect
#print axioms SmcTuring.Appendix.BranchTail.continued_return
#print axioms SmcTuring.Appendix.BranchTail.continued_frame
#print axioms SmcTuring.Appendix.BranchTail.continued_alias
#print axioms SmcTuring.Appendix.BranchTail.slot_add_no_carry
#print axioms SmcTuring.Appendix.BranchTail.continued_alias_no_carry
#print axioms SmcTuring.Appendix.BranchTail.prefixed_frame
#print axioms SmcTuring.Appendix.BranchTail.branch_pc
#print axioms SmcTuring.Appendix.BranchTail.branch_restored
#print axioms SmcTuring.Appendix.BranchTail.branch_pure
#print axioms SmcTuring.Appendix.ByteCode.immediate_tag
#print axioms SmcTuring.Appendix.ByteCode.memory_tag
#print axioms SmcTuring.Appendix.ByteCode.memory_not_immediate
#print axioms SmcTuring.Appendix.ByteCode.immediate_payload
#print axioms SmcTuring.Appendix.ByteCode.memory_payload
#print axioms SmcTuring.Appendix.ByteCode.form_roundtrip
#print axioms SmcTuring.Appendix.ByteCode.encode_injective
#print axioms SmcTuring.Appendix.ByteCode.encode_length
#print axioms SmcTuring.Appendix.ByteCode.length_bounds
#print axioms SmcTuring.Appendix.ByteCode.encoded_length
#print axioms SmcTuring.Appendix.ByteCode.length_take_two
#print axioms SmcTuring.Appendix.ByteCode.fetch_current_encoding
#print axioms SmcTuring.Appendix.ByteCode.fetch_written_encoding
#print axioms SmcTuring.Appendix.ByteCode.immediate_patch
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_immediate
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_current_immediate
#print axioms SmcTuring.Appendix.ByteCode.call_patch
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_call
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_current_call
#print axioms SmcTuring.Appendix.ByteCode.put_bytes_append
#print axioms SmcTuring.Appendix.ByteCode.patch_middle
#print axioms SmcTuring.Appendix.ByteCode.address_patch
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_address
#print axioms SmcTuring.Appendix.ByteCode.fetch_patched_current_address
#print axioms SmcTuring.Appendix.ByteExecution.execute_effect
#print axioms SmcTuring.Appendix.ByteExecution.execute_memory
#print axioms SmcTuring.Appendix.ByteExecution.execute_accumulator
#print axioms SmcTuring.Appendix.ByteExecution.execute_stack
#print axioms SmcTuring.Appendix.ByteExecution.execute_carry
#print axioms SmcTuring.Appendix.ByteExecution.execute_pc
#print axioms SmcTuring.Appendix.ByteExecution.written_word
#print axioms SmcTuring.Appendix.ByteExecution.execute_frame
#print axioms SmcTuring.Appendix.ByteExecution.load_frame
#print axioms SmcTuring.Appendix.ByteExecution.footprint_length
#print axioms SmcTuring.Appendix.ByteExecution.footprint_nonempty
#print axioms SmcTuring.Appendix.ByteExecution.store_preserves_carry
#print axioms SmcTuring.Appendix.ByteExecution.xor_clears_carry
#print axioms SmcTuring.Appendix.ByteExecution.and_clears_carry
#print axioms SmcTuring.Appendix.ByteExecution.neg_carry
#print axioms SmcTuring.Appendix.ByteExecution.not_preserves_carry
#print axioms SmcTuring.Appendix.ByteExecution.sbb_value
#print axioms SmcTuring.Appendix.ByteExecution.add_four_carry
#print axioms SmcTuring.Appendix.ByteExecution.call_target
#print axioms SmcTuring.Appendix.ByteExecution.call_return
#print axioms SmcTuring.Appendix.ByteExecution.common_encoding
#print axioms SmcTuring.Appendix.ByteExecution.common_execution
#print axioms SmcTuring.Appendix.ByteExecution.step_current_encoding
#print axioms SmcTuring.Appendix.ByteExecution.fetched_write
#print axioms SmcTuring.Appendix.ByteExecution.step_patched_immediate
#print axioms SmcTuring.Appendix.ByteExecution.step_patched_call
#print axioms SmcTuring.Appendix.ByteExecution.step_patched_address
#print axioms SmcTuring.Appendix.ByteExecution.trace_run
#print axioms SmcTuring.Appendix.ByteExecution.run_append
#print axioms SmcTuring.Appendix.ByteExecution.trace_append
#print axioms SmcTuring.Appendix.ByteExecution.trace_head_step
#print axioms SmcTuring.Appendix.ByteExecution.owned_append
#print axioms SmcTuring.Appendix.FieldRefinement.destination_dependency
#print axioms SmcTuring.Appendix.FieldRefinement.address_toNat
#print axioms SmcTuring.Appendix.FieldRefinement.equal_word_bytes
#print axioms SmcTuring.Appendix.FieldRefinement.equal_word_byte
#print axioms SmcTuring.Appendix.FieldRefinement.layout_outside
#print axioms SmcTuring.Appendix.FieldRefinement.translate_destination
#print axioms SmcTuring.Appendix.FieldRefinement.translate_value
#print axioms SmcTuring.Appendix.FieldRefinement.translate_accumulator
#print axioms SmcTuring.Appendix.FieldRefinement.translate_carry
#print axioms SmcTuring.Appendix.FieldRefinement.translate_stack
#print axioms SmcTuring.Appendix.FieldRefinement.execute_read_destination
#print axioms SmcTuring.Appendix.FieldRefinement.execute_read_frame
#print axioms SmcTuring.Appendix.FieldRefinement.simulate
#print axioms SmcTuring.Appendix.FieldRefinement.forms_length
#print axioms SmcTuring.Appendix.FieldRefinement.forms_run
#print axioms SmcTuring.Appendix.FieldRefinement.simulate_run
#print axioms SmcTuring.Appendix.FieldRefinement.run_stack
#print axioms SmcTuring.Appendix.FieldRefinement.run_frame
#print axioms SmcTuring.Appendix.FieldRefinement.owned_run
#print axioms SmcTuring.Appendix.FieldRefinement.trace_refines
#print axioms SmcTuring.Appendix.BranchExecution.initial_agreement
#print axioms SmcTuring.Appendix.BranchExecution.program_dependencies
#print axioms SmcTuring.Appendix.BranchExecution.relation_dependencies
#print axioms SmcTuring.Appendix.BranchExecution.refinement
#print axioms SmcTuring.Appendix.BranchExecution.word_result
#print axioms SmcTuring.Appendix.BranchExecution.displacement
#print axioms SmcTuring.Appendix.BranchExecution.accumulator
#print axioms SmcTuring.Appendix.BranchExecution.stack
#print axioms SmcTuring.Appendix.BranchExecution.carry
#print axioms SmcTuring.Appendix.BranchExecution.operand_x
#print axioms SmcTuring.Appendix.BranchExecution.operand_y
#print axioms SmcTuring.Appendix.BranchExecution.byte_frame
#print axioms SmcTuring.Appendix.BranchExecution.restored_byte_frame
#print axioms SmcTuring.Appendix.BranchExecution.owned
#print axioms SmcTuring.Appendix.BranchExecution.modular_target
#print axioms SmcTuring.Appendix.BranchExecution.trace_displacement
#print axioms SmcTuring.Appendix.ByteImage.word_at_total
#print axioms SmcTuring.Appendix.ByteImage.word_at_window
#print axioms SmcTuring.Appendix.ByteImage.word_at_read_field
#print axioms SmcTuring.Appendix.ByteImage.bytes_at_drop
#print axioms SmcTuring.Appendix.ByteImage.payload_window
#print axioms SmcTuring.Appendix.ByteImage.initial_length
#print axioms SmcTuring.Appendix.ByteImage.current_length
#print axioms SmcTuring.Appendix.ByteImage.immediate_words
#print axioms SmcTuring.Appendix.ByteImage.relative_word
#print axioms SmcTuring.Appendix.ByteImage.intact_current
#print axioms SmcTuring.Appendix.ByteImage.fetch_current
#print axioms SmcTuring.Appendix.ByteImage.initialized_packet
#print axioms SmcTuring.Appendix.ByteImage.patch_owner
#print axioms SmcTuring.Appendix.ByteImage.owned_field_inside
#print axioms SmcTuring.Appendix.ByteImage.separated_tail
#print axioms SmcTuring.Appendix.ByteImage.apart_bytes
#print axioms SmcTuring.Appendix.ByteImage.image_packet
#print axioms SmcTuring.Appendix.ByteImage.initialized_intact
#print axioms SmcTuring.Appendix.ByteImage.frame_packet
#print axioms SmcTuring.Appendix.ByteImage.store_intact
#print axioms SmcTuring.Appendix.ByteImage.execute_intact
#print axioms SmcTuring.Appendix.BytePacking.size_cons
#print axioms SmcTuring.Appendix.BytePacking.size_append
#print axioms SmcTuring.Appendix.BytePacking.place_append
#print axioms SmcTuring.Appendix.BytePacking.placed_lower
#print axioms SmcTuring.Appendix.BytePacking.placed_upper
#print axioms SmcTuring.Appendix.BytePacking.placed_separated
#print axioms SmcTuring.Appendix.BytePacking.initial_intact
#print axioms SmcTuring.Appendix.BytePacking.initial_fetch
#print axioms SmcTuring.Appendix.BytePacking.fields_owned
#print axioms SmcTuring.Appendix.BytePacking.same_owner_separate
#print axioms SmcTuring.Appendix.BytePacking.owned_separate
#print axioms SmcTuring.Appendix.BytePacking.field_layout
#print axioms SmcTuring.Appendix.BytePacking.placed_field_layout
#print axioms SmcTuring.Appendix.BytePacking.image_frame
#print axioms SmcTuring.Appendix.ByteProgram.span_cons
#print axioms SmcTuring.Appendix.ByteProgram.instruction_length
#print axioms SmcTuring.Appendix.ByteProgram.current_translation
#print axioms SmcTuring.Appendix.ByteProgram.execute_pc
#print axioms SmcTuring.Appendix.ByteProgram.constructed_trace
#print axioms SmcTuring.Appendix.ByteProgram.image_trace
#print axioms SmcTuring.Appendix.ByteProgram.run_pc
#print axioms SmcTuring.Appendix.BranchLayout.span
#print axioms SmcTuring.Appendix.BranchLayout.tail_size
#print axioms SmcTuring.Appendix.BranchLayout.continuation_size
#print axioms SmcTuring.Appendix.BranchLayout.image_end
#print axioms SmcTuring.Appendix.BranchLayout.linked
#print axioms SmcTuring.Appendix.BranchLayout.image_fields
#print axioms SmcTuring.Appendix.BranchLayout.separate_fields
#print axioms SmcTuring.Appendix.BranchLayout.fields_owned
#print axioms SmcTuring.Appendix.BranchLayout.field_layout
#print axioms SmcTuring.Appendix.BranchPrefix.prefix_placed
#print axioms SmcTuring.Appendix.BranchPrefix.storage_placed
#print axioms SmcTuring.Appendix.BranchPrefix.initial_operands
#print axioms SmcTuring.Appendix.BranchPrefix.prefix_capacity
#print axioms SmcTuring.Appendix.BranchPrefix.trace
#print axioms SmcTuring.Appendix.BranchPrefix.finish_pc
#print axioms SmcTuring.Appendix.BranchPrefix.displacement
#print axioms SmcTuring.Appendix.BranchPrefix.initialized_displacement
#print axioms SmcTuring.Appendix.BranchPrefix.accumulator
#print axioms SmcTuring.Appendix.BranchPrefix.stack
#print axioms SmcTuring.Appendix.BranchPrefix.carry
#print axioms SmcTuring.Appendix.BranchPrefix.byte_frame
#print axioms SmcTuring.Appendix.BranchPrefix.finish_intact

#print axioms SmcTuring.Appendix.ByteControl.apart_symmetric
#print axioms SmcTuring.Appendix.ByteControl.load_put
#print axioms SmcTuring.Appendix.ByteControl.load_frame
#print axioms SmcTuring.Appendix.ByteControl.put_overwrite
#print axioms SmcTuring.Appendix.ByteControl.put_commute
#print axioms SmcTuring.Appendix.ByteControl.put_back
#print axioms SmcTuring.Appendix.ByteControl.exchange_stack_effect
#print axioms SmcTuring.Appendix.ByteControl.exchange_acc_effect
#print axioms SmcTuring.Appendix.ByteControl.add_four_effect
#print axioms SmcTuring.Appendix.ByteControl.store_acc_effect
#print axioms SmcTuring.Appendix.ByteControl.restore_run
#print axioms SmcTuring.Appendix.ByteControl.restore_effect
#print axioms SmcTuring.Appendix.ByteControl.call_effect
#print axioms SmcTuring.Appendix.ByteControl.tail_run
#print axioms SmcTuring.Appendix.ByteControl.tail_effect
#print axioms SmcTuring.Appendix.ByteControl.continued_alias
#print axioms SmcTuring.Appendix.ByteLinear.span_cons
#print axioms SmcTuring.Appendix.ByteLinear.minimum_length
#print axioms SmcTuring.Appendix.ByteLinear.execute_pc
#print axioms SmcTuring.Appendix.ByteLinear.constructed_trace
#print axioms SmcTuring.Appendix.ByteLinear.image_trace
#print axioms SmcTuring.Appendix.ByteLinear.run_pc
#print axioms SmcTuring.Appendix.ByteLinear.owned_run
#print axioms SmcTuring.Appendix.ByteLinear.run_intact
#print axioms SmcTuring.Appendix.BranchControl.full_layout
#print axioms SmcTuring.Appendix.BranchControl.field_owned
#print axioms SmcTuring.Appendix.BranchControl.slot_apart
#print axioms SmcTuring.Appendix.BranchControl.call_apart
#print axioms SmcTuring.Appendix.BranchControl.slot_alias
#print axioms SmcTuring.Appendix.BranchControl.pointer_nonwrap
#print axioms SmcTuring.Appendix.BranchControl.stack_placed
#print axioms SmcTuring.Appendix.BranchControl.initial_stack
#print axioms SmcTuring.Appendix.BranchControl.prefix_load_frame
#print axioms SmcTuring.Appendix.BranchControl.prefix_stack
#print axioms SmcTuring.Appendix.BranchPaths.tail_placed
#print axioms SmcTuring.Appendix.BranchPaths.fall_placed
#print axioms SmcTuring.Appendix.BranchPaths.taken_placed
#print axioms SmcTuring.Appendix.BranchPaths.fetched_current
#print axioms SmcTuring.Appendix.BranchPaths.tail_trace_intact
#print axioms SmcTuring.Appendix.BranchWhole.run_forms
#print axioms SmcTuring.Appendix.BranchWhole.tail_pc
#print axioms SmcTuring.Appendix.BranchWhole.restored
#print axioms SmcTuring.Appendix.BranchWhole.finish_pc
#print axioms SmcTuring.Appendix.BranchWhole.accumulator
#print axioms SmcTuring.Appendix.BranchWhole.stack
#print axioms SmcTuring.Appendix.BranchWhole.carry
#print axioms SmcTuring.Appendix.BranchWhole.byte_frame
#print axioms SmcTuring.Appendix.BranchWhole.continuation_ownership
#print axioms SmcTuring.Appendix.BranchWhole.continuation_straight
#print axioms SmcTuring.Appendix.BranchWhole.continuation_span
#print axioms SmcTuring.Appendix.BranchWhole.continuation_trace
#print axioms SmcTuring.Appendix.BranchWhole.trace
#print axioms SmcTuring.Appendix.BranchWhole.tail_owned_run
#print axioms SmcTuring.Appendix.BranchWhole.owned_run
#print axioms SmcTuring.Appendix.BranchWhole.finish_intact
#print axioms SmcTuring.Appendix.BranchWhole.correct

#print axioms SmcTuring.Appendix.ByteRegions.member
#print axioms SmcTuring.Appendix.ByteRegions.entry_bounds
#print axioms SmcTuring.Appendix.ByteRegions.separated_append
#print axioms SmcTuring.Appendix.ByteRegions.separated
#print axioms SmcTuring.Appendix.ByteRegions.capacity
#print axioms SmcTuring.Appendix.ByteRegions.field_layout
#print axioms SmcTuring.Appendix.ByteRegions.initial_intact
#print axioms SmcTuring.Appendix.ByteRegions.image_append
#print axioms SmcTuring.Appendix.ByteRegions.image_frame
#print axioms SmcTuring.Appendix.ByteRegions.outside_owned
#print axioms SmcTuring.Appendix.SpacedLayout.span
#print axioms SmcTuring.Appendix.SpacedLayout.stack_size
#print axioms SmcTuring.Appendix.SpacedLayout.storage_size
#print axioms SmcTuring.Appendix.SpacedLayout.core_end
#print axioms SmcTuring.Appendix.SpacedLayout.ordered
#print axioms SmcTuring.Appendix.SpacedLayout.region_capacity
#print axioms SmcTuring.Appendix.SpacedLayout.separated
#print axioms SmcTuring.Appendix.SpacedLayout.image_fields
#print axioms SmcTuring.Appendix.SpacedLayout.full_layout
#print axioms SmcTuring.Appendix.SpacedLayout.field_owned
#print axioms SmcTuring.Appendix.SpacedLayout.fields_owned
#print axioms SmcTuring.Appendix.SpacedLayout.field_layout
#print axioms SmcTuring.Appendix.SpacedLayout.linked
#print axioms SmcTuring.Appendix.SpacedLayout.separate_fields
#print axioms SmcTuring.Appendix.SpacedLayout.initial_intact
#print axioms SmcTuring.Appendix.SpacedLayout.core_placed
#print axioms SmcTuring.Appendix.SpacedLayout.stack_placed
#print axioms SmcTuring.Appendix.SpacedLayout.prefix_placed
#print axioms SmcTuring.Appendix.SpacedLayout.tail_placed
#print axioms SmcTuring.Appendix.SpacedLayout.fall_placed
#print axioms SmcTuring.Appendix.SpacedLayout.taken_placed
#print axioms SmcTuring.Appendix.SpacedLayout.storage_placed
#print axioms SmcTuring.Appendix.SpacedLayout.gap_frame
#print axioms SmcTuring.Appendix.SpacedLayout.gap_outside
#print axioms SmcTuring.Appendix.SpacedLayout.initial_gap_frame
#print axioms SmcTuring.Appendix.SpacedPrefix.initial_operands
#print axioms SmcTuring.Appendix.SpacedPrefix.prefix_valid
#print axioms SmcTuring.Appendix.SpacedPrefix.trace
#print axioms SmcTuring.Appendix.SpacedPrefix.finish_pc
#print axioms SmcTuring.Appendix.SpacedPrefix.displacement
#print axioms SmcTuring.Appendix.SpacedPrefix.initialized_displacement
#print axioms SmcTuring.Appendix.SpacedPrefix.accumulator
#print axioms SmcTuring.Appendix.SpacedPrefix.stack
#print axioms SmcTuring.Appendix.SpacedPrefix.carry
#print axioms SmcTuring.Appendix.SpacedPrefix.byte_frame
#print axioms SmcTuring.Appendix.SpacedPrefix.finish_intact
#print axioms SmcTuring.Appendix.SpacedControl.slot_apart
#print axioms SmcTuring.Appendix.SpacedControl.call_apart
#print axioms SmcTuring.Appendix.SpacedControl.slot_alias
#print axioms SmcTuring.Appendix.SpacedControl.pointer_nonwrap
#print axioms SmcTuring.Appendix.SpacedControl.initial_stack
#print axioms SmcTuring.Appendix.SpacedControl.prefix_load_frame
#print axioms SmcTuring.Appendix.SpacedControl.prefix_stack
#print axioms SmcTuring.Appendix.SpacedPaths.tail_trace_intact
#print axioms SmcTuring.Appendix.SpacedWhole.run_forms
#print axioms SmcTuring.Appendix.SpacedWhole.tail_pc
#print axioms SmcTuring.Appendix.SpacedWhole.restored
#print axioms SmcTuring.Appendix.SpacedWhole.finish_pc
#print axioms SmcTuring.Appendix.SpacedWhole.accumulator
#print axioms SmcTuring.Appendix.SpacedWhole.stack
#print axioms SmcTuring.Appendix.SpacedWhole.carry
#print axioms SmcTuring.Appendix.SpacedWhole.byte_frame
#print axioms SmcTuring.Appendix.SpacedWhole.continuation_ownership
#print axioms SmcTuring.Appendix.SpacedWhole.continuation_straight
#print axioms SmcTuring.Appendix.SpacedWhole.continuation_span
#print axioms SmcTuring.Appendix.SpacedWhole.continuation_trace
#print axioms SmcTuring.Appendix.SpacedWhole.trace
#print axioms SmcTuring.Appendix.SpacedWhole.tail_owned_run
#print axioms SmcTuring.Appendix.SpacedWhole.owned_run
#print axioms SmcTuring.Appendix.SpacedWhole.finish_intact
#print axioms SmcTuring.Appendix.SpacedWhole.correct
#print axioms SmcTuring.Appendix.SpacedWhole.gap_frame

#print axioms SmcTuring.X64.HalfFrame.every_instruction_writes
#print axioms SmcTuring.X64.HalfFrame.run_append
#print axioms SmcTuring.X64.HalfFrame.pure_append
#print axioms SmcTuring.X64.HalfFrame.restored_exchange
#print axioms SmcTuring.X64.HalfFrame.carry_idempotent
#print axioms SmcTuring.X64.HalfFrame.use_effect
#print axioms SmcTuring.X64.HalfFrame.use_accumulator
#print axioms SmcTuring.X64.HalfFrame.use_source
#print axioms SmcTuring.X64.HalfFrame.use_target
#print axioms SmcTuring.X64.HalfFrame.use_carry
#print axioms SmcTuring.X64.HalfFrame.use_frame
#print axioms SmcTuring.X64.HalfFrame.use_length
#print axioms SmcTuring.X64.HalfFrame.use_pure
#print axioms SmcTuring.X64.HalfFrame.split_effect
#print axioms SmcTuring.X64.HalfFrame.split_accumulator
#print axioms SmcTuring.X64.HalfFrame.split_sources
#print axioms SmcTuring.X64.HalfFrame.split_carry
#print axioms SmcTuring.X64.HalfFrame.split_frame
#print axioms SmcTuring.X64.HalfFrame.split_length
#print axioms SmcTuring.X64.HalfFrame.split_pure
#print axioms SmcTuring.X64.HalfFrame.split_value
#print axioms SmcTuring.X64.HalfFrame.split_correct
#print axioms SmcTuring.X64.HalfFrame.complement_effect
#print axioms SmcTuring.X64.HalfFrame.complement_correct
#print axioms SmcTuring.X64.HalfFrame.complement_frame
#print axioms SmcTuring.X64.HalfFrame.complement_registers
#print axioms SmcTuring.X64.HalfFrame.complement_pure
#print axioms SmcTuring.X64.HalfFrame.complement_length

#print axioms SmcTuring.Appendix.MultiplyAlgebra.low_bit_toNat
#print axioms SmcTuring.Appendix.MultiplyAlgebra.low_bit_cases
#print axioms SmcTuring.Appendix.MultiplyAlgebra.shifted_toNat
#print axioms SmcTuring.Appendix.MultiplyAlgebra.doubled
#print axioms SmcTuring.Appendix.MultiplyAlgebra.decomposition
#print axioms SmcTuring.Appendix.MultiplyAlgebra.chosen_product
#print axioms SmcTuring.Appendix.MultiplyAlgebra.step_invariant
#print axioms SmcTuring.Appendix.MultiplyAlgebra.shifted_bound
#print axioms SmcTuring.Appendix.MultiplyAlgebra.iterate_correct
#print axioms SmcTuring.Appendix.MultiplyAlgebra.full_word_product

#print axioms SmcTuring.Appendix.MultiplyWords.full_and
#print axioms SmcTuring.Appendix.MultiplyWords.and_full
#print axioms SmcTuring.Appendix.MultiplyWords.field_eq
#print axioms SmcTuring.Appendix.MultiplyWords.every_instruction_writes
#print axioms SmcTuring.Appendix.MultiplyWords.execute_frame
#print axioms SmcTuring.Appendix.MultiplyWords.run_frame
#print axioms SmcTuring.Appendix.MultiplyWords.run_append
#print axioms SmcTuring.Appendix.MultiplyWords.pure_of_destinations
#print axioms SmcTuring.Appendix.MultiplyWords.copy_effect
#print axioms SmcTuring.Appendix.MultiplyWords.initialize_field
#print axioms SmcTuring.Appendix.MultiplyWords.initialize_accumulator
#print axioms SmcTuring.Appendix.MultiplyWords.initialize_carry
#print axioms SmcTuring.Appendix.MultiplyWords.guard_field
#print axioms SmcTuring.Appendix.MultiplyWords.guard_accumulator
#print axioms SmcTuring.Appendix.MultiplyWords.guard_carry
#print axioms SmcTuring.Appendix.MultiplyWords.guard_displacement
#print axioms SmcTuring.Appendix.MultiplyWords.guard_target
#print axioms SmcTuring.Appendix.MultiplyWords.body_field
#print axioms SmcTuring.Appendix.MultiplyWords.body_accumulator
#print axioms SmcTuring.Appendix.MultiplyWords.body_carry
#print axioms SmcTuring.Appendix.MultiplyWords.body_frame
#print axioms SmcTuring.Appendix.MultiplyWords.finish_field
#print axioms SmcTuring.Appendix.MultiplyWords.finish_registers
#print axioms SmcTuring.Appendix.MultiplyWords.initialize_pure
#print axioms SmcTuring.Appendix.MultiplyWords.guard_pure
#print axioms SmcTuring.Appendix.MultiplyWords.body_pure
#print axioms SmcTuring.Appendix.MultiplyWords.finish_pure
#print axioms SmcTuring.Appendix.MultiplyWords.block_lengths

#print axioms SmcTuring.Appendix.MultiplyLoop.guard_invariant
#print axioms SmcTuring.Appendix.MultiplyLoop.body_invariant
#print axioms SmcTuring.Appendix.MultiplyLoop.exit_post
#print axioms SmcTuring.Appendix.MultiplyLoop.post_step
#print axioms SmcTuring.Appendix.MultiplyLoop.loop_correct
#print axioms SmcTuring.Appendix.MultiplyLoop.loop_run
#print axioms SmcTuring.Appendix.MultiplyLoop.pure_append
#print axioms SmcTuring.Appendix.MultiplyLoop.loop_pure
#print axioms SmcTuring.Appendix.MultiplyLoop.full_product
#print axioms SmcTuring.Appendix.MultiplyLoop.multiply_run
#print axioms SmcTuring.Appendix.MultiplyLoop.multiply_pure
#print axioms SmcTuring.Appendix.MultiplyLoop.pure_destinations
#print axioms SmcTuring.Appendix.MultiplyLoop.multiply_frame
#print axioms SmcTuring.Appendix.MultiplyLoop.loop_length
#print axioms SmcTuring.Appendix.MultiplyLoop.multiply_length

#print axioms SmcTuring.Appendix.MultiplyControl.run_append
#print axioms SmcTuring.Appendix.MultiplyControl.pure_append
#print axioms SmcTuring.Appendix.MultiplyControl.lift_effect
#print axioms SmcTuring.Appendix.MultiplyControl.lift_pure
#print axioms SmcTuring.Appendix.MultiplyControl.literal_lengths
#print axioms SmcTuring.Appendix.MultiplyControl.tail_effect
#print axioms SmcTuring.Appendix.MultiplyControl.restore_effect
#print axioms SmcTuring.Appendix.MultiplyControl.round_trip_effect
#print axioms SmcTuring.Appendix.MultiplyControl.round_trip_ready
#print axioms SmcTuring.Appendix.MultiplyControl.round_trip_pure
#print axioms SmcTuring.Appendix.MultiplyControl.guard_ignore_carry
#print axioms SmcTuring.Appendix.MultiplyControl.loop_ignore_carry
#print axioms SmcTuring.Appendix.MultiplyControl.clear_carry_memory
#print axioms SmcTuring.Appendix.MultiplyControl.lift_length

#print axioms SmcTuring.Appendix.MultiplyBlocks.delta_value
#print axioms SmcTuring.Appendix.MultiplyBlocks.delta_nonzero
#print axioms SmcTuring.Appendix.MultiplyBlocks.continuations_distinct
#print axioms SmcTuring.Appendix.MultiplyBlocks.words_pure
#print axioms SmcTuring.Appendix.MultiplyBlocks.words_frame
#print axioms SmcTuring.Appendix.MultiplyBlocks.ready_lift
#print axioms SmcTuring.Appendix.MultiplyBlocks.call_separate
#print axioms SmcTuring.Appendix.MultiplyBlocks.program_effect
#print axioms SmcTuring.Appendix.MultiplyBlocks.program_ready
#print axioms SmcTuring.Appendix.MultiplyBlocks.program_frame
#print axioms SmcTuring.Appendix.MultiplyBlocks.program_pure
#print axioms SmcTuring.Appendix.MultiplyBlocks.clear_guard
#print axioms SmcTuring.Appendix.MultiplyBlocks.guard_effect
#print axioms SmcTuring.Appendix.MultiplyBlocks.body_effect
#print axioms SmcTuring.Appendix.MultiplyBlocks.entry_effect
#print axioms SmcTuring.Appendix.MultiplyBlocks.finish_effect

#print axioms SmcTuring.Appendix.MultiplyExecution.exit_matches
#print axioms SmcTuring.Appendix.MultiplyExecution.loop_matches
#print axioms SmcTuring.Appendix.MultiplyExecution.loop_run
#print axioms SmcTuring.Appendix.MultiplyExecution.loop_pure
#print axioms SmcTuring.Appendix.MultiplyExecution.correct

#print axioms SmcTuring.Appendix.MultiplyByteCode.common_decode
#print axioms SmcTuring.Appendix.MultiplyByteCode.add_payload
#print axioms SmcTuring.Appendix.MultiplyByteCode.form_roundtrip
#print axioms SmcTuring.Appendix.MultiplyByteCode.encode_injective
#print axioms SmcTuring.Appendix.MultiplyByteCode.encode_length
#print axioms SmcTuring.Appendix.MultiplyByteCode.length_bounds
#print axioms SmcTuring.Appendix.MultiplyByteCode.common_length
#print axioms SmcTuring.Appendix.MultiplyByteCode.encoded_length
#print axioms SmcTuring.Appendix.MultiplyByteCode.length_take_two
#print axioms SmcTuring.Appendix.MultiplyByteCode.fetch_current_encoding
#print axioms SmcTuring.Appendix.MultiplyByteCode.fetch_written_encoding
#print axioms SmcTuring.Appendix.MultiplyByteCode.add_patch
#print axioms SmcTuring.Appendix.MultiplyByteCode.fetch_patched_add
#print axioms SmcTuring.Appendix.MultiplyByteCode.fetch_patched_current_add
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_effect
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_memory
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_accumulator
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_stack
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_carry
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_pc
#print axioms SmcTuring.Appendix.MultiplyByteExecution.written_word
#print axioms SmcTuring.Appendix.MultiplyByteExecution.execute_frame
#print axioms SmcTuring.Appendix.MultiplyByteExecution.load_frame
#print axioms SmcTuring.Appendix.MultiplyByteExecution.footprint_length
#print axioms SmcTuring.Appendix.MultiplyByteExecution.footprint_nonempty
#print axioms SmcTuring.Appendix.MultiplyByteExecution.common_execution
#print axioms SmcTuring.Appendix.MultiplyByteExecution.and_native_encoding
#print axioms SmcTuring.Appendix.MultiplyByteExecution.and_native_execution
#print axioms SmcTuring.Appendix.MultiplyByteExecution.and_clears_carry
#print axioms SmcTuring.Appendix.MultiplyByteExecution.add_carry
#print axioms SmcTuring.Appendix.MultiplyByteExecution.shift_left_carry
#print axioms SmcTuring.Appendix.MultiplyByteExecution.shift_right_carry
#print axioms SmcTuring.Appendix.MultiplyByteExecution.step_current_encoding
#print axioms SmcTuring.Appendix.MultiplyByteExecution.step_patched_add
#print axioms SmcTuring.Appendix.MultiplyByteExecution.trace_run
#print axioms SmcTuring.Appendix.MultiplyByteExecution.run_append
#print axioms SmcTuring.Appendix.MultiplyByteExecution.trace_append
#print axioms SmcTuring.Appendix.MultiplyByteExecution.owned_append
#print axioms SmcTuring.Appendix.MultiplyRefinement.destination_dependency
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_destination
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_value
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_accumulator
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_carry
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_stack
#print axioms SmcTuring.Appendix.MultiplyRefinement.translate_length
#print axioms SmcTuring.Appendix.MultiplyRefinement.execute_pc
#print axioms SmcTuring.Appendix.MultiplyRefinement.execute_read_destination
#print axioms SmcTuring.Appendix.MultiplyRefinement.execute_read_frame
#print axioms SmcTuring.Appendix.MultiplyRefinement.simulate
#print axioms SmcTuring.Appendix.MultiplyRefinement.forms_length
#print axioms SmcTuring.Appendix.MultiplyRefinement.forms_run
#print axioms SmcTuring.Appendix.MultiplyRefinement.simulate_run
#print axioms SmcTuring.Appendix.MultiplyRefinement.run_stack
#print axioms SmcTuring.Appendix.MultiplyRefinement.run_frame
#print axioms SmcTuring.Appendix.MultiplyRefinement.owned_run
#print axioms SmcTuring.Appendix.MultiplyPackets.literal_current
#print axioms SmcTuring.Appendix.MultiplyPackets.literal_length
#print axioms SmcTuring.Appendix.MultiplyPackets.data_lengths
#print axioms SmcTuring.Appendix.MultiplyPackets.tail_span
#print axioms SmcTuring.Appendix.MultiplyPackets.restore_span
#print axioms SmcTuring.Appendix.MultiplyPackets.packet_count
#print axioms SmcTuring.Appendix.MultiplyPackets.data_lengths_block
#print axioms SmcTuring.Appendix.MultiplyPackets.packet_lengths
#print axioms SmcTuring.Appendix.MultiplyPackets.packet_span
#print axioms SmcTuring.Appendix.MultiplyPackets.positioned_offsets
#print axioms SmcTuring.Appendix.MultiplyPackets.packet_offsets
#print axioms SmcTuring.Appendix.MultiplyPackets.owner_coordinates
#print axioms SmcTuring.Appendix.MultiplyPackets.stack_alias
#print axioms SmcTuring.Appendix.MultiplyPackets.inactive_count
#print axioms SmcTuring.Appendix.MultiplyPackets.inactive_span

#print axioms SmcTuring.Appendix.MultiplyImage.initial_length
#print axioms SmcTuring.Appendix.MultiplyImage.current_length
#print axioms SmcTuring.Appendix.MultiplyImage.add_words
#print axioms SmcTuring.Appendix.MultiplyImage.intact_current
#print axioms SmcTuring.Appendix.MultiplyImage.fetch_current
#print axioms SmcTuring.Appendix.MultiplyImage.initialized_packet
#print axioms SmcTuring.Appendix.MultiplyImage.patch_owner
#print axioms SmcTuring.Appendix.MultiplyImage.owned_field_inside
#print axioms SmcTuring.Appendix.MultiplyImage.separated_tail
#print axioms SmcTuring.Appendix.MultiplyImage.apart_bytes
#print axioms SmcTuring.Appendix.MultiplyImage.image_packet
#print axioms SmcTuring.Appendix.MultiplyImage.initialized_intact
#print axioms SmcTuring.Appendix.MultiplyImage.frame_packet
#print axioms SmcTuring.Appendix.MultiplyImage.store_intact
#print axioms SmcTuring.Appendix.MultiplyImage.execute_intact
#print axioms SmcTuring.Appendix.MultiplyPacking.size_cons
#print axioms SmcTuring.Appendix.MultiplyPacking.size_append
#print axioms SmcTuring.Appendix.MultiplyPacking.place_append
#print axioms SmcTuring.Appendix.MultiplyPacking.placed_lower
#print axioms SmcTuring.Appendix.MultiplyPacking.placed_upper
#print axioms SmcTuring.Appendix.MultiplyPacking.placed_separated
#print axioms SmcTuring.Appendix.MultiplyPacking.initial_intact
#print axioms SmcTuring.Appendix.MultiplyPacking.initial_fetch
#print axioms SmcTuring.Appendix.MultiplyPacking.fields_append
#print axioms SmcTuring.Appendix.MultiplyPacking.fields_owned
#print axioms SmcTuring.Appendix.MultiplyPacking.same_owner_separate
#print axioms SmcTuring.Appendix.MultiplyPacking.owned_separate
#print axioms SmcTuring.Appendix.MultiplyPacking.field_layout
#print axioms SmcTuring.Appendix.MultiplyPacking.placed_field_layout
#print axioms SmcTuring.Appendix.MultiplyPacking.image_frame
#print axioms SmcTuring.Appendix.MultiplyRegions.member
#print axioms SmcTuring.Appendix.MultiplyRegions.entry_bounds
#print axioms SmcTuring.Appendix.MultiplyRegions.separated_append
#print axioms SmcTuring.Appendix.MultiplyRegions.separated
#print axioms SmcTuring.Appendix.MultiplyRegions.capacity
#print axioms SmcTuring.Appendix.MultiplyRegions.field_layout
#print axioms SmcTuring.Appendix.MultiplyRegions.initial_intact
#print axioms SmcTuring.Appendix.MultiplyRegions.image_append
#print axioms SmcTuring.Appendix.MultiplyRegions.image_frame
#print axioms SmcTuring.Appendix.MultiplyRegions.outside_owned
#print axioms SmcTuring.Appendix.MultiplyLayout.data_initial
#print axioms SmcTuring.Appendix.MultiplyLayout.data_initials
#print axioms SmcTuring.Appendix.MultiplyLayout.tail_initials
#print axioms SmcTuring.Appendix.MultiplyLayout.restore_initials
#print axioms SmcTuring.Appendix.MultiplyLayout.pure_initials
#print axioms SmcTuring.Appendix.MultiplyLayout.pure_size
#print axioms SmcTuring.Appendix.MultiplyLayout.data_size
#print axioms SmcTuring.Appendix.MultiplyLayout.tail_size
#print axioms SmcTuring.Appendix.MultiplyLayout.restore_size
#print axioms SmcTuring.Appendix.MultiplyLayout.data_fields
#print axioms SmcTuring.Appendix.MultiplyLayout.tail_fields
#print axioms SmcTuring.Appendix.MultiplyLayout.restore_fields
#print axioms SmcTuring.Appendix.MultiplyLayout.ordered
#print axioms SmcTuring.Appendix.MultiplyLayout.capacity
#print axioms SmcTuring.Appendix.MultiplyLayout.separated
#print axioms SmcTuring.Appendix.MultiplyLayout.field_layout
#print axioms SmcTuring.Appendix.MultiplyLayout.initial_intact
#print axioms SmcTuring.Appendix.MultiplyLayout.initial_fetch
#print axioms SmcTuring.Appendix.MultiplyLayout.pure_fields
#print axioms SmcTuring.Appendix.MultiplyLayout.image_fields
#print axioms SmcTuring.Appendix.MultiplyLayout.slot_owned
#print axioms SmcTuring.Appendix.MultiplyLayout.pointer_owned
#print axioms SmcTuring.Appendix.MultiplyLayout.address_owned
#print axioms SmcTuring.Appendix.MultiplyLayout.slot_fits
#print axioms SmcTuring.Appendix.MultiplyLayout.owned_patch_intact
#print axioms SmcTuring.Appendix.MultiplyData.span_cons
#print axioms SmcTuring.Appendix.MultiplyData.instruction_length
#print axioms SmcTuring.Appendix.MultiplyData.current_translation
#print axioms SmcTuring.Appendix.MultiplyData.execute_pc
#print axioms SmcTuring.Appendix.MultiplyData.constructed_trace
#print axioms SmcTuring.Appendix.MultiplyData.image_trace
#print axioms SmcTuring.Appendix.MultiplyData.run_pc
#print axioms SmcTuring.Appendix.MultiplyData.block_linked
#print axioms SmcTuring.Appendix.MultiplyData.block_dependency_owned
#print axioms SmcTuring.Appendix.MultiplyData.block_capacity
#print axioms SmcTuring.Appendix.MultiplyData.block_placed
#print axioms SmcTuring.Appendix.MultiplyData.block_code_fits
#print axioms SmcTuring.Appendix.MultiplyData.block_trace
#print axioms SmcTuring.Appendix.MultiplyData.block_image_trace
#print axioms SmcTuring.Appendix.MultiplyData.run_intact
#print axioms SmcTuring.Appendix.MultiplyData.block_intact
#print axioms SmcTuring.Appendix.MultiplyData.block_refinement
#print axioms SmcTuring.Appendix.MultiplyLinear.span_cons
#print axioms SmcTuring.Appendix.MultiplyLinear.minimum_length
#print axioms SmcTuring.Appendix.MultiplyLinear.execute_pc
#print axioms SmcTuring.Appendix.MultiplyLinear.constructed_trace
#print axioms SmcTuring.Appendix.MultiplyLinear.image_trace
#print axioms SmcTuring.Appendix.MultiplyLinear.run_pc
#print axioms SmcTuring.Appendix.MultiplyLinear.owned_run
#print axioms SmcTuring.Appendix.MultiplyLinear.run_intact
#print axioms SmcTuring.Appendix.MultiplyLinear.run_common
#print axioms SmcTuring.Appendix.MultiplySetup.call_field_position
#print axioms SmcTuring.Appendix.MultiplySetup.tail_placed
#print axioms SmcTuring.Appendix.MultiplySetup.continuation_placed
#print axioms SmcTuring.Appendix.MultiplySetup.tail_fits
#print axioms SmcTuring.Appendix.MultiplySetup.continuation_fits
#print axioms SmcTuring.Appendix.MultiplySetup.pointer_fits
#print axioms SmcTuring.Appendix.MultiplySetup.address_fits
#print axioms SmcTuring.Appendix.MultiplySetup.call_fits
#print axioms SmcTuring.Appendix.MultiplySetup.slot_alias
#print axioms SmcTuring.Appendix.MultiplySetup.pointer_nonwrap
#print axioms SmcTuring.Appendix.MultiplySetup.slot_apart
#print axioms SmcTuring.Appendix.MultiplySetup.call_apart
#print axioms SmcTuring.Appendix.MultiplySetup.metadata_outside
#print axioms SmcTuring.Appendix.MultiplySetup.run_read_frame
#print axioms SmcTuring.Appendix.MultiplySetup.data_read_frame
#print axioms SmcTuring.Appendix.MultiplySetup.data_ready
#print axioms SmcTuring.Appendix.MultiplySetup.stack_placed
#print axioms SmcTuring.Appendix.MultiplySetup.initial_ready
#print axioms SmcTuring.Appendix.MultiplySetup.single_owner_placed
#print axioms SmcTuring.Appendix.MultiplySetup.initial_mov
#print axioms SmcTuring.Appendix.MultiplySetup.initial_operands
#print axioms SmcTuring.Appendix.MultiplySetup.call_placed
#print axioms SmcTuring.Appendix.MultiplySetup.call_entry_initial
#print axioms SmcTuring.Appendix.MultiplySetup.initial_call
#print axioms SmcTuring.Appendix.MultiplySetup.fixed_call
#print axioms SmcTuring.Appendix.MultiplySetup.word_separate
#print axioms SmcTuring.Appendix.MultiplySetup.control_separate
#print axioms SmcTuring.Appendix.MultiplyPaths.tail_run
#print axioms SmcTuring.Appendix.MultiplyPaths.restore_run
#print axioms SmcTuring.Appendix.MultiplyPaths.forms_run
#print axioms SmcTuring.Appendix.MultiplyPaths.fetched_current
#print axioms SmcTuring.Appendix.MultiplyPaths.call_current
#print axioms SmcTuring.Appendix.MultiplyPaths.tail_trace_intact
#print axioms SmcTuring.Appendix.MultiplyPaths.tail_owned
#print axioms SmcTuring.Appendix.MultiplyPaths.continuation_ownership
#print axioms SmcTuring.Appendix.MultiplyPaths.continuation_straight
#print axioms SmcTuring.Appendix.MultiplyPaths.continuation_span
#print axioms SmcTuring.Appendix.MultiplyPaths.continuation_trace
#print axioms SmcTuring.Appendix.MultiplyPaths.continuation_intact
#print axioms SmcTuring.Appendix.MultiplyPaths.continued_effect
#print axioms SmcTuring.Appendix.MultiplyPaths.continued_ready
#print axioms SmcTuring.Appendix.MultiplyPaths.continued_intact
#print axioms SmcTuring.Appendix.MultiplyPaths.tail_target_pc
#print axioms SmcTuring.Appendix.MultiplyPaths.continued_trace
#print axioms SmcTuring.Appendix.MultiplyPaths.continued_owned
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.view_agreement
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.forms_run
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.data_end_pc
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.guard_displacement
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.target
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.run_effect
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.trace
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.image_trace
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.run_intact
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.run_ready
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.owned
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.refinement
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.run_pc
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.field
#print axioms SmcTuring.Appendix.MultiplyByteBlocks.stack
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.view_agreement
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.slot_word
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.source_ready
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.block_start
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.guard_ready
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.source_data_effect
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.source_stack_effect
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.block
#print axioms SmcTuring.Appendix.MultiplyByteSimulation.advance
#print axioms SmcTuring.Appendix.MultiplyByteLoop.entry_location
#print axioms SmcTuring.Appendix.MultiplyByteLoop.body_boundary
#print axioms SmcTuring.Appendix.MultiplyByteLoop.exit_simulate
#print axioms SmcTuring.Appendix.MultiplyByteLoop.simulate
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.initial_context
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.multiply_simulate
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.execution
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.owned_run_frame
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.trace_frame
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.field_cases
#print axioms SmcTuring.Appendix.MultiplyByteCorrect.correct
#print axioms SmcTuring.Appendix.ConstantAlgebra.zeros_lt
#print axioms SmcTuring.Appendix.ConstantAlgebra.lower_bits_zero
#print axioms SmcTuring.Appendix.ConstantAlgebra.quotient_odd
#print axioms SmcTuring.Appendix.ConstantAlgebra.rest_toNat
#print axioms SmcTuring.Appendix.ConstantAlgebra.decomposition_nat
#print axioms SmcTuring.Appendix.ConstantAlgebra.decomposition
#print axioms SmcTuring.Appendix.ConstantAlgebra.shifted
#print axioms SmcTuring.Appendix.ConstantAlgebra.scale_successor
#print axioms SmcTuring.Appendix.ConstantAlgebra.rest_bound
#print axioms SmcTuring.Appendix.ConstantAlgebra.gap_invariant
#print axioms SmcTuring.Appendix.ConstantAlgebra.tail_correct
#print axioms SmcTuring.Appendix.ConstantAlgebra.first_invariant
#print axioms SmcTuring.Appendix.ConstantAlgebra.correct
#print axioms SmcTuring.Appendix.ConstantAlgebra.gap_count_lt
#print axioms SmcTuring.Appendix.ConstantAlgebra.rest_decreases
#print axioms SmcTuring.Appendix.ConstantAlgebra.top_bit_consumed
#print axioms SmcTuring.Appendix.ConstantAlgebra.zero_correct
#print axioms SmcTuring.Appendix.ConstantAlgebra.signed_low_product
#print axioms SmcTuring.Appendix.ConstantWords.run_append
#print axioms SmcTuring.Appendix.ConstantWords.execute_frame
#print axioms SmcTuring.Appendix.ConstantWords.shift_data
#print axioms SmcTuring.Appendix.ConstantWords.shift_frame
#print axioms SmcTuring.Appendix.ConstantWords.shift_accumulator
#print axioms SmcTuring.Appendix.ConstantWords.copy_effect
#print axioms SmcTuring.Appendix.ConstantWords.accumulate_effect
#print axioms SmcTuring.Appendix.ConstantWords.tail_data
#print axioms SmcTuring.Appendix.ConstantWords.correct
#print axioms SmcTuring.Appendix.ConstantWords.shift_legal
#print axioms SmcTuring.Appendix.ConstantWords.tail_legal
#print axioms SmcTuring.Appendix.ConstantWords.program_legal
#print axioms SmcTuring.Appendix.ConstantWords.tail_owned
#print axioms SmcTuring.Appendix.ConstantWords.program_owned
#print axioms SmcTuring.Appendix.ConstantWords.run_frame
#print axioms SmcTuring.Appendix.ConstantWords.frame
#print axioms SmcTuring.Appendix.ConstantWords.tail_accumulator
#print axioms SmcTuring.Appendix.ConstantWords.accumulator
#print axioms SmcTuring.Appendix.ConstantWords.pure_of_owned_legal
#print axioms SmcTuring.Appendix.ConstantWords.pure
#print axioms SmcTuring.Appendix.ConstantWords.tail_length
#print axioms SmcTuring.Appendix.ConstantWords.program_length
#print axioms SmcTuring.Appendix.ConstantWords.contract
#print axioms SmcTuring.Appendix.ConstantByteCode.count_byte
#print axioms SmcTuring.Appendix.ConstantByteCode.count_bounds
#print axioms SmcTuring.Appendix.ConstantByteCode.shift_payload
#print axioms SmcTuring.Appendix.ConstantByteCode.common_decode
#print axioms SmcTuring.Appendix.ConstantByteCode.form_roundtrip
#print axioms SmcTuring.Appendix.ConstantByteCode.encode_injective
#print axioms SmcTuring.Appendix.ConstantByteCode.encode_length
#print axioms SmcTuring.Appendix.ConstantByteCode.length_bounds
#print axioms SmcTuring.Appendix.ConstantByteCode.common_length
#print axioms SmcTuring.Appendix.ConstantByteCode.encoded_length
#print axioms SmcTuring.Appendix.ConstantByteCode.length_take_two
#print axioms SmcTuring.Appendix.ConstantByteCode.fetch_current_encoding
#print axioms SmcTuring.Appendix.ConstantByteCode.fetch_written_encoding
#print axioms SmcTuring.Appendix.ConstantByteCode.fetch_patched_current_add
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_effect
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_memory
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_accumulator
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_stack
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_carry
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_pc
#print axioms SmcTuring.Appendix.ConstantByteExecution.written_word
#print axioms SmcTuring.Appendix.ConstantByteExecution.execute_frame
#print axioms SmcTuring.Appendix.ConstantByteExecution.load_frame
#print axioms SmcTuring.Appendix.ConstantByteExecution.footprint_length
#print axioms SmcTuring.Appendix.ConstantByteExecution.footprint_nonempty
#print axioms SmcTuring.Appendix.ConstantByteExecution.common_execution
#print axioms SmcTuring.Appendix.ConstantByteExecution.shift_carry
#print axioms SmcTuring.Appendix.ConstantByteExecution.step_current_encoding
#print axioms SmcTuring.Appendix.ConstantByteExecution.step_patched_add
#print axioms SmcTuring.Appendix.ConstantByteExecution.trace_run
#print axioms SmcTuring.Appendix.ConstantByteExecution.run_append
#print axioms SmcTuring.Appendix.ConstantByteExecution.trace_append
#print axioms SmcTuring.Appendix.ConstantByteExecution.owned_append
#print axioms SmcTuring.Appendix.ConstantRefinement.count_value
#print axioms SmcTuring.Appendix.ConstantRefinement.destination_dependency
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_destination
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_value
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_accumulator
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_carry
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_stack
#print axioms SmcTuring.Appendix.ConstantRefinement.translate_length
#print axioms SmcTuring.Appendix.ConstantRefinement.execute_pc
#print axioms SmcTuring.Appendix.ConstantRefinement.execute_read_destination
#print axioms SmcTuring.Appendix.ConstantRefinement.execute_read_frame
#print axioms SmcTuring.Appendix.ConstantRefinement.simulate
#print axioms SmcTuring.Appendix.ConstantRefinement.forms_length
#print axioms SmcTuring.Appendix.ConstantRefinement.forms_run
#print axioms SmcTuring.Appendix.ConstantRefinement.simulate_run
#print axioms SmcTuring.Appendix.ConstantRefinement.run_stack
#print axioms SmcTuring.Appendix.ConstantRefinement.run_frame
#print axioms SmcTuring.Appendix.ConstantRefinement.owned_run
#print axioms SmcTuring.Appendix.ConstantImage.initial_length
#print axioms SmcTuring.Appendix.ConstantImage.current_length
#print axioms SmcTuring.Appendix.ConstantImage.intact_current
#print axioms SmcTuring.Appendix.ConstantImage.fetch_current
#print axioms SmcTuring.Appendix.ConstantImage.initialized_packet
#print axioms SmcTuring.Appendix.ConstantImage.patch_owner
#print axioms SmcTuring.Appendix.ConstantImage.owned_field_inside
#print axioms SmcTuring.Appendix.ConstantImage.separated_tail
#print axioms SmcTuring.Appendix.ConstantImage.apart_bytes
#print axioms SmcTuring.Appendix.ConstantImage.image_packet
#print axioms SmcTuring.Appendix.ConstantImage.initialized_intact
#print axioms SmcTuring.Appendix.ConstantImage.frame_packet
#print axioms SmcTuring.Appendix.ConstantImage.store_intact
#print axioms SmcTuring.Appendix.ConstantImage.execute_intact
#print axioms SmcTuring.Appendix.ConstantPacking.size_cons
#print axioms SmcTuring.Appendix.ConstantPacking.size_append
#print axioms SmcTuring.Appendix.ConstantPacking.place_append
#print axioms SmcTuring.Appendix.ConstantPacking.placed_lower
#print axioms SmcTuring.Appendix.ConstantPacking.placed_upper
#print axioms SmcTuring.Appendix.ConstantPacking.placed_separated
#print axioms SmcTuring.Appendix.ConstantPacking.initial_intact
#print axioms SmcTuring.Appendix.ConstantPacking.initial_fetch
#print axioms SmcTuring.Appendix.ConstantPacking.fields_append
#print axioms SmcTuring.Appendix.ConstantPacking.fields_owned
#print axioms SmcTuring.Appendix.ConstantPacking.same_owner_separate
#print axioms SmcTuring.Appendix.ConstantPacking.owned_separate
#print axioms SmcTuring.Appendix.ConstantPacking.field_layout
#print axioms SmcTuring.Appendix.ConstantPacking.placed_field_layout
#print axioms SmcTuring.Appendix.ConstantPacking.image_frame
#print axioms SmcTuring.Appendix.ConstantData.span_cons
#print axioms SmcTuring.Appendix.ConstantData.instruction_length
#print axioms SmcTuring.Appendix.ConstantData.current_translation
#print axioms SmcTuring.Appendix.ConstantData.execute_pc
#print axioms SmcTuring.Appendix.ConstantData.constructed_trace
#print axioms SmcTuring.Appendix.ConstantData.image_trace
#print axioms SmcTuring.Appendix.ConstantData.run_pc
#print axioms SmcTuring.Appendix.ConstantData.run_intact
#print axioms SmcTuring.Appendix.ConstantSimulation.shift_uses
#print axioms SmcTuring.Appendix.ConstantSimulation.copy_uses
#print axioms SmcTuring.Appendix.ConstantSimulation.accumulate_uses
#print axioms SmcTuring.Appendix.ConstantSimulation.tail_uses
#print axioms SmcTuring.Appendix.ConstantSimulation.program_uses
#print axioms SmcTuring.Appendix.ConstantSimulation.view_agreement
#print axioms SmcTuring.Appendix.ConstantSimulation.compiled_agreement
#print axioms SmcTuring.Appendix.ConstantSimulation.carry
#print axioms SmcTuring.Appendix.ConstantSimulation.effect
#print axioms SmcTuring.Appendix.ConstantSimulation.two_field_layout
#print axioms SmcTuring.Appendix.ConstantSimulation.original_image_correct
#print axioms SmcTuring.Appendix.ConstantShape.span_append
#print axioms SmcTuring.Appendix.ConstantShape.shift_span
#print axioms SmcTuring.Appendix.ConstantShape.copy_span
#print axioms SmcTuring.Appendix.ConstantShape.accumulate_span
#print axioms SmcTuring.Appendix.ConstantShape.tail_span_independent
#print axioms SmcTuring.Appendix.ConstantShape.program_span_independent
#print axioms SmcTuring.Appendix.ConstantShape.plain_append
#print axioms SmcTuring.Appendix.ConstantShape.shift_plain
#print axioms SmcTuring.Appendix.ConstantShape.copy_plain
#print axioms SmcTuring.Appendix.ConstantShape.accumulate_plain
#print axioms SmcTuring.Appendix.ConstantShape.plain_linked
#print axioms SmcTuring.Appendix.ConstantShape.linked_append
#print axioms SmcTuring.Appendix.ConstantShape.tail_shape
#print axioms SmcTuring.Appendix.ConstantShape.program_shape
#print axioms SmcTuring.Appendix.ConstantShape.inactive_plain
#print axioms SmcTuring.Appendix.ConstantShape.active_span
#print axioms SmcTuring.Appendix.ConstantShape.active_linked
#print axioms SmcTuring.Appendix.ConstantShape.active_owned
#print axioms SmcTuring.Appendix.ConstantRegions.member
#print axioms SmcTuring.Appendix.ConstantRegions.entry_bounds
#print axioms SmcTuring.Appendix.ConstantRegions.separated_append
#print axioms SmcTuring.Appendix.ConstantRegions.capacity
#print axioms SmcTuring.Appendix.ConstantRegions.field_layout
#print axioms SmcTuring.Appendix.ConstantRegions.initial_intact
#print axioms SmcTuring.Appendix.ConstantRegions.image_append
#print axioms SmcTuring.Appendix.ConstantRegions.image_frame
#print axioms SmcTuring.Appendix.ConstantRegions.outside_owned
#print axioms SmcTuring.Appendix.ConstantGeometry.ops_span
#print axioms SmcTuring.Appendix.ConstantGeometry.storage_size
#print axioms SmcTuring.Appendix.ConstantGeometry.linked
#print axioms SmcTuring.Appendix.ConstantGeometry.placed
#print axioms SmcTuring.Appendix.ConstantGeometry.separated
#print axioms SmcTuring.Appendix.ConstantGeometry.capacity
#print axioms SmcTuring.Appendix.ConstantGeometry.data_member
#print axioms SmcTuring.Appendix.ConstantGeometry.data_owned
#print axioms SmcTuring.Appendix.ConstantGeometry.scratch_owned
#print axioms SmcTuring.Appendix.ConstantGeometry.distinct
#print axioms SmcTuring.Appendix.ConstantGeometry.code_fits
#print axioms SmcTuring.Appendix.ConstantGeometry.two_field_layout
#print axioms SmcTuring.Appendix.ConstantCorrect.data_initial
#print axioms SmcTuring.Appendix.ConstantCorrect.correct
#print axioms SmcTuring.Appendix.ConstantCorrect.reusable_trace
#print axioms SmcTuring.Appendix.ConstantRegions.separated
#print axioms SmcTuring.Appendix.ConstantCorrect.reusable_correct
#print axioms SmcTuring.Appendix.ZeroImage.packet_length
#print axioms SmcTuring.Appendix.ZeroImage.field_owned
#print axioms SmcTuring.Appendix.ZeroImage.separated
#print axioms SmcTuring.Appendix.ZeroImage.initial_intact
#print axioms SmcTuring.Appendix.ZeroImage.current_form
#print axioms SmcTuring.Appendix.ZeroImage.current_value
#print axioms SmcTuring.Appendix.ZeroImage.fetched
#print axioms SmcTuring.Appendix.ZeroImage.step_correct
#print axioms SmcTuring.Appendix.ZeroImage.effect
#print axioms SmcTuring.Appendix.ZeroImage.written_zero
#print axioms SmcTuring.Appendix.ZeroImage.intact_after
#print axioms SmcTuring.Appendix.ZeroImage.frame
#print axioms SmcTuring.Appendix.ZeroImage.trace
#print axioms SmcTuring.Appendix.ZeroImage.owned_run
#print axioms SmcTuring.Appendix.ZeroImage.correct
#print axioms SmcTuring.Appendix.ZeroImage.original_image_correct
#print axioms SmcTuring.Appendix.ZeroImage.reentry_intact
#print axioms SmcTuring.Appendix.ZeroImage.reentry_trace

#print axioms SmcTuring.Native.ConversionLayout.lengths

#print axioms SmcTuring.Native.ConversionLayout.span_size

#print axioms SmcTuring.Native.ConversionLayout.placed_entries

#print axioms SmcTuring.Native.ConversionLayout.endpoint

#print axioms SmcTuring.Native.ConversionLayout.separated

#print axioms SmcTuring.Native.ConversionLayout.source_toNat

#print axioms SmcTuring.Native.ConversionLayout.destination_toNat

#print axioms SmcTuring.Native.ConversionLayout.outside

#print axioms SmcTuring.Native.ConversionLayout.first_hits

#print axioms SmcTuring.Native.ConversionLayout.second_hits

#print axioms SmcTuring.Native.ConversionLayout.third_hits

#print axioms SmcTuring.Native.ConversionLayout.first_next

#print axioms SmcTuring.Native.ConversionLayout.second_next

#print axioms SmcTuring.Native.ConversionLayout.third_next

#print axioms SmcTuring.Native.ConversionEffects.source_outside

#print axioms SmcTuring.Native.ConversionEffects.destination_outside

#print axioms SmcTuring.Native.ConversionEffects.first_effect

#print axioms SmcTuring.Native.ConversionEffects.second_effect

#print axioms SmcTuring.Native.ConversionEffects.third_effect

#print axioms SmcTuring.Native.ConversionEffects.swapped_pc

#print axioms SmcTuring.Native.ConversionEffects.stored_effect

#print axioms SmcTuring.Native.ConversionEffects.stored_pc

#print axioms SmcTuring.Native.ConversionEffects.original_source_read

#print axioms SmcTuring.Native.ConversionEffects.source_read_after_stored

#print axioms SmcTuring.Native.ConversionEffects.restored_memory

#print axioms SmcTuring.Native.ConversionEffects.effect

#print axioms SmcTuring.Native.ConversionEffects.destination_value

#print axioms SmcTuring.Native.ConversionEffects.source_value

#print axioms SmcTuring.Native.ConversionEffects.frame

#print axioms SmcTuring.Native.ConversionImage.initial_intact

#print axioms SmcTuring.Native.ConversionImage.source_external

#print axioms SmcTuring.Native.ConversionImage.destination_external

#print axioms SmcTuring.Native.ConversionImage.swapped_intact

#print axioms SmcTuring.Native.ConversionImage.stored_intact

#print axioms SmcTuring.Native.ConversionImage.finish_intact

#print axioms SmcTuring.Native.ConversionImage.fetched

#print axioms SmcTuring.Native.ConversionImage.trace

#print axioms SmcTuring.Native.ConversionImage.correct

#print axioms SmcTuring.Native.ConversionImage.original_image_correct

#print axioms SmcTuring.Native.ConversionImage.reentry_trace

#print axioms SmcTuring.Native.ConversionImage.reentry_effect

#print axioms SmcTuring.Native.ConversionOperands.owner_prefix_outside

#print axioms SmcTuring.Native.ConversionOperands.destination_prefix

#print axioms SmcTuring.Native.ConversionOperands.destination_fetch

#print axioms SmcTuring.Native.ConversionOperands.source_prefix

#print axioms SmcTuring.Native.ConversionOperands.source_fetch

#print axioms SmcTuring.Native.ConversionOwnership.first_address

#print axioms SmcTuring.Native.ConversionOwnership.second_address

#print axioms SmcTuring.Native.ConversionOwnership.third_address

#print axioms SmcTuring.Native.ConversionOwnership.supported_run

#print axioms SmcTuring.Native.ConversionOwnership.code_owned_run

#print axioms SmcTuring.Native.ConversionOwnership.whole_intact

#print axioms SmcTuring.Native.ConversionOwnership.original_image_correct

#print axioms SmcTuring.Native.StringCopy.adjacent_put

#print axioms SmcTuring.Native.StringCopy.empty_put

#print axioms SmcTuring.Native.StringCopy.apart_tail

#print axioms SmcTuring.Native.StringCopy.source_outside

#print axioms SmcTuring.Native.StringCopy.tail_read

#print axioms SmcTuring.Native.StringCopy.effect

#print axioms SmcTuring.Native.StringCopy.copied

#print axioms SmcTuring.Native.StringCopy.source_preserved

#print axioms SmcTuring.Native.StringCopy.frame

#print axioms SmcTuring.Native.StringCopy.run_append

#print axioms SmcTuring.Native.StringPlan.sum_replicate

#print axioms SmcTuring.Native.StringPlan.total

#print axioms SmcTuring.Native.StringPlan.remainder_two

#print axioms SmcTuring.Native.StringPlan.remainder_four

#print axioms SmcTuring.Native.StringPlan.remainder_one

#print axioms SmcTuring.Native.StringPlan.legal

#print axioms SmcTuring.Native.StringPlan.positive

#print axioms SmcTuring.Native.StringPlan.opcode_nonempty

#print axioms SmcTuring.Native.StringPlan.opcode_length

#print axioms SmcTuring.Native.StringPlan.correct

#print axioms SmcTuring.Native.StringPlan.copied

#print axioms SmcTuring.Native.StringPlan.source_preserved

#print axioms SmcTuring.Native.StringPlan.frame

#print axioms SmcTuring.Native.StringCursor.exchange_twice

#print axioms SmcTuring.Native.StringCursor.effect

#print axioms SmcTuring.Native.StringCursor.advanced_pointer

#print axioms SmcTuring.Native.StringCursor.restored_index

#print axioms SmcTuring.Native.StringCursor.restored_field

#print axioms SmcTuring.Native.StringCursor.encoded_sum

#print axioms SmcTuring.Native.StringCursor.advanced_toNat

#print axioms SmcTuring.Native.StringCursor.no_borrow

#print axioms SmcTuring.Native.StringCursor.pair_correct

#print axioms SmcTuring.Native.StringFields.prepared_source

#print axioms SmcTuring.Native.StringFields.copied_effect

#print axioms SmcTuring.Native.StringFields.cursor_outside

#print axioms SmcTuring.Native.StringFields.copy_word_commute

#print axioms SmcTuring.Native.StringFields.restored_fields

#print axioms SmcTuring.Native.StringFields.effect

#print axioms SmcTuring.Native.StringFields.destination_value

#print axioms SmcTuring.Native.StringFields.frame

#print axioms SmcTuring.Native.StringPlan.two_bit_count

#print axioms SmcTuring.Native.StringPlan.four_bit_count

#print axioms SmcTuring.Native.StringPlan.one_bit_count

#print axioms SmcTuring.Native.StringPlan.literal_widths

#print axioms SmcTuring.Native.StringCodec.initial_length

#print axioms SmcTuring.Native.StringCodec.exchange_length

#print axioms SmcTuring.Native.StringCodec.sub_length

#print axioms SmcTuring.Native.StringCodec.field_end

#print axioms SmcTuring.Native.StringCodec.destination_field_end

#print axioms SmcTuring.Native.StringCodec.body_coordinate

#print axioms SmcTuring.Native.StringCodec.whole_length

#print axioms SmcTuring.Native.StringForm.native_extra_none

#print axioms SmcTuring.Native.StringForm.native_decode

#print axioms SmcTuring.Native.StringForm.form_roundtrip

#print axioms SmcTuring.Native.StringForm.native_extra_length_none

#print axioms SmcTuring.Native.StringForm.encoded_length

#print axioms SmcTuring.Native.StringForm.length_bound

#print axioms SmcTuring.Native.StringForm.length_take_three

#print axioms SmcTuring.Native.StringForm.fetch_current_encoding

#print axioms SmcTuring.Native.StringExecution.native_effect

#print axioms SmcTuring.Native.StringExecution.native_indices

#print axioms SmcTuring.Native.StringExecution.direction_preserved

#print axioms SmcTuring.Native.StringExecution.run_direction

#print axioms SmcTuring.Native.StringExecution.move_effect

#print axioms SmcTuring.Native.StringExecution.move_frame

#print axioms SmcTuring.Native.StringExecution.move_accumulator

#print axioms SmcTuring.Native.StringExecution.move_stack

#print axioms SmcTuring.Native.StringExecution.move_carry

#print axioms SmcTuring.Native.StringExecution.exchange_source

#print axioms SmcTuring.Native.StringExecution.exchange_destination

#print axioms SmcTuring.Native.StringExecution.trace_run

#print axioms SmcTuring.Native.StringExecution.run_append

#print axioms SmcTuring.Native.StringExecution.trace_append

#print axioms SmcTuring.Native.StringExecution.step_current_encoding

#print axioms SmcTuring.Native.StringMoves.code_cons

#print axioms SmcTuring.Native.StringMoves.span_cons

#print axioms SmcTuring.Native.StringMoves.index_advance

#print axioms SmcTuring.Native.StringMoves.move_view

#print axioms SmcTuring.Native.StringMoves.run_view

#print axioms SmcTuring.Native.StringMoves.run_pc

#print axioms SmcTuring.Native.StringMoves.run_source

#print axioms SmcTuring.Native.StringMoves.run_destination

#print axioms SmcTuring.Native.StringMoves.run_accumulator

#print axioms SmcTuring.Native.StringMoves.run_stack

#print axioms SmcTuring.Native.StringMoves.run_carry

#print axioms SmcTuring.Native.StringMoves.effect

#print axioms SmcTuring.Native.StringMoves.copied

#print axioms SmcTuring.Native.StringMoves.frame

#print axioms SmcTuring.Native.StringMoveTrace.current_head

#print axioms SmcTuring.Native.StringMoveTrace.current_tail

#print axioms SmcTuring.Native.StringMoveTrace.tail_separate

#print axioms SmcTuring.Native.StringMoveTrace.next_location

#print axioms SmcTuring.Native.StringMoveTrace.constructed_trace

#print axioms SmcTuring.Native.StringMoveTrace.image_trace

#print axioms SmcTuring.Native.StringMoveTrace.correct

#print axioms SmcTuring.Native.StringMoveTrace.code_preserved

#print axioms SmcTuring.Native.StringTemplate.copied_window

#print axioms SmcTuring.Native.StringTemplate.copied_fetch

#print axioms SmcTuring.Native.StringTemplate.delta_internal

#print axioms SmcTuring.Native.StringTemplate.relative_internal

#print axioms SmcTuring.Native.StringTemplate.signed_internal

#print axioms SmcTuring.Native.StringTemplate.rip_internal

#print axioms SmcTuring.Native.StringTemplate.rip_target

#print axioms SmcTuring.Native.StringTemplate.absolute_external

#print axioms SmcTuring.Native.StringTemplate.absolute_target

#print axioms SmcTuring.Native.StringOperands.exchange_encoding

#print axioms SmcTuring.Native.StringOperands.exchange_length

#print axioms SmcTuring.Native.StringOperands.sign_extend_small

#print axioms SmcTuring.Native.StringOperands.sign_extend_full

#print axioms SmcTuring.Native.StringOperands.subtract_encoding

#print axioms SmcTuring.Native.StringOperands.subtract_length

#print axioms SmcTuring.Native.StringOperands.exchange_hits

#print axioms SmcTuring.Native.StringOperands.subtract_next

#print axioms SmcTuring.Native.StringOperands.subtract_effect

#print axioms SmcTuring.Native.StringOperands.source_effect

#print axioms SmcTuring.Native.StringOperands.destination_effect

#print axioms SmcTuring.Native.StringWindow.bytes_at_slice

#print axioms SmcTuring.Native.StringWindow.packet_window

#print axioms SmcTuring.Native.StringWindow.initial_word

#print axioms SmcTuring.Native.StringWindow.load_frame

#print axioms SmcTuring.Native.StringInit.first_displacement

#print axioms SmcTuring.Native.StringInit.second_displacement

#print axioms SmcTuring.Native.StringInit.leading_length

#print axioms SmcTuring.Native.StringInit.initial_shape

#print axioms SmcTuring.Native.StringInit.forms_encoding

#print axioms SmcTuring.Native.StringInit.initialized_pointer

#print axioms SmcTuring.Native.StringInit.native_run

#print axioms SmcTuring.Native.StringInit.effect

#print axioms SmcTuring.Native.StringRestore.forms_encoding

#print axioms SmcTuring.Native.StringRestore.no_borrow

#print axioms SmcTuring.Native.StringRestore.loaded_exchange

#print axioms SmcTuring.Native.StringRestore.source_effect

#print axioms SmcTuring.Native.StringRestore.destination_effect

#print axioms SmcTuring.Native.StringRestore.trace

#print axioms SmcTuring.Native.StringInitTrace.trace

#print axioms SmcTuring.Native.StringSetup.cursor_range

#print axioms SmcTuring.Native.StringSetup.source_field_fits

#print axioms SmcTuring.Native.StringSetup.destination_field_fits

#print axioms SmcTuring.Native.StringSetup.initializer_fits

#print axioms SmcTuring.Native.StringSetup.source_effect

#print axioms SmcTuring.Native.StringSetup.destination_window

#print axioms SmcTuring.Native.StringSetup.effect

#print axioms SmcTuring.Native.StringSetupTrace.forms_encoding

#print axioms SmcTuring.Native.StringSetupTrace.source_field_frame

#print axioms SmcTuring.Native.StringSetupTrace.source_trace

#print axioms SmcTuring.Native.StringSetupTrace.trace

#print axioms SmcTuring.Native.StringSetupTrace.initialized_trace

#print axioms SmcTuring.Native.StringProgram.body_encoding

#print axioms SmcTuring.Native.StringProgram.prefix_extent

#print axioms SmcTuring.Native.StringProgram.encoding

#print axioms SmcTuring.Native.StringProgram.code_extent

#print axioms SmcTuring.Native.StringProgram.instruction_count

#print axioms SmcTuring.Native.StringProgram.setup_legal

#print axioms SmcTuring.Native.StringProgram.restore_legal

#print axioms SmcTuring.Native.StringProgram.legal

#print axioms SmcTuring.Native.StringMacroLayout.split_bytes

#print axioms SmcTuring.Native.StringMacroLayout.coordinates

#print axioms SmcTuring.Native.StringMacroLayout.field_coordinates

#print axioms SmcTuring.Native.StringMacroLayout.repeat_length

#print axioms SmcTuring.Native.StringMacroLayout.body_bound

#print axioms SmcTuring.Native.StringMacroLayout.span_bound

#print axioms SmcTuring.Native.StringMacroLayout.internal_range

#print axioms SmcTuring.Native.StringMacroLayout.tail_ranges

#print axioms SmcTuring.Native.StringMacroLayout.source_capacity

#print axioms SmcTuring.Native.StringMacroLayout.destination_capacity

#print axioms SmcTuring.Native.StringMacroLayout.prefix_capacity

#print axioms SmcTuring.Native.StringMacroLayout.fields_separate

#print axioms SmcTuring.Native.StringMacroLayout.source_cursor_frame

#print axioms SmcTuring.Native.StringMacroLayout.destination_cursor_frame

#print axioms SmcTuring.Native.StringMacroLayout.copy_code_frame

#print axioms SmcTuring.Native.StringMacroImage.windows

#print axioms SmcTuring.Native.StringMacroImage.initializer_windows

#print axioms SmcTuring.Native.StringMacroImage.initialized_pointers

#print axioms SmcTuring.Native.StringMacroImage.initial_words

#print axioms SmcTuring.Native.StringMacroImage.destination_word_outside

#print axioms SmcTuring.Native.StringMacroImage.prefix_effect

#print axioms SmcTuring.Native.StringMacroImage.prefix_trace

#print axioms SmcTuring.Native.StringMacroImage.prepared_window

#print axioms SmcTuring.Native.StringMacroEffects.state_eq

#print axioms SmcTuring.Native.StringMacroEffects.setup_effect

#print axioms SmcTuring.Native.StringMacroEffects.copied_effect

#print axioms SmcTuring.Native.StringMacroEffects.copied_source_load

#print axioms SmcTuring.Native.StringMacroEffects.copied_destination_load

#print axioms SmcTuring.Native.StringMacroEffects.source_effect

#print axioms SmcTuring.Native.StringMacroEffects.source_destination_load

#print axioms SmcTuring.Native.StringMacroEffects.finish_effect

#print axioms SmcTuring.Native.StringMacroEffects.program_run

#print axioms SmcTuring.Native.StringMacroTrace.setup_trace

#print axioms SmcTuring.Native.StringMacroTrace.body_trace

#print axioms SmcTuring.Native.StringMacroTrace.copied_window

#print axioms SmcTuring.Native.StringMacroTrace.source_trace

#print axioms SmcTuring.Native.StringMacroTrace.destination_window

#print axioms SmcTuring.Native.StringMacroTrace.destination_trace

#print axioms SmcTuring.Native.StringMacroTrace.trace

#print axioms SmcTuring.Native.StringMacroTrace.correct

#print axioms SmcTuring.Native.StringMacroTrace.code_preserved

#print axioms SmcTuring.Native.StringMacroTrace.reusable

#print axioms SmcTuring.Native.StringMacroTrace.run_correct

#print axioms SmcTuring.Native.StringMacroTrace.frame

#print axioms SmcTuring.Native.StringMacroTrace.source_preserved

#print axioms SmcTuring.Native.StringMacroTrace.reentry_trace


#print axioms SmcTuring.Native.TemplateRelocation.bound_length

#print axioms SmcTuring.Native.TemplateRelocation.encoded_length

#print axioms SmcTuring.Native.TemplateRelocation.length_positive

#print axioms SmcTuring.Native.TemplateRelocation.length_bound

#print axioms SmcTuring.Native.TemplateRelocation.bytes_cons

#print axioms SmcTuring.Native.TemplateRelocation.bytes_length

#print axioms SmcTuring.Native.TemplateRelocation.instruction_count

#print axioms SmcTuring.Native.TemplateRelocation.places_lower

#print axioms SmcTuring.Native.TemplateRelocation.places_upper

#print axioms SmcTuring.Native.TemplateRelocation.bound_member

#print axioms SmcTuring.Native.TemplateRelocation.whole_packet

#print axioms SmcTuring.Native.TemplateRelocation.whole_fetch

#print axioms SmcTuring.Native.TemplateRelocation.moffs_address

#print axioms SmcTuring.Native.TemplateRelocation.moffs_field

#print axioms SmcTuring.Native.TemplateRelocation.memory_field

#print axioms SmcTuring.Native.TemplateRelocation.memory_target

#print axioms SmcTuring.Native.TemplateRelocation.call_target

#print axioms SmcTuring.Native.TemplateRelocation.internal_rip

#print axioms SmcTuring.Native.TemplateRelocation.internal_call

#print axioms SmcTuring.Native.TemplateRelocation.external_moffs

#print axioms SmcTuring.Native.TemplateRelocation.external_absolute

#print axioms SmcTuring.Native.TemplateRelocation.moffs_position

#print axioms SmcTuring.Native.TemplateRelocation.memory_position

#print axioms SmcTuring.Native.TemplateRelocation.call_position

#print axioms SmcTuring.Native.TemplateCopy.complete_image

#print axioms SmcTuring.Native.TemplateCopy.packet

#print axioms SmcTuring.Native.TemplateCopy.fetch

#print axioms SmcTuring.Native.TemplateCopy.packet_capacity

#print axioms SmcTuring.Native.TemplateCopy.moffs_payload

#print axioms SmcTuring.Native.TemplateCopy.memory_target

#print axioms SmcTuring.Native.TemplateCopy.call_target

#print axioms SmcTuring.Native.TemplateCopy.correct

#print axioms SmcTuring.Native.TemplateCopy.initialized_blueprint

#print axioms SmcTuring.Native.TemplateCopy.initialized_macro

#print axioms SmcTuring.Native.TemplateCopy.ready_initialized

#print axioms SmcTuring.Native.TemplateCopy.ready_initial

#print axioms SmcTuring.Native.TemplateCopy.original_image_correct

#print axioms SmcTuring.Native.TemplateCopy.internal_target_capacity

#print axioms SmcTuring.Native.TemplateCopy.moffs_position


#print axioms SmcTuring.Native.TemplateRelocation.observed_target

#print axioms SmcTuring.Native.TemplateCopy.original_addresses_correct


#print axioms SmcTuring.Appendix.DivisionAlgebra.step_processed
#print axioms SmcTuring.Appendix.DivisionAlgebra.step_valid
#print axioms SmcTuring.Appendix.DivisionAlgebra.scan_valid
#print axioms SmcTuring.Appendix.DivisionAlgebra.scan_processed
#print axioms SmcTuring.Appendix.DivisionAlgebra.scan_correct
#print axioms SmcTuring.Appendix.DivisionAlgebra.remainder_le_processed
#print axioms SmcTuring.Appendix.DivisionAlgebra.trial_fits
#print axioms SmcTuring.Appendix.DivisionAlgebra.full_word_division
#print axioms SmcTuring.Appendix.DivisionAlgebra.quotient_fits
#print axioms SmcTuring.Appendix.DivisionRepairs.divisor_copy
#print axioms SmcTuring.Appendix.DivisionRepairs.divisor_copy_register
#print axioms SmcTuring.Appendix.DivisionRepairs.exit_selection
#print axioms SmcTuring.Appendix.DivisionRepairs.exit_delta
#print axioms SmcTuring.Appendix.DivisionRepairs.body_continuation
#print axioms SmcTuring.Appendix.DivisionRepairs.reset_owned_field
#print axioms SmcTuring.Appendix.DivisionRepairs.reset_packet
#print axioms SmcTuring.Appendix.DivisionRepairs.reset_fetch
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.sample_sign
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.sample_mask
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.sample_xor
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.borrow_sign
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.normalize_mask
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.negative_bit_mask
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.normalize_negative_mask
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.apply_sign
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.absolute_normalization
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_toNat
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_bound
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_nonnegative_small
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.signed_decomposition
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_nonzero
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.mathematical_magnitude
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.result_pattern
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.quotient_word
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.remainder_word
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.result_sdiv
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.result_srem
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.result_toInt
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_half_iff
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.magnitude_not_min
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.negative_magnitude_one
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.positive_quotient_small
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.quotient_range
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.remainder_range
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.quotient_toInt
#print axioms SmcTuring.Appendix.DivisionSignedAlgebra.remainder_toInt
#print axioms SmcTuring.Appendix.DivisionWords.field_eq
#print axioms SmcTuring.Appendix.DivisionWords.every_instruction_writes
#print axioms SmcTuring.Appendix.DivisionWords.execute_frame
#print axioms SmcTuring.Appendix.DivisionWords.run_frame
#print axioms SmcTuring.Appendix.DivisionWords.run_append
#print axioms SmcTuring.Appendix.DivisionWords.embedded_run
#print axioms SmcTuring.Appendix.DivisionWords.copy_effect
#print axioms SmcTuring.Appendix.DivisionWords.pure_of_destinations
#print axioms SmcTuring.Appendix.DivisionWords.body_length
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.doubling_borrow
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.masked_double_no_borrow
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.subtract_restore
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.quotient_bit
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.low_add_carry
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.trial_toNat
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.next_high_toNat
#print axioms SmcTuring.Appendix.DivisionWordAlgebra.signed_result_carry
#print axioms SmcTuring.Appendix.DivisionPrefixes.sample_field
#print axioms SmcTuring.Appendix.DivisionPrefixes.sample_accumulator
#print axioms SmcTuring.Appendix.DivisionPrefixes.sample_carry
#print axioms SmcTuring.Appendix.DivisionPrefixes.sign_field
#print axioms SmcTuring.Appendix.DivisionPrefixes.sign_accumulator
#print axioms SmcTuring.Appendix.DivisionPrefixes.sign_carry
#print axioms SmcTuring.Appendix.DivisionPrefixes.masked_normalization
#print axioms SmcTuring.Appendix.DivisionPrefixes.normalize_field
#print axioms SmcTuring.Appendix.DivisionPrefixes.normalize_accumulator
#print axioms SmcTuring.Appendix.DivisionPrefixes.normalize_carry
#print axioms SmcTuring.Appendix.DivisionPrefixes.sign_length
#print axioms SmcTuring.Appendix.DivisionPrefixes.normalize_length
#print axioms SmcTuring.Appendix.DivisionBody.body_field
#print axioms SmcTuring.Appendix.DivisionBody.body_accumulator
#print axioms SmcTuring.Appendix.DivisionBody.body_carry
#print axioms SmcTuring.Appendix.DivisionBody.body_frame
#print axioms SmcTuring.Appendix.DivisionBody.body_pure
#print axioms SmcTuring.Appendix.DivisionBody.body_low
#print axioms SmcTuring.Appendix.DivisionBody.body_high
#print axioms SmcTuring.Appendix.DivisionBody.body_counter
#print axioms SmcTuring.Appendix.DivisionBody.body_divisor
#print axioms SmcTuring.Appendix.DivisionBody.restoring_remainder
#print axioms SmcTuring.Appendix.DivisionStages.signed_initial_shape
#print axioms SmcTuring.Appendix.DivisionStages.initial_field
#print axioms SmcTuring.Appendix.DivisionStages.initial_accumulator
#print axioms SmcTuring.Appendix.DivisionStages.initial_carry
#print axioms SmcTuring.Appendix.DivisionStages.initial_length
#print axioms SmcTuring.Appendix.DivisionStages.finish_field
#print axioms SmcTuring.Appendix.DivisionStages.finish_accumulator
#print axioms SmcTuring.Appendix.DivisionStages.finish_carry
#print axioms SmcTuring.Appendix.DivisionStages.finish_signed_result
#print axioms SmcTuring.Appendix.DivisionStages.finish_length
#print axioms SmcTuring.Appendix.DivisionStages.initial_frame
#print axioms SmcTuring.Appendix.DivisionStages.initial_pure
#print axioms SmcTuring.Appendix.DivisionStages.initial_inputs
#print axioms SmcTuring.Appendix.DivisionStages.finish_frame
#print axioms SmcTuring.Appendix.DivisionStages.finish_pure
#print axioms SmcTuring.Appendix.DivisionStages.finish_signed_carry
#print axioms SmcTuring.Appendix.DivisionPacked.prefix_bound
#print axioms SmcTuring.Appendix.DivisionPacked.quotient_bound
#print axioms SmcTuring.Appendix.DivisionPacked.packed_bit
#print axioms SmcTuring.Appendix.DivisionPacked.packed_shift
#print axioms SmcTuring.Appendix.DivisionPacked.scan_next
#print axioms SmcTuring.Appendix.DivisionPacked.next_low_toNat
#print axioms SmcTuring.Appendix.DivisionPacked.packed_step
#print axioms SmcTuring.Appendix.DivisionIteration.initial_invariant
#print axioms SmcTuring.Appendix.DivisionIteration.advance
#print axioms SmcTuring.Appendix.DivisionIteration.invariant
#print axioms SmcTuring.Appendix.DivisionIteration.correct
#print axioms SmcTuring.Appendix.DivisionIteration.accumulator
#print axioms SmcTuring.Appendix.DivisionIteration.frame
#print axioms SmcTuring.Appendix.DivisionIteration.repeated_execution
#print axioms SmcTuring.Appendix.DivisionIteration.repeated_length
#print axioms SmcTuring.Appendix.DivisionIteration.repeated_pure
#print axioms SmcTuring.Appendix.DivisionDataCorrect.initialized
#print axioms SmcTuring.Appendix.DivisionDataCorrect.divisor_nonzero
#print axioms SmcTuring.Appendix.DivisionDataCorrect.loop_result
#print axioms SmcTuring.Appendix.DivisionDataCorrect.loop_sign
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_execution
#print axioms SmcTuring.Appendix.DivisionDataCorrect.result_pattern
#print axioms SmcTuring.Appendix.DivisionDataCorrect.signed_quotient
#print axioms SmcTuring.Appendix.DivisionDataCorrect.signed_remainder
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_accumulator
#print axioms SmcTuring.Appendix.DivisionDataCorrect.pure_append
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_pure
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_length
#print axioms SmcTuring.Appendix.DivisionDataCorrect.loop_preserved
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_inputs
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_frame
#print axioms SmcTuring.Appendix.DivisionDataCorrect.displacement_reset
#print axioms SmcTuring.Appendix.DivisionDataCorrect.program_carry
#print axioms SmcTuring.Appendix.DivisionGuard.binding_injective
#print axioms SmcTuring.Appendix.DivisionGuard.guard_separate
#print axioms SmcTuring.Appendix.DivisionGuard.frame
#print axioms SmcTuring.Appendix.DivisionGuard.field
#print axioms SmcTuring.Appendix.DivisionGuard.accumulator
#print axioms SmcTuring.Appendix.DivisionGuard.carry
#print axioms SmcTuring.Appendix.DivisionGuard.displacement
#print axioms SmcTuring.Appendix.DivisionGuard.pure
#print axioms SmcTuring.Appendix.DivisionGuard.invariant
#print axioms SmcTuring.Appendix.DivisionGuard.length
#print axioms SmcTuring.Appendix.DivisionControl.run_append
#print axioms SmcTuring.Appendix.DivisionControl.pure_append
#print axioms SmcTuring.Appendix.DivisionControl.lift_effect
#print axioms SmcTuring.Appendix.DivisionControl.lift_pure
#print axioms SmcTuring.Appendix.DivisionControl.embed_run
#print axioms SmcTuring.Appendix.DivisionControl.embed_pure
#print axioms SmcTuring.Appendix.DivisionControl.round_trip_effect
#print axioms SmcTuring.Appendix.DivisionControl.round_trip_ready
#print axioms SmcTuring.Appendix.DivisionControl.round_trip_pure
#print axioms SmcTuring.Appendix.DivisionControl.ready_lift
#print axioms SmcTuring.Appendix.DivisionControl.initial_ready
#print axioms SmcTuring.Appendix.DivisionControl.lift_length
#print axioms SmcTuring.Appendix.DivisionControl.round_trip_length
#print axioms SmcTuring.Appendix.DivisionBlocks.delta_value
#print axioms SmcTuring.Appendix.DivisionBlocks.delta_nonzero
#print axioms SmcTuring.Appendix.DivisionBlocks.continuations_distinct
#print axioms SmcTuring.Appendix.DivisionBlocks.literal_lengths
#print axioms SmcTuring.Appendix.DivisionBlocks.words_pure
#print axioms SmcTuring.Appendix.DivisionBlocks.words_frame
#print axioms SmcTuring.Appendix.DivisionBlocks.ready_lift
#print axioms SmcTuring.Appendix.DivisionBlocks.call_separate
#print axioms SmcTuring.Appendix.DivisionBlocks.program_effect
#print axioms SmcTuring.Appendix.DivisionBlocks.program_ready
#print axioms SmcTuring.Appendix.DivisionBlocks.program_frame
#print axioms SmcTuring.Appendix.DivisionBlocks.program_pure
#print axioms SmcTuring.Appendix.DivisionBlocks.clear_guard
#print axioms SmcTuring.Appendix.DivisionBlocks.guard_effect
#print axioms SmcTuring.Appendix.DivisionBlocks.body_effect
#print axioms SmcTuring.Appendix.DivisionBlocks.entry_effect
#print axioms SmcTuring.Appendix.DivisionBlocks.finish_effect
#print axioms SmcTuring.Appendix.DivisionBlocks.words_frame_written
#print axioms SmcTuring.Appendix.DivisionBlocks.program_frame_written
#print axioms SmcTuring.Appendix.DivisionBlocks.program_accumulator
#print axioms SmcTuring.Appendix.DivisionBlocks.program_stack
#print axioms SmcTuring.Appendix.DivisionExecution.finish_invariant
#print axioms SmcTuring.Appendix.DivisionExecution.finish_observations
#print axioms SmcTuring.Appendix.DivisionExecution.exit_finishes
#print axioms SmcTuring.Appendix.DivisionExecution.loop_finishes
#print axioms SmcTuring.Appendix.DivisionExecution.loop_run
#print axioms SmcTuring.Appendix.DivisionExecution.divide_finishes
#print axioms SmcTuring.Appendix.DivisionObservations.loop_frame
#print axioms SmcTuring.Appendix.DivisionObservations.loop_pure
#print axioms SmcTuring.Appendix.DivisionObservations.loop_preserves
#print axioms SmcTuring.Appendix.DivisionObservations.source_slots_stable
#print axioms SmcTuring.Appendix.DivisionObservations.divide_pure
#print axioms SmcTuring.Appendix.DivisionObservations.divide_frame
#print axioms SmcTuring.Appendix.DivisionObservations.divide_inputs
#print axioms SmcTuring.Appendix.DivisionObservations.divide_sign
#print axioms SmcTuring.Appendix.DivisionCorrect.selected
#print axioms SmcTuring.Appendix.DivisionCorrect.output
#print axioms SmcTuring.Appendix.DivisionCorrect.carry
#print axioms SmcTuring.Appendix.DivisionCorrect.correct
#print axioms SmcTuring.Appendix.DivisionCorrect.signed_quotient
#print axioms SmcTuring.Appendix.DivisionCorrect.signed_remainder
#print axioms SmcTuring.Appendix.DivisionCorrect.unsigned_quotient
#print axioms SmcTuring.Appendix.DivisionCorrect.unsigned_remainder
#print axioms SmcTuring.Appendix.DivisionByteCode.common_decode
#print axioms SmcTuring.Appendix.DivisionByteCode.subtract_payload
#print axioms SmcTuring.Appendix.DivisionByteCode.right_payload
#print axioms SmcTuring.Appendix.DivisionByteCode.adc_payload
#print axioms SmcTuring.Appendix.DivisionByteCode.form_roundtrip
#print axioms SmcTuring.Appendix.DivisionByteCode.encode_injective
#print axioms SmcTuring.Appendix.DivisionByteCode.encode_length
#print axioms SmcTuring.Appendix.DivisionByteCode.length_bounds
#print axioms SmcTuring.Appendix.DivisionByteCode.common_length
#print axioms SmcTuring.Appendix.DivisionByteCode.encoded_length
#print axioms SmcTuring.Appendix.DivisionByteCode.length_take_two
#print axioms SmcTuring.Appendix.DivisionByteCode.fetch_current_encoding
#print axioms SmcTuring.Appendix.DivisionByteCode.fetch_written_encoding
#print axioms SmcTuring.Appendix.DivisionByteCode.subtract_patch
#print axioms SmcTuring.Appendix.DivisionByteCode.fetch_patched_subtract
#print axioms SmcTuring.Appendix.DivisionByteCode.fetch_patched_current_subtract
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_effect
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_memory
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_accumulator
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_stack
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_carry
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_pc
#print axioms SmcTuring.Appendix.DivisionByteExecution.written_word
#print axioms SmcTuring.Appendix.DivisionByteExecution.execute_frame
#print axioms SmcTuring.Appendix.DivisionByteExecution.load_frame
#print axioms SmcTuring.Appendix.DivisionByteExecution.footprint_length
#print axioms SmcTuring.Appendix.DivisionByteExecution.footprint_nonempty
#print axioms SmcTuring.Appendix.DivisionByteExecution.common_execution
#print axioms SmcTuring.Appendix.DivisionByteExecution.subtract_carry
#print axioms SmcTuring.Appendix.DivisionByteExecution.right31_carry
#print axioms SmcTuring.Appendix.DivisionByteExecution.adc_zero_value
#print axioms SmcTuring.Appendix.DivisionByteExecution.adc_zero_carry
#print axioms SmcTuring.Appendix.DivisionByteExecution.decrement_preserves_carry
#print axioms SmcTuring.Appendix.DivisionByteExecution.step_current_encoding
#print axioms SmcTuring.Appendix.DivisionByteExecution.step_patched_subtract
#print axioms SmcTuring.Appendix.DivisionByteExecution.trace_run
#print axioms SmcTuring.Appendix.DivisionByteExecution.run_append
#print axioms SmcTuring.Appendix.DivisionByteExecution.trace_append
#print axioms SmcTuring.Appendix.DivisionByteExecution.owned_append
#print axioms SmcTuring.Appendix.DivisionRefinement.destination_dependency
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_destination
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_value
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_accumulator
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_carry
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_stack
#print axioms SmcTuring.Appendix.DivisionRefinement.translate_length
#print axioms SmcTuring.Appendix.DivisionRefinement.execute_pc
#print axioms SmcTuring.Appendix.DivisionRefinement.execute_read_destination
#print axioms SmcTuring.Appendix.DivisionRefinement.execute_read_frame
#print axioms SmcTuring.Appendix.DivisionRefinement.simulate
#print axioms SmcTuring.Appendix.DivisionRefinement.forms_length
#print axioms SmcTuring.Appendix.DivisionRefinement.forms_run
#print axioms SmcTuring.Appendix.DivisionRefinement.simulate_run
#print axioms SmcTuring.Appendix.DivisionRefinement.run_stack
#print axioms SmcTuring.Appendix.DivisionRefinement.run_frame
#print axioms SmcTuring.Appendix.DivisionRefinement.owned_run
#print axioms SmcTuring.Appendix.DivisionImage.initial_length
#print axioms SmcTuring.Appendix.DivisionImage.current_length
#print axioms SmcTuring.Appendix.DivisionImage.subtract_words
#print axioms SmcTuring.Appendix.DivisionImage.intact_current
#print axioms SmcTuring.Appendix.DivisionImage.fetch_current
#print axioms SmcTuring.Appendix.DivisionImage.initialized_packet
#print axioms SmcTuring.Appendix.DivisionImage.patch_owner
#print axioms SmcTuring.Appendix.DivisionImage.owned_field_inside
#print axioms SmcTuring.Appendix.DivisionImage.separated_tail
#print axioms SmcTuring.Appendix.DivisionImage.apart_bytes
#print axioms SmcTuring.Appendix.DivisionImage.image_packet
#print axioms SmcTuring.Appendix.DivisionImage.initialized_intact
#print axioms SmcTuring.Appendix.DivisionImage.frame_packet
#print axioms SmcTuring.Appendix.DivisionImage.store_intact
#print axioms SmcTuring.Appendix.DivisionImage.execute_intact
#print axioms SmcTuring.Appendix.DivisionPackets.literal_current
#print axioms SmcTuring.Appendix.DivisionPackets.literal_length
#print axioms SmcTuring.Appendix.DivisionPackets.data_span
#print axioms SmcTuring.Appendix.DivisionPackets.tail_span
#print axioms SmcTuring.Appendix.DivisionPackets.restore_span
#print axioms SmcTuring.Appendix.DivisionPackets.span_append
#print axioms SmcTuring.Appendix.DivisionPackets.packet_span
#print axioms SmcTuring.Appendix.DivisionPackets.packet_count
#print axioms SmcTuring.Appendix.DivisionPackets.inactive_count
#print axioms SmcTuring.Appendix.DivisionPackets.inactive_span
#print axioms SmcTuring.Appendix.DivisionPacking.size_cons
#print axioms SmcTuring.Appendix.DivisionPacking.size_append
#print axioms SmcTuring.Appendix.DivisionPacking.place_append
#print axioms SmcTuring.Appendix.DivisionPacking.placed_lower
#print axioms SmcTuring.Appendix.DivisionPacking.placed_upper
#print axioms SmcTuring.Appendix.DivisionPacking.placed_separated
#print axioms SmcTuring.Appendix.DivisionPacking.initial_intact
#print axioms SmcTuring.Appendix.DivisionPacking.initial_fetch
#print axioms SmcTuring.Appendix.DivisionPacking.fields_append
#print axioms SmcTuring.Appendix.DivisionPacking.fields_owned
#print axioms SmcTuring.Appendix.DivisionPacking.same_owner_separate
#print axioms SmcTuring.Appendix.DivisionPacking.owned_separate
#print axioms SmcTuring.Appendix.DivisionPacking.field_layout
#print axioms SmcTuring.Appendix.DivisionPacking.placed_field_layout
#print axioms SmcTuring.Appendix.DivisionPacking.image_frame
#print axioms SmcTuring.Appendix.DivisionRegions.member
#print axioms SmcTuring.Appendix.DivisionRegions.entry_bounds
#print axioms SmcTuring.Appendix.DivisionRegions.separated_append
#print axioms SmcTuring.Appendix.DivisionRegions.capacity
#print axioms SmcTuring.Appendix.DivisionRegions.field_layout
#print axioms SmcTuring.Appendix.DivisionRegions.initial_intact
#print axioms SmcTuring.Appendix.DivisionRegions.image_append
#print axioms SmcTuring.Appendix.DivisionRegions.image_frame
#print axioms SmcTuring.Appendix.DivisionRegions.outside_owned
#print axioms SmcTuring.Appendix.DivisionLinear.span_cons
#print axioms SmcTuring.Appendix.DivisionLinear.minimum_length
#print axioms SmcTuring.Appendix.DivisionLinear.execute_pc
#print axioms SmcTuring.Appendix.DivisionLinear.constructed_trace
#print axioms SmcTuring.Appendix.DivisionLinear.image_trace
#print axioms SmcTuring.Appendix.DivisionLinear.run_pc
#print axioms SmcTuring.Appendix.DivisionLinear.owned_run
#print axioms SmcTuring.Appendix.DivisionLinear.run_intact
#print axioms SmcTuring.Appendix.DivisionLinear.run_common
#print axioms SmcTuring.Appendix.DivisionLayout.data_initial
#print axioms SmcTuring.Appendix.DivisionLayout.data_initials
#print axioms SmcTuring.Appendix.DivisionLayout.tail_initials
#print axioms SmcTuring.Appendix.DivisionLayout.restore_initials
#print axioms SmcTuring.Appendix.DivisionLayout.pure_initials
#print axioms SmcTuring.Appendix.DivisionLayout.pure_size
#print axioms SmcTuring.Appendix.DivisionLayout.data_size
#print axioms SmcTuring.Appendix.DivisionLayout.tail_size
#print axioms SmcTuring.Appendix.DivisionLayout.restore_size
#print axioms SmcTuring.Appendix.DivisionLayout.data_fields
#print axioms SmcTuring.Appendix.DivisionLayout.tail_fields
#print axioms SmcTuring.Appendix.DivisionLayout.restore_fields
#print axioms SmcTuring.Appendix.DivisionLayout.ordered
#print axioms SmcTuring.Appendix.DivisionLayout.capacity
#print axioms SmcTuring.Appendix.DivisionLayout.separated
#print axioms SmcTuring.Appendix.DivisionLayout.field_layout
#print axioms SmcTuring.Appendix.DivisionLayout.initial_intact
#print axioms SmcTuring.Appendix.DivisionLayout.initial_fetch
#print axioms SmcTuring.Appendix.DivisionLayout.pure_fields
#print axioms SmcTuring.Appendix.DivisionLayout.image_fields
#print axioms SmcTuring.Appendix.DivisionLayout.slot_owned
#print axioms SmcTuring.Appendix.DivisionLayout.pointer_owned
#print axioms SmcTuring.Appendix.DivisionLayout.address_owned
#print axioms SmcTuring.Appendix.DivisionLayout.slot_fits
#print axioms SmcTuring.Appendix.DivisionLayout.owned_patch_intact
#print axioms SmcTuring.Appendix.DivisionLayout.written_active
#print axioms SmcTuring.Appendix.DivisionData.span_cons
#print axioms SmcTuring.Appendix.DivisionData.instruction_length
#print axioms SmcTuring.Appendix.DivisionData.current_translation
#print axioms SmcTuring.Appendix.DivisionData.execute_pc
#print axioms SmcTuring.Appendix.DivisionData.constructed_trace
#print axioms SmcTuring.Appendix.DivisionData.image_trace
#print axioms SmcTuring.Appendix.DivisionData.run_pc
#print axioms SmcTuring.Appendix.DivisionData.block_linked
#print axioms SmcTuring.Appendix.DivisionData.block_dependency_owned
#print axioms SmcTuring.Appendix.DivisionData.block_capacity
#print axioms SmcTuring.Appendix.DivisionData.block_placed
#print axioms SmcTuring.Appendix.DivisionData.block_code_fits
#print axioms SmcTuring.Appendix.DivisionData.block_trace
#print axioms SmcTuring.Appendix.DivisionData.block_image_trace
#print axioms SmcTuring.Appendix.DivisionData.run_intact
#print axioms SmcTuring.Appendix.DivisionData.block_intact
#print axioms SmcTuring.Appendix.DivisionData.block_refinement
#print axioms SmcTuring.Appendix.DivisionData.pure_destinations
#print axioms SmcTuring.Appendix.DivisionSetup.call_field_position
#print axioms SmcTuring.Appendix.DivisionSetup.tail_placed
#print axioms SmcTuring.Appendix.DivisionSetup.continuation_placed
#print axioms SmcTuring.Appendix.DivisionSetup.tail_fits
#print axioms SmcTuring.Appendix.DivisionSetup.continuation_fits
#print axioms SmcTuring.Appendix.DivisionSetup.pointer_fits
#print axioms SmcTuring.Appendix.DivisionSetup.address_fits
#print axioms SmcTuring.Appendix.DivisionSetup.call_fits
#print axioms SmcTuring.Appendix.DivisionSetup.slot_alias
#print axioms SmcTuring.Appendix.DivisionSetup.pointer_nonwrap
#print axioms SmcTuring.Appendix.DivisionSetup.slot_apart
#print axioms SmcTuring.Appendix.DivisionSetup.call_apart
#print axioms SmcTuring.Appendix.DivisionSetup.metadata_outside
#print axioms SmcTuring.Appendix.DivisionSetup.run_read_frame
#print axioms SmcTuring.Appendix.DivisionSetup.data_read_frame
#print axioms SmcTuring.Appendix.DivisionSetup.data_ready
#print axioms SmcTuring.Appendix.DivisionSetup.stack_placed
#print axioms SmcTuring.Appendix.DivisionSetup.initial_ready
#print axioms SmcTuring.Appendix.DivisionSetup.single_owner_placed
#print axioms SmcTuring.Appendix.DivisionSetup.initial_mov
#print axioms SmcTuring.Appendix.DivisionSetup.initial_operands
#print axioms SmcTuring.Appendix.DivisionSetup.call_placed
#print axioms SmcTuring.Appendix.DivisionSetup.call_entry_initial
#print axioms SmcTuring.Appendix.DivisionSetup.initial_call
#print axioms SmcTuring.Appendix.DivisionSetup.fixed_call
#print axioms SmcTuring.Appendix.DivisionSetup.word_separate
#print axioms SmcTuring.Appendix.DivisionSetup.control_separate
#print axioms SmcTuring.Appendix.DivisionSetup.continuation_code
#print axioms SmcTuring.Appendix.DivisionPaths.tail_run
#print axioms SmcTuring.Appendix.DivisionPaths.restore_run
#print axioms SmcTuring.Appendix.DivisionPaths.forms_run
#print axioms SmcTuring.Appendix.DivisionPaths.fetched_current
#print axioms SmcTuring.Appendix.DivisionPaths.call_current
#print axioms SmcTuring.Appendix.DivisionPaths.tail_trace_intact
#print axioms SmcTuring.Appendix.DivisionPaths.tail_owned
#print axioms SmcTuring.Appendix.DivisionPaths.continuation_ownership
#print axioms SmcTuring.Appendix.DivisionPaths.continuation_straight
#print axioms SmcTuring.Appendix.DivisionPaths.continuation_span
#print axioms SmcTuring.Appendix.DivisionPaths.continuation_trace
#print axioms SmcTuring.Appendix.DivisionPaths.continuation_intact
#print axioms SmcTuring.Appendix.DivisionPaths.continued_effect
#print axioms SmcTuring.Appendix.DivisionPaths.continued_ready
#print axioms SmcTuring.Appendix.DivisionPaths.continued_intact
#print axioms SmcTuring.Appendix.DivisionPaths.tail_target_pc
#print axioms SmcTuring.Appendix.DivisionPaths.continued_trace
#print axioms SmcTuring.Appendix.DivisionPaths.continued_owned
#print axioms SmcTuring.Appendix.DivisionByteBlocks.view_agreement
#print axioms SmcTuring.Appendix.DivisionByteBlocks.forms_run
#print axioms SmcTuring.Appendix.DivisionByteBlocks.data_end_pc
#print axioms SmcTuring.Appendix.DivisionByteBlocks.guard_displacement
#print axioms SmcTuring.Appendix.DivisionByteBlocks.target
#print axioms SmcTuring.Appendix.DivisionByteBlocks.run_effect
#print axioms SmcTuring.Appendix.DivisionByteBlocks.trace
#print axioms SmcTuring.Appendix.DivisionByteBlocks.image_trace
#print axioms SmcTuring.Appendix.DivisionByteBlocks.run_intact
#print axioms SmcTuring.Appendix.DivisionByteBlocks.run_ready
#print axioms SmcTuring.Appendix.DivisionByteBlocks.owned
#print axioms SmcTuring.Appendix.DivisionByteBlocks.refinement
#print axioms SmcTuring.Appendix.DivisionByteBlocks.run_pc
#print axioms SmcTuring.Appendix.DivisionByteBlocks.field
#print axioms SmcTuring.Appendix.DivisionByteBlocks.stack
#print axioms SmcTuring.Appendix.DivisionByteSimulation.view_agreement
#print axioms SmcTuring.Appendix.DivisionByteSimulation.slot_word
#print axioms SmcTuring.Appendix.DivisionByteSimulation.source_ready
#print axioms SmcTuring.Appendix.DivisionByteSimulation.continued_pc
#print axioms SmcTuring.Appendix.DivisionByteSimulation.end_code
#print axioms SmcTuring.Appendix.DivisionByteSimulation.block_start
#print axioms SmcTuring.Appendix.DivisionByteSimulation.guard_ready
#print axioms SmcTuring.Appendix.DivisionByteSimulation.source_data_effect
#print axioms SmcTuring.Appendix.DivisionByteSimulation.source_stack_effect
#print axioms SmcTuring.Appendix.DivisionByteSimulation.advance
#print axioms SmcTuring.Appendix.DivisionByteLoop.loop_step
#print axioms SmcTuring.Appendix.DivisionByteLoop.entry_location
#print axioms SmcTuring.Appendix.DivisionByteLoop.body_boundary
#print axioms SmcTuring.Appendix.DivisionByteLoop.exit_simulate
#print axioms SmcTuring.Appendix.DivisionByteLoop.simulate
#print axioms SmcTuring.Appendix.DivisionByteCorrect.initial_context
#print axioms SmcTuring.Appendix.DivisionByteCorrect.divide_simulate
#print axioms SmcTuring.Appendix.DivisionByteCorrect.execution
#print axioms SmcTuring.Appendix.DivisionByteCorrect.owned_run_frame
#print axioms SmcTuring.Appendix.DivisionByteCorrect.trace_frame
#print axioms SmcTuring.Appendix.DivisionByteCorrect.field_cases
#print axioms SmcTuring.Appendix.DivisionByteCorrect.correct
#print axioms SmcTuring.Appendix.DivisionByteCorrect.signed_quotient
#print axioms SmcTuring.Appendix.DivisionByteCorrect.signed_remainder
#print axioms SmcTuring.Appendix.DivisionByteCorrect.unsigned_quotient
#print axioms SmcTuring.Appendix.DivisionByteCorrect.unsigned_remainder
#print axioms SmcTuring.Appendix.DivisionByteExecution.common_run

#print axioms SmcTuring.Appendix.DivisionByteCorrect.maintained_context
#print axioms SmcTuring.Appendix.DivisionByteCorrect.context_execution
#print axioms SmcTuring.Appendix.DivisionByteCorrect.context_correct
#print axioms SmcTuring.Appendix.DivisionByteCorrect.reusable_correct

#print axioms SmcTuring.Appendix.DivisionRegions.separated
#print axioms SmcTuring.Appendix.DivisionByteSimulation.block

#print axioms SmcTuring.Appendix.ByteRegions.separated_append_disjoint
#print axioms SmcTuring.Appendix.ByteRegions.separated_disjoint
#print axioms SmcTuring.Appendix.SpacedLayout.valid_checks
#print axioms SmcTuring.Appendix.SpacedLayout.ordered_valid
#print axioms SmcTuring.Appendix.SpacedLayout.regions_disjoint
#print axioms SmcTuring.Appendix.SpacedControl.prefix_disjoint_frame

-- Corrected reusable terminal marker, both selected modes.
#print axioms SmcTuring.Native.ByteMemory.put_current
#print axioms SmcTuring.Native.DwordStore.roundtrip
#print axioms SmcTuring.Native.DwordStore.length
#print axioms SmcTuring.Native.DwordStore.encode_injective
#print axioms SmcTuring.Native.DwordStore.fetch_encoding
#print axioms SmcTuring.Native.DwordStore.step_encoding
#print axioms SmcTuring.Native.DwordStore.registers
#print axioms SmcTuring.Native.DwordStore.pc
#print axioms SmcTuring.Native.DwordStore.memory
#print axioms SmcTuring.Native.DwordStore.frame
#print axioms SmcTuring.Native.DwordStore.written
#print axioms SmcTuring.Native.DwordStore.writes
#print axioms SmcTuring.Native.DwordStore.emit_address
#print axioms SmcTuring.Native.TerminalMarker.length
#print axioms SmcTuring.Native.TerminalMarker.reach
#print axioms SmcTuring.Native.TerminalMarker.displacement_x64
#print axioms SmcTuring.Native.TerminalMarker.target
#print axioms SmcTuring.Native.TerminalMarker.target_toNat
#print axioms SmcTuring.Native.TerminalMarker.current_image
#print axioms SmcTuring.Native.TerminalMarker.current_immediate
#print axioms SmcTuring.Native.TerminalMarker.memory_unchanged
#print axioms SmcTuring.Native.TerminalMarker.next_position
#print axioms SmcTuring.Native.TerminalMarker.owned_write
#print axioms SmcTuring.Native.TerminalMarker.pure
#print axioms SmcTuring.Native.TerminalMarker.correct
#print axioms SmcTuring.Native.TerminalMarker.reusable
#print axioms SmcTuring.Native.TerminalMarker.output_preserved

-- Printed full-width accumulator preservation and terminal composition.
#print axioms SmcTuring.Native.AccumulatorLayout.lengths
#print axioms SmcTuring.Native.AccumulatorLayout.save_toNat
#print axioms SmcTuring.Native.AccumulatorLayout.pointer_toNat
#print axioms SmcTuring.Native.AccumulatorLayout.save_next
#print axioms SmcTuring.Native.AccumulatorLayout.first_next
#print axioms SmcTuring.Native.AccumulatorLayout.second_next
#print axioms SmcTuring.Native.AccumulatorLayout.third_next
#print axioms SmcTuring.Native.AccumulatorLayout.save_hits
#print axioms SmcTuring.Native.AccumulatorLayout.first_hits
#print axioms SmcTuring.Native.AccumulatorLayout.second_hits
#print axioms SmcTuring.Native.AccumulatorLayout.third_hits
#print axioms SmcTuring.Native.AccumulatorLayout.save_pointer_apart
#print axioms SmcTuring.Native.AccumulatorEffects.state_ext
#print axioms SmcTuring.Native.AccumulatorEffects.save_effect
#print axioms SmcTuring.Native.AccumulatorEffects.saved_value
#print axioms SmcTuring.Native.AccumulatorEffects.saved_pointer
#print axioms SmcTuring.Native.AccumulatorEffects.swapped_pc
#print axioms SmcTuring.Native.AccumulatorEffects.restored_pc
#print axioms SmcTuring.Native.AccumulatorEffects.restored_memory
#print axioms SmcTuring.Native.AccumulatorEffects.restored_accumulator
#print axioms SmcTuring.Native.AccumulatorEffects.restored_effect
#print axioms SmcTuring.Native.AccumulatorEffects.effect
#print axioms SmcTuring.Native.AccumulatorEffects.correct
#print axioms SmcTuring.Native.AccumulatorEffects.reset_value
#print axioms SmcTuring.Native.AccumulatorEffects.pointer_value
#print axioms SmcTuring.Native.AccumulatorEffects.frame
#print axioms SmcTuring.Native.AccumulatorImage.save_address
#print axioms SmcTuring.Native.AccumulatorImage.first_address
#print axioms SmcTuring.Native.AccumulatorImage.second_address
#print axioms SmcTuring.Native.AccumulatorImage.third_address
#print axioms SmcTuring.Native.AccumulatorImage.supported_run
#print axioms SmcTuring.Native.AccumulatorImage.saved_intact
#print axioms SmcTuring.Native.AccumulatorImage.swapped_intact
#print axioms SmcTuring.Native.AccumulatorImage.restored_intact
#print axioms SmcTuring.Native.AccumulatorImage.finish_intact
#print axioms SmcTuring.Native.AccumulatorImage.fetched
#print axioms SmcTuring.Native.AccumulatorImage.save_trace
#print axioms SmcTuring.Native.AccumulatorImage.trace
#print axioms SmcTuring.Native.AccumulatorImage.owner_value
#print axioms SmcTuring.Native.AccumulatorImage.owner_owned
#print axioms SmcTuring.Native.AccumulatorImage.load_agreement
#print axioms SmcTuring.Native.AccumulatorFinalization.terminal_current
#print axioms SmcTuring.Native.AccumulatorFinalization.terminal_correct
#print axioms SmcTuring.Native.AccumulatorFinalization.memory_effect
#print axioms SmcTuring.Native.AccumulatorFinalization.output_frame
#print axioms SmcTuring.Native.AccumulatorFinalization.live_reuse
#print axioms SmcTuring.Native.AccumulatorFinalization.surround
#print axioms SmcTuring.Native.AccumulatorFinalization.surrounding_pure
#print axioms SmcTuring.Native.AccumulatorFinalization.original_prologue

-- Minimal Listing 8 input immediate-field repair.
#print axioms SmcTuring.Appendix.InputOperand.source_length
#print axioms SmcTuring.Appendix.InputOperand.target_length
#print axioms SmcTuring.Appendix.InputOperand.target_roundtrip
#print axioms SmcTuring.Appendix.InputOperand.read_payload
#print axioms SmcTuring.Appendix.InputOperand.current_source
#print axioms SmcTuring.Appendix.InputOperand.current_source_load
#print axioms SmcTuring.Appendix.InputOperand.target_patch
#print axioms SmcTuring.Appendix.InputOperand.patched_target
#print axioms SmcTuring.Appendix.InputOperand.copy_correct
#print axioms SmcTuring.Appendix.InputOperand.copy_frame
#print axioms SmcTuring.Appendix.InputOperand.copy_pure
#print axioms SmcTuring.Appendix.InputOperand.operand_windows
#print axioms SmcTuring.Appendix.InputOperand.word_effect
#print axioms SmcTuring.Appendix.InputOperand.word_symbol

#print axioms SmcTuring.Appendix.InputOperand.source_code_frame

-- Positive printed live DWORD scalar owner.
#print axioms SmcTuring.Native.DwordOwner.length
#print axioms SmcTuring.Native.DwordOwner.reach
#print axioms SmcTuring.Native.DwordOwner.displacement_x64
#print axioms SmcTuring.Native.DwordOwner.target
#print axioms SmcTuring.Native.DwordOwner.target_toNat
#print axioms SmcTuring.Native.DwordOwner.current_image
#print axioms SmcTuring.Native.DwordOwner.current_immediate
#print axioms SmcTuring.Native.DwordOwner.memory_unchanged
#print axioms SmcTuring.Native.DwordOwner.next_position
#print axioms SmcTuring.Native.DwordOwner.owned_write
#print axioms SmcTuring.Native.DwordOwner.pure
#print axioms SmcTuring.Native.DwordOwner.correct
#print axioms SmcTuring.Native.DwordOwner.reusable
#print axioms SmcTuring.Native.DwordOwner.output_preserved
#print axioms SmcTuring.Native.DwordOwner.patch_value
#print axioms SmcTuring.Native.DwordOwner.patched_current
#print axioms SmcTuring.Native.DwordOwner.initial_zero

-- Universal both-mode DWORD helper and corrected current-symbol copy.
#print axioms SmcTuring.Native.DwordCode.roundtrip
#print axioms SmcTuring.Native.DwordCode.encode_injective
#print axioms SmcTuring.Native.DwordCode.encode_length
#print axioms SmcTuring.Native.DwordCode.length_bound
#print axioms SmcTuring.Native.DwordCode.current_header
#print axioms SmcTuring.Native.DwordCode.fetch_encoding
#print axioms SmcTuring.Native.DwordCode.put_word
#print axioms SmcTuring.Native.DwordCode.put_overwrite
#print axioms SmcTuring.Native.DwordCode.put_commute
#print axioms SmcTuring.Native.DwordCode.lift_toNat
#print axioms SmcTuring.Native.DwordCode.low_lift
#print axioms SmcTuring.Native.DwordCode.lift_low_x86
#print axioms SmcTuring.Native.DwordCode.lift_low_x64_bound
#print axioms SmcTuring.Native.DwordCode.read_total
#print axioms SmcTuring.Native.DwordCode.get_put
#print axioms SmcTuring.Native.DwordCode.put_get_back
#print axioms SmcTuring.Native.DwordCode.get_frame
#print axioms SmcTuring.Native.DwordCode.step_encoding
#print axioms SmcTuring.Native.DwordCode.memory
#print axioms SmcTuring.Native.DwordCode.preserved
#print axioms SmcTuring.Native.DwordCode.frame
#print axioms SmcTuring.Native.DwordCode.write_nonempty
#print axioms SmcTuring.Native.DwordLayout.lengths
#print axioms SmcTuring.Native.DwordLayout.endpoint
#print axioms SmcTuring.Native.DwordLayout.span_sizes
#print axioms SmcTuring.Native.DwordLayout.source_toNat
#print axioms SmcTuring.Native.DwordLayout.destination_toNat
#print axioms SmcTuring.Native.DwordLayout.next_nat
#print axioms SmcTuring.Native.DwordLayout.first_next
#print axioms SmcTuring.Native.DwordLayout.second_next
#print axioms SmcTuring.Native.DwordLayout.third_next
#print axioms SmcTuring.Native.DwordLayout.first_hits
#print axioms SmcTuring.Native.DwordLayout.second_hits
#print axioms SmcTuring.Native.DwordLayout.third_hits
#print axioms SmcTuring.Native.DwordLayout.source_outside
#print axioms SmcTuring.Native.DwordLayout.destination_outside
#print axioms SmcTuring.Native.DwordLayout.reachable_iff
#print axioms SmcTuring.Native.DwordLayout.checks_valid
#print axioms SmcTuring.Native.DwordEffects.first_effect
#print axioms SmcTuring.Native.DwordEffects.second_effect
#print axioms SmcTuring.Native.DwordEffects.third_effect
#print axioms SmcTuring.Native.DwordEffects.swapped_pc
#print axioms SmcTuring.Native.DwordEffects.stored_effect
#print axioms SmcTuring.Native.DwordEffects.stored_pc
#print axioms SmcTuring.Native.DwordEffects.original_source_read
#print axioms SmcTuring.Native.DwordEffects.source_read_after_stored
#print axioms SmcTuring.Native.DwordEffects.restored_memory
#print axioms SmcTuring.Native.DwordEffects.effect
#print axioms SmcTuring.Native.DwordEffects.destination_value
#print axioms SmcTuring.Native.DwordEffects.source_value
#print axioms SmcTuring.Native.DwordEffects.frame
#print axioms SmcTuring.Native.DwordEffects.registers
#print axioms SmcTuring.Native.DwordEffects.x86_accumulator
#print axioms SmcTuring.Native.DwordEffects.x64_zero_extension
#print axioms SmcTuring.Native.DwordImage.byte_bindings
#print axioms SmcTuring.Native.DwordImage.placed_entries
#print axioms SmcTuring.Native.DwordImage.size_span
#print axioms SmcTuring.Native.DwordImage.separated
#print axioms SmcTuring.Native.DwordImage.initial_intact
#print axioms SmcTuring.Native.DwordImage.packet_bounds
#print axioms SmcTuring.Native.DwordImage.intact_put
#print axioms SmcTuring.Native.DwordImage.swapped_intact
#print axioms SmcTuring.Native.DwordImage.stored_intact
#print axioms SmcTuring.Native.DwordImage.finish_intact
#print axioms SmcTuring.Native.DwordImage.first_fetch
#print axioms SmcTuring.Native.DwordImage.second_fetch
#print axioms SmcTuring.Native.DwordImage.third_fetch
#print axioms SmcTuring.Native.DwordImage.trace
#print axioms SmcTuring.Native.DwordImage.supported_run
#print axioms SmcTuring.Native.DwordImage.correct
#print axioms SmcTuring.Native.DwordImage.original_correct
#print axioms SmcTuring.Native.DwordImage.image_frame
#print axioms SmcTuring.Native.DwordImage.initial_field
#print axioms SmcTuring.Appendix.InputDword.current_source_word
#print axioms SmcTuring.Appendix.InputDword.copy_correct
#print axioms SmcTuring.Appendix.InputDword.copy_pure
#print axioms SmcTuring.Appendix.InputDword.source_code_frame
#print axioms SmcTuring.Native.DwordArithmetic.two_words
#print axioms SmcTuring.Native.DwordArithmetic.roundtrip
#print axioms SmcTuring.Native.DwordArithmetic.encode_injective
#print axioms SmcTuring.Native.DwordArithmetic.encode_length
#print axioms SmcTuring.Native.DwordArithmetic.header_size
#print axioms SmcTuring.Native.DwordArithmetic.fetch_encoding
#print axioms SmcTuring.Native.DwordArithmetic.step_encoding
#print axioms SmcTuring.Native.DwordArithmetic.registers
#print axioms SmcTuring.Native.DwordArithmetic.written
#print axioms SmcTuring.Native.DwordArithmetic.frame
#print axioms SmcTuring.Native.DwordArithmetic.payload_patch
#print axioms SmcTuring.Native.DwordArithmetic.base_xor_patch
#print axioms SmcTuring.Native.DwordArithmetic.relocate_length
#print axioms SmcTuring.Native.DwordArithmetic.relocate_result
#print axioms SmcTuring.Native.DwordArithmetic.relocate_flag
#print axioms SmcTuring.Native.DwordArithmetic.located_next
#print axioms SmcTuring.Native.DwordArithmetic.located_address
#print axioms SmcTuring.Native.DwordArithmetic.located_effect
#print axioms SmcTuring.Native.DwordArithmetic.write_nonempty
#print axioms SmcTuring.Appendix.DwordComparison.length
#print axioms SmcTuring.Appendix.DwordComparison.initially_intact
#print axioms SmcTuring.Appendix.DwordComparison.packet_window
#print axioms SmcTuring.Appendix.DwordComparison.current_packet
#print axioms SmcTuring.Appendix.DwordComparison.intact_put
#print axioms SmcTuring.Appendix.DwordComparison.scalar_apart
#print axioms SmcTuring.Appendix.DwordComparison.mask_apart
#print axioms SmcTuring.Appendix.DwordComparison.located_effect
#print axioms SmcTuring.Appendix.DwordComparison.reset_effect
#print axioms SmcTuring.Appendix.DwordComparison.subtracted_effect
#print axioms SmcTuring.Appendix.DwordComparison.negated_effect
#print axioms SmcTuring.Appendix.DwordComparison.borrowed_effect
#print axioms SmcTuring.Appendix.DwordComparison.finish_effect
#print axioms SmcTuring.Appendix.DwordComparison.intermediate_intact
#print axioms SmcTuring.Appendix.DwordComparison.trace
#print axioms SmcTuring.Appendix.DwordComparison.difference_zero
#print axioms SmcTuring.Appendix.DwordComparison.mask_value
#print axioms SmcTuring.Appendix.DwordComparison.memory_effect
#print axioms SmcTuring.Appendix.DwordComparison.frame
#print axioms SmcTuring.Appendix.DwordComparison.owned_destinations
#print axioms SmcTuring.Appendix.DwordComparison.correct
#print axioms SmcTuring.Appendix.DwordComparison.original_correct
#print axioms SmcTuring.Appendix.DwordComparison.pure
#print axioms SmcTuring.Appendix.DwordComparison.checks_valid
#print axioms SmcTuring.Appendix.InputSelection.chosen_difference
#print axioms SmcTuring.Appendix.InputSelection.selected_symbol
#print axioms SmcTuring.Appendix.InputSelection.current_patch
#print axioms SmcTuring.Appendix.InputSelection.xor_then_and
#print axioms SmcTuring.Appendix.InputSelection.tape_target
#print axioms SmcTuring.Appendix.InputSelection.tape_effect
#print axioms SmcTuring.Appendix.InputSelection.tape_step
#print axioms SmcTuring.Appendix.InputSelection.tape_code_frame
#print axioms SmcTuring.Appendix.InputSelection.tape_owned_write
#print axioms SmcTuring.Appendix.InputSelection.comparison_selection

#print axioms SmcTuring.Native.MixedDword.encode_length
#print axioms SmcTuring.Native.MixedDword.arithmetic_fetch
#print axioms SmcTuring.Native.MixedDword.arithmetic_encoding
#print axioms SmcTuring.Native.MixedDword.copy_encoding
#print axioms SmcTuring.Native.MixedDword.wide_encoding
#print axioms SmcTuring.Native.MixedDword.current_encoding
#print axioms SmcTuring.Native.MixedDword.step_encoding
#print axioms SmcTuring.Native.MixedDword.arithmetic_trace
#print axioms SmcTuring.Native.MixedDword.trace_append
#print axioms SmcTuring.Native.MixedDword.exchange_bytes
#print axioms SmcTuring.Native.MixedDword.exchange_length
#print axioms SmcTuring.Native.MixedDword.exchange_execution
#print axioms SmcTuring.Native.MixedDword.exchange_address
#print axioms SmcTuring.Native.MixedDword.exchange_width
#print axioms SmcTuring.Native.MixedDword.write_nonempty
#print axioms SmcTuring.Native.MixedDword.frame
#print axioms SmcTuring.Native.MixedMemory.read_total
#print axioms SmcTuring.Native.MixedMemory.get_put
#print axioms SmcTuring.Native.MixedMemory.put_get_back
#print axioms SmcTuring.Native.MixedMemory.load_nat
#print axioms SmcTuring.Native.MixedMemory.wide_after_dword
#print axioms SmcTuring.Native.MixedMemory.dword_after_wide
#print axioms SmcTuring.Native.MixedMemory.stores_commute
#print axioms SmcTuring.Native.MixedMemory.wide_frame
#print axioms SmcTuring.Native.ByteWindow.drop
#print axioms SmcTuring.Native.ByteWindow.packet
#print axioms SmcTuring.Appendix.CursorLayout.exchange_sizes
#print axioms SmcTuring.Appendix.CursorLayout.lengths
#print axioms SmcTuring.Appendix.CursorLayout.endpoint
#print axioms SmcTuring.Appendix.CursorLayout.spans
#print axioms SmcTuring.Appendix.CursorLayout.cursor_toNat
#print axioms SmcTuring.Appendix.CursorLayout.head_toNat
#print axioms SmcTuring.Appendix.CursorLayout.first_next
#print axioms SmcTuring.Appendix.CursorLayout.last_next
#print axioms SmcTuring.Appendix.CursorLayout.first_hits
#print axioms SmcTuring.Appendix.CursorLayout.last_hits
#print axioms SmcTuring.Appendix.CursorLayout.cursor_apart
#print axioms SmcTuring.Appendix.CursorLayout.tape_apart
#print axioms SmcTuring.Appendix.CursorEffects.selection
#print axioms SmcTuring.Appendix.CursorEffects.selection_rule
#print axioms SmcTuring.Appendix.CursorEffects.swapped_effect
#print axioms SmcTuring.Appendix.CursorEffects.swapped_pc
#print axioms SmcTuring.Appendix.CursorEffects.updated_effect
#print axioms SmcTuring.Appendix.CursorEffects.updated_pc
#print axioms SmcTuring.Appendix.CursorEffects.cursor_after_update
#print axioms SmcTuring.Appendix.CursorEffects.finish_effect
#print axioms SmcTuring.Appendix.CursorEffects.selected_effect
#print axioms SmcTuring.Appendix.CursorEffects.selected_effect_rule
#print axioms SmcTuring.Appendix.CursorEffects.restored_cursor
#print axioms SmcTuring.Appendix.CursorEffects.frame
#print axioms SmcTuring.Appendix.CursorImage.length
#print axioms SmcTuring.Appendix.CursorImage.initial_intact
#print axioms SmcTuring.Appendix.CursorImage.first_current
#print axioms SmcTuring.Appendix.CursorImage.middle_current
#print axioms SmcTuring.Appendix.CursorImage.last_current
#print axioms SmcTuring.Appendix.CursorImage.intact_wide
#print axioms SmcTuring.Appendix.CursorImage.intact_dword
#print axioms SmcTuring.Appendix.CursorImage.swapped_intact
#print axioms SmcTuring.Appendix.CursorImage.updated_intact
#print axioms SmcTuring.Appendix.CursorImage.finish_intact
#print axioms SmcTuring.Appendix.CursorImage.trace
#print axioms SmcTuring.Appendix.CursorImage.original_trace
#print axioms SmcTuring.Appendix.CursorImage.correct
#print axioms SmcTuring.Appendix.CursorImage.pure

#print axioms SmcTuring.Appendix.CursorLayout.checks_valid

#print axioms SmcTuring.Native.BytePatch.put_append
#print axioms SmcTuring.Native.BytePatch.middle
#print axioms SmcTuring.Native.BytePatch.current
#print axioms SmcTuring.Appendix.CursorPatch.spelling
#print axioms SmcTuring.Appendix.CursorPatch.leading_length
#print axioms SmcTuring.Appendix.CursorPatch.current
#print axioms SmcTuring.Appendix.CursorPatch.operand
#print axioms SmcTuring.Appendix.InputUpdate.prefix_lengths
#print axioms SmcTuring.Appendix.InputUpdate.length
#print axioms SmcTuring.Appendix.InputUpdate.positions
#print axioms SmcTuring.Appendix.InputUpdate.endpoint
#print axioms SmcTuring.Appendix.InputUpdate.field_bounds
#print axioms SmcTuring.Appendix.InputUpdate.field_fits
#print axioms SmcTuring.Appendix.InputUpdate.xor_range
#print axioms SmcTuring.Appendix.InputUpdate.and_range
#print axioms SmcTuring.Appendix.InputUpdate.initial_intact
#print axioms SmcTuring.Appendix.InputUpdate.body_current
#print axioms SmcTuring.Appendix.InputUpdate.operand
#print axioms SmcTuring.Appendix.InputUpdate.patch
#print axioms SmcTuring.Appendix.InputUpdate.xored_effect
#print axioms SmcTuring.Appendix.InputUpdate.xored_intact
#print axioms SmcTuring.Appendix.InputUpdate.masked_effect
#print axioms SmcTuring.Appendix.InputUpdate.masked_intact
#print axioms SmcTuring.Appendix.InputUpdate.intact_external
#print axioms SmcTuring.Appendix.InputUpdate.checks_valid
#print axioms SmcTuring.Appendix.InputUpdateTrace.first_current
#print axioms SmcTuring.Appendix.InputUpdateTrace.second_current
#print axioms SmcTuring.Appendix.InputUpdateTrace.prefix_trace
#print axioms SmcTuring.Appendix.InputUpdateTrace.cursor_frame
#print axioms SmcTuring.Appendix.InputUpdateTrace.tape_frame
#print axioms SmcTuring.Appendix.InputUpdateTrace.masked_cursor
#print axioms SmcTuring.Appendix.InputUpdateTrace.masked_tape
#print axioms SmcTuring.Appendix.InputUpdateTrace.masked_tape_rule
#print axioms SmcTuring.Appendix.InputUpdateTrace.trace
#print axioms SmcTuring.Appendix.InputUpdateTrace.effect
#print axioms SmcTuring.Appendix.InputUpdateTrace.effect_rule
#print axioms SmcTuring.Appendix.InputUpdateTrace.exterior
#print axioms SmcTuring.Appendix.InputUpdateTrace.exterior_rule
#print axioms SmcTuring.Appendix.InputUpdateTrace.pure
#print axioms SmcTuring.Appendix.InputUpdateTrace.original_correct
#print axioms SmcTuring.Appendix.InputUpdateTrace.original_correct_rule
#print axioms SmcTuring.Appendix.InputUpdateTrace.retained_image
#print axioms SmcTuring.Appendix.InputUpdateTrace.retained_image_rule

#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_fields
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_and_mask_fields
#print axioms SmcTuring.Appendix.Listing8InputPrefix.stage_boundaries
#print axioms SmcTuring.Appendix.Listing8InputPrefix.positions
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_admissible
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_bytes_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.prefix_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.bytes_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.initial_intact
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_binding
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_block_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.source_value
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_first_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_second_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_third_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_intact
#print axioms SmcTuring.Appendix.Listing8InputPrefix.start_fits
#print axioms SmcTuring.Appendix.Listing8InputPrefix.mask_fits
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_effect
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_intact
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_trace
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_step
#print axioms SmcTuring.Appendix.Listing8InputPrefix.copy_trace
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_trace
#print axioms SmcTuring.Appendix.Listing8InputPrefix.source_after_reset
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_effect
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_exact
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_source_restored
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_word_frame
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_current_after_copy
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_value_after_copy
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.scalar_fits
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_effect_after_copy
#print axioms SmcTuring.Appendix.Listing8InputPrefix.owner_trace_after_copy
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_owner_trace
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_word_frame
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_current_after_owner
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_trace_after_owner
#print axioms SmcTuring.Appendix.Listing8InputPrefix.reset_copy_owner_sub_trace
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sub_effect_after_owner
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.packet_word_frame
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_current_after_sub
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_effect_after_sub
#print axioms SmcTuring.Appendix.Listing8InputPrefix.neg_trace_after_sub
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_current_after_neg
#print axioms SmcTuring.Appendix.Listing8InputPrefix.word_get_frame
#print axioms SmcTuring.Appendix.Listing8InputPrefix.mask_get_after_neg
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_effect_after_neg
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_trace_after_neg
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_length
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_current
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_current_after_sbb
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_mask
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_mask_prop
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_carry_prop
#print axioms SmcTuring.Appendix.Listing8InputPrefix.mask_get_after_sbb
#print axioms SmcTuring.Appendix.Listing8InputPrefix.sbb_carry_after_neg
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_range
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_effect_after_sbb
#print axioms SmcTuring.Appendix.Listing8InputPrefix.not_trace_after_sbb
#print axioms SmcTuring.Appendix.Listing8InputPrefix.prefix_trace

#print axioms SmcTuring.Appendix.Listing8InputComposition.initial_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.update_mask_spelling
#print axioms SmcTuring.Appendix.Listing8InputComposition.update_mask_patch
#print axioms SmcTuring.Appendix.Listing8InputComposition.scalar_before_update
#print axioms SmcTuring.Appendix.Listing8InputComposition.scalar_update_frame
#print axioms SmcTuring.Appendix.Listing8InputComposition.reset_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.copied_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.owner_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.sub_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.neg_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.mask_eq
#print axioms SmcTuring.Appendix.Listing8InputComposition.sbb_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_update_intact
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_pc
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_pending
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_mask
#print axioms SmcTuring.Appendix.Listing8InputComposition.chosen_iff
#print axioms SmcTuring.Appendix.Listing8InputComposition.chosen_matches_tape
#print axioms SmcTuring.Appendix.Listing8InputComposition.code_field_bounds
#print axioms SmcTuring.Appendix.Listing8InputComposition.cursor_field_frame
#print axioms SmcTuring.Appendix.Listing8InputComposition.tape_field_frame
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_memory
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_cursor
#print axioms SmcTuring.Appendix.Listing8InputComposition.prefix_tape
#print axioms SmcTuring.Appendix.Listing8InputComposition.full_input_trace
#print axioms SmcTuring.Appendix.Listing8InputComposition.full_input_effect
#print axioms SmcTuring.Appendix.Listing8InputComposition.full_input_retained
#print axioms SmcTuring.Appendix.Listing8InputComposition.full_input_tape

#print axioms SmcTuring.Appendix.Listing8MaskCopy.printed_source_counterexample
#print axioms SmcTuring.Appendix.Listing8MaskCopy.printed_source_is_not_zero_mask
#print axioms SmcTuring.Appendix.Listing8MaskCopy.printed_source_is_not_true_mask
#print axioms SmcTuring.Appendix.Listing8MaskCopy.mask_operand
#print axioms SmcTuring.Appendix.Listing8MaskCopy.repeated_mask
#print axioms SmcTuring.Appendix.Listing8MaskCopy.copy_mask_correct
#print axioms SmcTuring.Appendix.Listing8MaskCopy.trace_append
#print axioms SmcTuring.Appendix.Listing8MaskCopy.second_entry
#print axioms SmcTuring.Appendix.Listing8MaskCopy.second_intact
#print axioms SmcTuring.Appendix.Listing8MaskCopy.effect
#print axioms SmcTuring.Appendix.Listing8MaskCopy.trace
#print axioms SmcTuring.Appendix.Listing8MaskCopy.broadcast_correct
#print axioms SmcTuring.Appendix.Listing8MaskCopy.copy_length
#print axioms SmcTuring.Appendix.Listing8MaskCopy.distribution_length
#print axioms SmcTuring.Appendix.Listing8MaskCopy.literal_input_offsets
#print axioms SmcTuring.Appendix.Listing8MaskCopy.instruction_start_not_mask

#print axioms SmcTuring.Appendix.DwordComparisonTail.length
#print axioms SmcTuring.Appendix.DwordComparisonTail.current_packet
#print axioms SmcTuring.Appendix.DwordComparisonTail.intact_put
#print axioms SmcTuring.Appendix.DwordComparisonTail.located_effect
#print axioms SmcTuring.Appendix.DwordComparisonTail.intact_execute
#print axioms SmcTuring.Appendix.DwordComparisonTail.sub_pc
#print axioms SmcTuring.Appendix.DwordComparisonTail.neg_pc
#print axioms SmcTuring.Appendix.DwordComparisonTail.sbb_pc
#print axioms SmcTuring.Appendix.DwordComparisonTail.finish_pc
#print axioms SmcTuring.Appendix.DwordComparisonTail.sub_intact
#print axioms SmcTuring.Appendix.DwordComparisonTail.neg_intact
#print axioms SmcTuring.Appendix.DwordComparisonTail.sbb_intact
#print axioms SmcTuring.Appendix.DwordComparisonTail.finish_intact
#print axioms SmcTuring.Appendix.DwordComparisonTail.fetched
#print axioms SmcTuring.Appendix.DwordComparisonTail.trace
#print axioms SmcTuring.Appendix.DwordComparisonTail.sub_effect
#print axioms SmcTuring.Appendix.DwordComparisonTail.neg_effect
#print axioms SmcTuring.Appendix.DwordComparisonTail.mask_apart
#print axioms SmcTuring.Appendix.DwordComparisonTail.mask_after_neg
#print axioms SmcTuring.Appendix.DwordComparisonTail.sbb_result
#print axioms SmcTuring.Appendix.DwordComparisonTail.sbb_flag
#print axioms SmcTuring.Appendix.DwordComparisonTail.sbb_effect
#print axioms SmcTuring.Appendix.DwordComparisonTail.mask_after_sbb
#print axioms SmcTuring.Appendix.DwordComparisonTail.effect
#print axioms SmcTuring.Appendix.DwordComparisonTail.correct

#print axioms SmcTuring.Native.DwordMixedImage.fetched
#print axioms SmcTuring.Native.DwordMixedImage.trace
#print axioms SmcTuring.Native.DwordMixedImage.bytes_length
#print axioms SmcTuring.Native.DwordMixedImage.intact_of_bytes
#print axioms SmcTuring.Native.DwordMixedImage.bytes_frame

#print axioms SmcTuring.Native.DwordMixedSequence.trace
#print axioms SmcTuring.Native.DwordMixedSequence.endpoint
#print axioms SmcTuring.Native.DwordMixedSequence.memory_effect
#print axioms SmcTuring.Native.DwordMixedSequence.intact_of_bytes
#print axioms SmcTuring.Native.DwordMixedSequence.putFields_window
#print axioms SmcTuring.Native.DwordMixedSequence.putFields_preserves
#print axioms SmcTuring.Native.DwordMixedSequence.putFields_value
#print axioms SmcTuring.Native.DwordMixedSequence.registers

#print axioms SmcTuring.Appendix.Listing8LiteralInput.positions
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_length
#print axioms SmcTuring.Appendix.Listing8LiteralInput.distribution_length
#print axioms SmcTuring.Appendix.Listing8LiteralInput.bytes_length
#print axioms SmcTuring.Appendix.Listing8LiteralInput.initial_intact
#print axioms SmcTuring.Appendix.Listing8LiteralInput.copy_admissible
#print axioms SmcTuring.Appendix.Listing8LiteralInput.tail_valid
#print axioms SmcTuring.Appendix.Listing8LiteralInput.reset_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.copy_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.tail_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.distribution_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.update_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.field_geometry
#print axioms SmcTuring.Appendix.Listing8LiteralInput.reset_effect
#print axioms SmcTuring.Appendix.Listing8LiteralInput.source_value
#print axioms SmcTuring.Appendix.Listing8LiteralInput.copied_effect
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_after_copy
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_effect
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_scalar
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_mask
#print axioms SmcTuring.Appendix.Listing8LiteralInput.owner_tail
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_trace
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_effect
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_distribution_current
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_update_intact
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_pc
#print axioms SmcTuring.Appendix.Listing8LiteralInput.prefix_mask

#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.helper_bounds
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.copies_valid
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.chain
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.code_frames
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.initial_helpers
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.trace
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.endpoint
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.memory_effect
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.fields_separate
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.destinations
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.x86_masks
#print axioms SmcTuring.Appendix.Listing8LiteralMaskTrace.x64_masks

#print axioms SmcTuring.Appendix.Listing8LiteralComposition.field_bounds
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.cursor_field_frame
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.tape_field_frame
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.prefix_cursor
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.prefix_tape
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.distribution_memory
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.distribution_cursor
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.distribution_tape
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.distribution_update_intact
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.distribution_pc
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.trace
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.instruction_count
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.effect
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.retained
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.restored_mask_source
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.destination_values
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.tape_value
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.region_size
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.registers
#print axioms SmcTuring.Appendix.Listing8LiteralComposition.original_correct

#print axioms SmcTuring.Appendix.Listing8Prototypes.pointer_length
#print axioms SmcTuring.Appendix.Listing8Prototypes.pointer_shape
#print axioms SmcTuring.Appendix.Listing8Prototypes.pointer_prefix_length
#print axioms SmcTuring.Appendix.Listing8Prototypes.pointer_value
#print axioms SmcTuring.Appendix.Listing8Prototypes.pointer_label_is_not_entry
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_length
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_sizes
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_symbol_current
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_back_current
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_forward_current
#print axioms SmcTuring.Appendix.Listing8Prototypes.node_values
#print axioms SmcTuring.Appendix.Listing8Prototypes.transition_length
#print axioms SmcTuring.Appendix.Listing8Prototypes.transition_sizes
#print axioms SmcTuring.Appendix.Listing8Prototypes.transition_values

#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.initial_payload
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.initial_macro
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.ready
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.original_copy
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.node_copy
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.transition_copy
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.short_node_frame
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.short_node_zero_counterexample
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.operand_destination_counterexample
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.end_labels

#print axioms SmcTuring.Appendix.Listing8SourceEffects.effect
#print axioms SmcTuring.Appendix.Listing8SourceEffects.retained
#print axioms SmcTuring.Appendix.Listing8SourceEffects.destination_values
#print axioms SmcTuring.Appendix.Listing8SourceEffects.tape_value
#print axioms SmcTuring.Appendix.Listing8SourceEffects.registers
#print axioms SmcTuring.Appendix.Listing8SourceEffects.original_correct

#print axioms SmcTuring.Native.DwordRetarget.owner_bytes
#print axioms SmcTuring.Native.DwordRetarget.printed_displacement
#print axioms SmcTuring.Native.DwordRetarget.displacement_patch
#print axioms SmcTuring.Native.DwordRetarget.patch_effect
#print axioms SmcTuring.Native.DwordRetarget.patched_current
#print axioms SmcTuring.Native.DwordRetarget.patch_trace
#print axioms SmcTuring.Native.DwordRetarget.owner_effect
#print axioms SmcTuring.Native.DwordRetarget.owner_trace

#print axioms SmcTuring.Native.DwordRetargetSequence.bytes_length
#print axioms SmcTuring.Native.DwordRetargetSequence.bytes_frame
#print axioms SmcTuring.Native.DwordRetargetSequence.intact_of_bytes
#print axioms SmcTuring.Native.DwordRetargetSequence.trace
#print axioms SmcTuring.Native.DwordRetargetSequence.effect
#print axioms SmcTuring.Native.DwordRetargetSequence.writes_window
#print axioms SmcTuring.Native.DwordRetargetSequence.owner_current
#print axioms SmcTuring.Native.DwordRetargetSequence.owned_run

#print axioms SmcTuring.Appendix.Listing8ModeOffsets.geometry
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.sites_length
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.chain
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.distinct
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.owners_after_patches
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.outside
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.owners_separate
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.patch_ranges
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.valid
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.bytes_length
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.initial_image
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.initial_patches
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.trace
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.effect
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.copied_node
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.copied_transition
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.source_owners
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.retargeted_owners
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.tape_owner_trace
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.tape_owner_effect
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.tape_operand
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.tape_owner_registers
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.original_correct
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.tape_block_frame
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.remaining_owners
#print axioms SmcTuring.Appendix.Listing8ModeOffsets.patch_owned

#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.source_node_copy
#print axioms SmcTuring.Appendix.Listing8PrototypeCopy.source_transition_copy

#print axioms SmcTuring.Native.StringDword.string_fetch
#print axioms SmcTuring.Native.StringDword.string_trace
#print axioms SmcTuring.Native.StringDword.trace_append
#print axioms SmcTuring.Native.StringDword.store_encoding
#print axioms SmcTuring.Native.StringDword.store_execute
#print axioms SmcTuring.Native.StringDword.store_trace
#print axioms SmcTuring.Native.StringRetarget.execution
#print axioms SmcTuring.Native.StringRetarget.trace
#print axioms SmcTuring.Appendix.Listing8InputMask.zero_bytes
#print axioms SmcTuring.Appendix.Listing8InputMask.mask_position
#print axioms SmcTuring.Appendix.Listing8InputMask.bytes_length
#print axioms SmcTuring.Appendix.Listing8InputMask.initial_intact
#print axioms SmcTuring.Appendix.Listing8InputMask.zero_intact
#print axioms SmcTuring.Appendix.Listing8InputMask.reset_same
#print axioms SmcTuring.Appendix.Listing8InputMask.finish_same
#print axioms SmcTuring.Appendix.Listing8InputMask.reset_current
#print axioms SmcTuring.Appendix.Listing8InputMask.replace_head
#print axioms SmcTuring.Appendix.Listing8InputMask.trace
#print axioms SmcTuring.Appendix.Listing8InputMask.tape_value
#print axioms SmcTuring.Appendix.Listing8InputMask.retained
#print axioms SmcTuring.Appendix.Listing8InputFields.tape_spelling
#print axioms SmcTuring.Appendix.Listing8InputFields.tape_position
#print axioms SmcTuring.Appendix.Listing8InputFields.tape_patch
#print axioms SmcTuring.Appendix.Listing8CopyImage.endpoint_lower
#print axioms SmcTuring.Appendix.Listing8CopyImage.coordinates
#print axioms SmcTuring.Appendix.Listing8CopyImage.code_length
#print axioms SmcTuring.Appendix.Listing8CopyImage.code_to_input
#print axioms SmcTuring.Appendix.Listing8CopyImage.byte_frame
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_code
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_source_node
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_source_transition
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_node_macro
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_transition_macro
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_patches
#print axioms SmcTuring.Appendix.Listing8CopyImage.destinations
#print axioms SmcTuring.Appendix.Listing8CopyImage.block_capacity
#print axioms SmcTuring.Appendix.Listing8CopyImage.initial_input
#print axioms SmcTuring.Appendix.Listing8CopyImage.cursor_end
#print axioms SmcTuring.Appendix.Listing8CopyTrace.first_ready
#print axioms SmcTuring.Appendix.Listing8CopyTrace.first_source
#print axioms SmcTuring.Appendix.Listing8CopyTrace.first_effect
#print axioms SmcTuring.Appendix.Listing8CopyTrace.second_macro
#print axioms SmcTuring.Appendix.Listing8CopyTrace.second_ready
#print axioms SmcTuring.Appendix.Listing8CopyTrace.second_source
#print axioms SmcTuring.Appendix.Listing8CopyTrace.second_effect
#print axioms SmcTuring.Appendix.Listing8CopyTrace.copies_trace
#print axioms SmcTuring.Appendix.Listing8CopyTrace.copied_node
#print axioms SmcTuring.Appendix.Listing8CopyTrace.copied_transition
#print axioms SmcTuring.Appendix.Listing8CopyTrace.retained_patches
#print axioms SmcTuring.Appendix.Listing8CopyTrace.copied_block
#print axioms SmcTuring.Appendix.Listing8CopyTrace.patch_entry
#print axioms SmcTuring.Appendix.Listing8CopyTrace.patches_and_tape_trace
#print axioms SmcTuring.Appendix.Listing8CopyTrace.input_retained
#print axioms SmcTuring.Appendix.Listing8CopyTrace.indices
#print axioms SmcTuring.Appendix.Listing8CopyTrace.cursor_retained
#print axioms SmcTuring.Appendix.Listing8CopyTrace.source_node_retained
#print axioms SmcTuring.Appendix.Listing8CopyTrace.tape_source_value
#print axioms SmcTuring.Appendix.Listing8Initializer.patch_trace
#print axioms SmcTuring.Appendix.Listing8Initializer.patched_tape
#print axioms SmcTuring.Appendix.Listing8Initializer.patched_pc
#print axioms SmcTuring.Appendix.Listing8Initializer.last_trace
#print axioms SmcTuring.Appendix.Listing8Initializer.trace
#print axioms SmcTuring.Appendix.Listing8Initializer.principal_effect
#print axioms SmcTuring.Appendix.Listing8Initializer.tape_operand
#print axioms SmcTuring.Appendix.Listing8Initializer.instruction_count
#print axioms SmcTuring.Appendix.Listing8Initializer.code_geometry
#print axioms SmcTuring.Appendix.Listing8Initializer.input_after_patches
#print axioms SmcTuring.Appendix.Listing8Initializer.input_after_tape
#print axioms SmcTuring.Appendix.Listing8CursorFields.field_is_operand
#print axioms SmcTuring.Appendix.Listing8CursorFields.printed_x86_is_header
#print axioms SmcTuring.Appendix.Listing8CursorFields.x86_bare_label_counterexample
#print axioms SmcTuring.Appendix.Listing8CursorFields.x64_immediate_offset_counterexample
#print axioms SmcTuring.Appendix.Listing8CursorFields.source_cursor
#print axioms SmcTuring.Appendix.Listing8PointerTargets.slots
#print axioms SmcTuring.Appendix.Listing8PointerTargets.opcode_copy_counterexample
#print axioms SmcTuring.Appendix.Listing8PointerTargets.immediate_patch
#print axioms SmcTuring.Appendix.Listing8PointerTargets.pointer_half_effect
#print axioms SmcTuring.Appendix.Listing8PointerTargets.half_selected
#print axioms SmcTuring.Native.ByteWindow.append
#print axioms SmcTuring.Native.ByteWindow.join

#print axioms SmcTuring.Appendix.Listing8CopiedPointer.x64_relocates
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.encoding
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.self_value
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.first_hits
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.second_hits
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.swapped_pc
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.restored_pc
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.dereferenced_pc
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.reader_pc
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.run_reader
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.effect
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.trace
#print axioms SmcTuring.Appendix.Listing8CopiedPointer.unified_trace
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.scalar_effect
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.pointer_effect
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.advance_pc
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.advance_trace
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.window_frame
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.retained
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.trace
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.advance_result
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.result
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.retained_observer
#print axioms SmcTuring.Appendix.Listing8OwnerSequence.retained_image
#print axioms SmcTuring.Appendix.Listing8OwnerImage.source_field_bounds
#print axioms SmcTuring.Appendix.Listing8OwnerImage.source_field_fits
#print axioms SmcTuring.Appendix.Listing8OwnerImage.entry
#print axioms SmcTuring.Appendix.Listing8OwnerImage.frame
#print axioms SmcTuring.Appendix.Listing8OwnerImage.pointer_bounds
#print axioms SmcTuring.Appendix.Listing8OwnerImage.pointer_patch_frame
#print axioms SmcTuring.Appendix.Listing8OwnerImage.pointer_frame
#print axioms SmcTuring.Appendix.Listing8OwnerImage.original_frame
#print axioms SmcTuring.Appendix.Listing8OwnerImage.source_transition_after_copies
#print axioms SmcTuring.Appendix.Listing8OwnerImage.original_node
#print axioms SmcTuring.Appendix.Listing8OwnerImage.original_transition
#print axioms SmcTuring.Appendix.Listing8OwnerImage.node_windows
#print axioms SmcTuring.Appendix.Listing8OwnerImage.transition_windows
#print axioms SmcTuring.Appendix.Listing8OwnerImage.initial_current
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.chain
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.endpoint
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.source_limits
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.pointer_valid
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.scalar_bounds
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.scalar_code_bounds
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.valid
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.window_bounds
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.outside
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.trace
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.instruction_count
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.result
#print axioms SmcTuring.Appendix.Listing8CopiedOwners.retained_image
#print axioms SmcTuring.Appendix.Listing8OwnerInput.rule_spelling
#print axioms SmcTuring.Appendix.Listing8OwnerInput.rule_position
#print axioms SmcTuring.Appendix.Listing8OwnerInput.rule_patch
#print axioms SmcTuring.Appendix.Listing8OwnerInput.fresh_spelling
#print axioms SmcTuring.Appendix.Listing8OwnerInput.fresh_position
#print axioms SmcTuring.Appendix.Listing8OwnerInput.fresh_patch
#print axioms SmcTuring.Appendix.Listing8OwnerInput.input_image
#print axioms SmcTuring.Appendix.Listing8OwnerInput.cursor_after_initializer
#print axioms SmcTuring.Appendix.Listing8OwnerInput.cursor
#print axioms SmcTuring.Appendix.Listing8OwnerInput.bound_cursor
#print axioms SmcTuring.Appendix.Listing8OwnerInput.source_node
#print axioms SmcTuring.Appendix.Listing8OwnerInput.tape_symbol
#print axioms SmcTuring.Appendix.Listing8OwnerInput.corrected_cursor_label
#print axioms SmcTuring.Appendix.Listing8OwnerInput.registers

#print axioms SmcTuring.Native.StringDwordCopy.native_encoding
#print axioms SmcTuring.Native.StringDwordCopy.native_execute
#print axioms SmcTuring.Native.StringDwordCopy.low_x86
#print axioms SmcTuring.Native.StringDwordCopy.lift_x86
#print axioms SmcTuring.Native.StringDwordCopy.copy_encoding
#print axioms SmcTuring.Native.StringDwordCopy.copy_execute
#print axioms SmcTuring.Native.StringDwordCopy.word_trace
#print axioms SmcTuring.Native.StringDwordCopy.dword_trace

#print axioms SmcTuring.Native.StringDwordSequence.trace

#print axioms SmcTuring.Native.StringDwordSequence.endpoint

#print axioms SmcTuring.Native.StringDwordSequence.memory_snapshot

#print axioms SmcTuring.Native.StringDwordSequence.memory_effect

#print axioms SmcTuring.Native.StringDwordSequence.writes_window

#print axioms SmcTuring.Native.StringDwordSequence.registers

#print axioms SmcTuring.Native.PointerHalves.pack_append

#print axioms SmcTuring.Native.PointerHalves.split_get

#print axioms SmcTuring.Native.PointerHalves.low_get

#print axioms SmcTuring.Native.PointerHalves.high_get

#print axioms SmcTuring.Appendix.Listing8PointerCopies.chain

#print axioms SmcTuring.Appendix.Listing8PointerCopies.sizes

#print axioms SmcTuring.Appendix.Listing8PointerCopies.cursor_before_patch

#print axioms SmcTuring.Appendix.Listing8PointerCopies.cursor_before

#print axioms SmcTuring.Appendix.Listing8PointerCopies.source_bounds

#print axioms SmcTuring.Appendix.Listing8PointerCopies.destination_after

#print axioms SmcTuring.Appendix.Listing8PointerCopies.outside

#print axioms SmcTuring.Appendix.Listing8PointerCopies.word_length

#print axioms SmcTuring.Appendix.Listing8PointerCopies.bytes_length

#print axioms SmcTuring.Appendix.Listing8PointerCopies.word_intact

#print axioms SmcTuring.Appendix.Listing8PointerCopies.trace

#print axioms SmcTuring.Appendix.Listing8PointerCopies.endpoint

#print axioms SmcTuring.Appendix.Listing8PointerCopies.memory_effect

#print axioms SmcTuring.Appendix.Listing8PointerCopies.window_frame

#print axioms SmcTuring.Appendix.Listing8PointerCopies.registers

#print axioms SmcTuring.Appendix.Listing8PointerImage.prefix_window

#print axioms SmcTuring.Appendix.Listing8PointerImage.initial_helper

#print axioms SmcTuring.Appendix.Listing8PointerImage.helper_current

#print axioms SmcTuring.Appendix.Listing8PointerImage.trace

#print axioms SmcTuring.Appendix.Listing8PointerImage.instruction_count

#print axioms SmcTuring.Appendix.Listing8PointerImage.endpoint

#print axioms SmcTuring.Appendix.Listing8PointerValues.copied_operand

#print axioms SmcTuring.Appendix.Listing8PointerValues.sources

#print axioms SmcTuring.Appendix.Listing8PointerValues.transition_cursor

#print axioms SmcTuring.Appendix.Listing8PointerValues.input_image

#print axioms SmcTuring.Appendix.Listing8PointerValues.x64_source_halves

#print axioms SmcTuring.Appendix.Listing8PointerValues.memory_effect

#print axioms SmcTuring.Appendix.Listing8PointerValues.input_cursor

#print axioms SmcTuring.Appendix.Listing8PointerValues.source_node

#print axioms SmcTuring.Appendix.Listing8PointerValues.tape_symbol

#print axioms SmcTuring.Appendix.Listing8PointerValues.registers

#print axioms SmcTuring.Native.DecodeImage.payload

#print axioms SmcTuring.Native.DecodeImage.tag

#print axioms SmcTuring.Native.DecodeImage.core

#print axioms SmcTuring.Native.DecodeImage.core_prefix

#print axioms SmcTuring.Native.DecodeImage.native

#print axioms SmcTuring.Native.DecodeImage.native_fetch

#print axioms SmcTuring.Native.StringDwordArithmetic.fallback

#print axioms SmcTuring.Native.StringDwordArithmetic.encoding

#print axioms SmcTuring.Native.StringDwordArithmetic.execute

#print axioms SmcTuring.Native.DwordDecodeImage.two_words

#print axioms SmcTuring.Native.DwordDecodeImage.arithmetic

#print axioms SmcTuring.Native.DwordDecodeImage.arithmetic_fetch

#print axioms SmcTuring.Native.DwordDecodeImage.copy

#print axioms SmcTuring.Native.DwordDecodeImage.copy_fetch

#print axioms SmcTuring.Native.StringMixed.packet

#print axioms SmcTuring.Native.StringMixed.fetched

#print axioms SmcTuring.Native.StringMixed.execute

#print axioms SmcTuring.Native.StringMixed.trace

#print axioms SmcTuring.Appendix.Listing8InputBounds.masks

#print axioms SmcTuring.Appendix.Listing8InputBounds.positions

#print axioms SmcTuring.Appendix.Listing8InputBounds.cursor_bounds

#print axioms SmcTuring.Appendix.Listing8InputBounds.outside

#print axioms SmcTuring.Appendix.Listing8InputBounds.update

#print axioms SmcTuring.Appendix.Listing8InputMaskEffects.cursor

#print axioms SmcTuring.Appendix.Listing8InputMaskEffects.symbol

#print axioms SmcTuring.Appendix.Listing8InputMaskEffects.endpoint

#print axioms SmcTuring.Appendix.Listing8InputMaskEffects.registers

#print axioms SmcTuring.Appendix.Listing8GlobalInput.entry

#print axioms SmcTuring.Appendix.Listing8GlobalInput.input_image

#print axioms SmcTuring.Appendix.Listing8GlobalInput.cursor

#print axioms SmcTuring.Appendix.Listing8GlobalInput.symbol

#print axioms SmcTuring.Appendix.Listing8GlobalInput.trace

#print axioms SmcTuring.Appendix.Listing8GlobalInput.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalInput.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalInput.tape_value

#print axioms SmcTuring.Appendix.Listing8GlobalInput.retained

#print axioms SmcTuring.Appendix.Listing8GlobalInput.registers

#print axioms SmcTuring.Native.DwordPackets.payload

#print axioms SmcTuring.Native.DwordPackets.header_length

#print axioms SmcTuring.Native.DwordPackets.current

#print axioms SmcTuring.Native.DwordPackets.initial_header

#print axioms SmcTuring.Native.DwordPackets.effect

#print axioms SmcTuring.Native.DwordPackets.intact_put

#print axioms SmcTuring.Native.DwordPackets.trace

#print axioms SmcTuring.Native.DwordPackets.instruction_count

#print axioms SmcTuring.Native.DwordPackets.bytes_length

#print axioms SmcTuring.Native.DwordPackets.initial_headers

#print axioms SmcTuring.Native.DwordPackets.endpoint

#print axioms SmcTuring.Native.DwordPackets.window

#print axioms SmcTuring.Native.DwordPackets.registers

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.helper_chain

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.arithmetic_chain

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.positions

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.helpers_length

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.arithmetic_length

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.packet_lengths

#print axioms SmcTuring.Appendix.Listing8DirectionLayout.bytes_length

#print axioms SmcTuring.Appendix.Listing8DirectionBounds.helper_valid

#print axioms SmcTuring.Appendix.Listing8DirectionBounds.helper_frames

#print axioms SmcTuring.Appendix.Listing8DirectionBounds.arithmetic_valid

#print axioms SmcTuring.Appendix.Listing8DirectionBounds.arithmetic_frames

#print axioms SmcTuring.Appendix.Listing8DirectionBounds.helpers_outside_headers

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.helper_endpoint

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.helper_headers

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.trace

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.endpoint

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.registers

#print axioms SmcTuring.Appendix.Listing8InputWindows.window

#print axioms SmcTuring.Appendix.Listing8GlobalWindows.owners

#print axioms SmcTuring.Appendix.Listing8GlobalWindows.pointers

#print axioms SmcTuring.Appendix.Listing8GlobalWindows.input

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.positions

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.helper_bytes

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.arithmetic_header_bounds

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.input_window

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.pointer_headers

#print axioms SmcTuring.Appendix.Listing8DirectionGeometry.pointer_helpers

#print axioms SmcTuring.Appendix.Listing8DirectionImage.initial_region

#print axioms SmcTuring.Appendix.Listing8DirectionImage.initial_helpers

#print axioms SmcTuring.Appendix.Listing8DirectionImage.initial_headers

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.entry

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.helper_current

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.arithmetic_current

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.trace

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalDirection.registers

#print axioms SmcTuring.Native.StringDwordSequence.window

#print axioms SmcTuring.Native.DwordDataflow.no_carry

#print axioms SmcTuring.Native.DwordDataflow.helpers

#print axioms SmcTuring.Native.DwordDataflow.packets

#print axioms SmcTuring.Native.DwordDataflow.read_offset

#print axioms SmcTuring.Native.DwordDataflow.word_frame

#print axioms SmcTuring.Appendix.Listing8DirectionMemory.memory

#print axioms SmcTuring.Appendix.Listing8DirectionMemory.low_value

#print axioms SmcTuring.Appendix.Listing8DirectionMemory.high_value

#print axioms SmcTuring.Appendix.Listing8DirectionMemory.blend_mask

#print axioms SmcTuring.Native.DwordXor.roundtrip

#print axioms SmcTuring.Native.DwordXor.decode_image

#print axioms SmcTuring.Native.DwordXor.fetch_encoding

#print axioms SmcTuring.Native.DwordXor.fetch_image

#print axioms SmcTuring.Native.DwordXor.located_effect

#print axioms SmcTuring.Native.DwordXor.native_x86

#print axioms SmcTuring.Native.DwordXor.frame

#print axioms SmcTuring.Native.DwordXor.registers

#print axioms SmcTuring.Native.StringDwordXor.encoding

#print axioms SmcTuring.Native.StringDwordXor.execute

#print axioms SmcTuring.Native.DwordXorHelper.bytes_length

#print axioms SmcTuring.Native.DwordXorHelper.exchange_effect

#print axioms SmcTuring.Native.DwordXorHelper.first_effect

#print axioms SmcTuring.Native.DwordXorHelper.middle_effect

#print axioms SmcTuring.Native.DwordXorHelper.third_effect

#print axioms SmcTuring.Native.DwordXorHelper.effect

#print axioms SmcTuring.Native.DwordXorHelper.trace

#print axioms SmcTuring.Native.DwordXorHelper.window

#print axioms SmcTuring.Appendix.Listing8DirectionFields.field_bounds

#print axioms SmcTuring.Appendix.Listing8DirectionFields.input_outside

#print axioms SmcTuring.Appendix.Listing8DirectionFields.input_frame

#print axioms SmcTuring.Appendix.Listing8DirectionFields.pointer_low

#print axioms SmcTuring.Appendix.Listing8DirectionFields.pointer_high

#print axioms SmcTuring.Appendix.Listing8DirectionFields.pointer_frame

#print axioms SmcTuring.Appendix.Listing8DirectionValues.back_low

#print axioms SmcTuring.Appendix.Listing8DirectionValues.forward_low

#print axioms SmcTuring.Appendix.Listing8DirectionValues.back_high

#print axioms SmcTuring.Appendix.Listing8DirectionValues.forward_high

#print axioms SmcTuring.Appendix.Listing8DirectionValues.direction

#print axioms SmcTuring.Appendix.Listing8DirectionSelected.low_result

#print axioms SmcTuring.Appendix.Listing8DirectionSelected.high_result

#print axioms SmcTuring.Appendix.Listing8DirectionSelected.selected

#print axioms SmcTuring.Native.DwordXorSequence.trace

#print axioms SmcTuring.Native.DwordXorSequence.initial_helpers

#print axioms SmcTuring.Native.DwordXorSequence.endpoint

#print axioms SmcTuring.Native.DwordXorSequence.memory_effect

#print axioms SmcTuring.Native.DwordXorSequence.window

#print axioms SmcTuring.Native.DwordXorSequence.instruction_count

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.xor_chain

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.xor_bytes

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.xor_valid

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.xor_frames

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.masks_chain

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.heads_chain

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.packets_valid

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.masks_frames

#print axioms SmcTuring.Appendix.Listing8HeadTailBounds.heads_frames

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.xor_headers

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.mask_headers

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.xor_span

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.mask_span

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.head_span

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.selection_span

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.xor_length

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.prefix_span

#print axioms SmcTuring.Appendix.Listing8HeadTailFrames.headers_chain

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.xor_endpoint

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.mask_endpoint

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.xor_current

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.head_current

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.trace

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.endpoint

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.registers

#print axioms SmcTuring.Appendix.Listing8HeadTailTrace.window

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.tail_bounds

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.window_span

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.direction_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.distribution_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.input_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.pointer_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.helper_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.packet_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.masks_separate

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.cursor_input_outside

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.cursor_helpers

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.cursor_packets

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.mask_helpers

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.mask_packets

#print axioms SmcTuring.Appendix.Listing8HeadGeometry.source_field_outside

#print axioms SmcTuring.Appendix.Listing8HeadImage.current_window

#print axioms SmcTuring.Appendix.Listing8HeadImage.initial_xor

#print axioms SmcTuring.Appendix.Listing8HeadImage.xor_current

#print axioms SmcTuring.Appendix.Listing8HeadImage.initial_headers

#print axioms SmcTuring.Appendix.Listing8HeadImage.header_member

#print axioms SmcTuring.Appendix.Listing8HeadImage.headers_current

#print axioms SmcTuring.Appendix.Listing8HeadTailMemory.memory

#print axioms SmcTuring.Appendix.Listing8HeadTailMemory.low_cursor

#print axioms SmcTuring.Appendix.Listing8HeadTailMemory.high_cursor

#print axioms SmcTuring.Appendix.Listing8HeadTailMemory.selected

#print axioms SmcTuring.Appendix.Listing8HeadEntryValues.input_mask

#print axioms SmcTuring.Appendix.Listing8HeadEntryValues.mask

#print axioms SmcTuring.Appendix.Listing8HeadEntryValues.cursor

#print axioms SmcTuring.Appendix.Listing8GlobalHead.entry

#print axioms SmcTuring.Appendix.Listing8GlobalHead.trace

#print axioms SmcTuring.Appendix.Listing8GlobalHead.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalHead.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalHead.registers

#print axioms SmcTuring.Appendix.Listing8HeadValues.head

#print axioms SmcTuring.Appendix.Listing8HeadValues.tape

#print axioms SmcTuring.Appendix.Listing8CallSelection.printed_expression

#print axioms SmcTuring.Appendix.Listing8CallSelection.toggle_selection

#print axioms SmcTuring.Appendix.Listing8CallSelection.displacement_selection

#print axioms SmcTuring.Appendix.Listing8CallSelection.operand_current

#print axioms SmcTuring.Appendix.Listing8CallSelection.patched_fetch

#print axioms SmcTuring.Appendix.Listing8CallSelection.call_target

#print axioms SmcTuring.Appendix.Listing8CallSelection.call_return_word

#print axioms SmcTuring.Appendix.Listing8CallSelection.reset_fetch

#print axioms SmcTuring.Native.DwordXorSequence.registers

#print axioms SmcTuring.Native.DwordDataflow.read_disjoint

#print axioms SmcTuring.Appendix.Listing8DirectionTrace.window

#print axioms SmcTuring.Appendix.Listing8InputMaskEffects.destination_values

#print axioms SmcTuring.Appendix.Listing8StateLayout.helper_chain

#print axioms SmcTuring.Appendix.Listing8StateLayout.packet_chain

#print axioms SmcTuring.Appendix.Listing8StateLayout.positions

#print axioms SmcTuring.Appendix.Listing8StateLayout.helper_length

#print axioms SmcTuring.Appendix.Listing8StateLayout.packet_length

#print axioms SmcTuring.Appendix.Listing8StateLayout.helper_span

#print axioms SmcTuring.Appendix.Listing8StateLayout.packet_span

#print axioms SmcTuring.Appendix.Listing8StateLayout.bytes_length

#print axioms SmcTuring.Appendix.Listing8StateBounds.helper_valid

#print axioms SmcTuring.Appendix.Listing8StateBounds.helper_frames

#print axioms SmcTuring.Appendix.Listing8StateBounds.packet_valid

#print axioms SmcTuring.Appendix.Listing8StateBounds.packet_frames

#print axioms SmcTuring.Appendix.Listing8StateBounds.helpers_outside_headers

#print axioms SmcTuring.Appendix.Listing8StateTrace.helper_endpoint

#print axioms SmcTuring.Appendix.Listing8StateTrace.helper_headers

#print axioms SmcTuring.Appendix.Listing8StateTrace.trace

#print axioms SmcTuring.Appendix.Listing8StateTrace.endpoint

#print axioms SmcTuring.Appendix.Listing8StateTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8StateTrace.registers

#print axioms SmcTuring.Appendix.Listing8StateTrace.window

#print axioms SmcTuring.Appendix.Listing8StateGeometry.positions

#print axioms SmcTuring.Appendix.Listing8StateGeometry.local_bounds

#print axioms SmcTuring.Appendix.Listing8StateGeometry.window_span

#print axioms SmcTuring.Appendix.Listing8StateGeometry.direction_outside

#print axioms SmcTuring.Appendix.Listing8StateGeometry.distribution_outside

#print axioms SmcTuring.Appendix.Listing8StateGeometry.pointer_outside

#print axioms SmcTuring.Appendix.Listing8StateGeometry.input_outside

#print axioms SmcTuring.Appendix.Listing8StateFrames.direction_helpers

#print axioms SmcTuring.Appendix.Listing8StateFrames.direction_packets

#print axioms SmcTuring.Appendix.Listing8StateFrames.tail_xors

#print axioms SmcTuring.Appendix.Listing8StateFrames.tail_packets

#print axioms SmcTuring.Appendix.Listing8StateFrames.after_head

#print axioms SmcTuring.Appendix.Listing8StateImage.initial_region

#print axioms SmcTuring.Appendix.Listing8StateImage.initial_helpers

#print axioms SmcTuring.Appendix.Listing8StateImage.initial_headers

#print axioms SmcTuring.Appendix.Listing8StateImage.current_window

#print axioms SmcTuring.Appendix.Listing8StateImage.helper_current

#print axioms SmcTuring.Appendix.Listing8StateImage.header_member

#print axioms SmcTuring.Appendix.Listing8StateImage.headers_current

#print axioms SmcTuring.Appendix.Listing8GlobalState.entry

#print axioms SmcTuring.Appendix.Listing8GlobalState.trace

#print axioms SmcTuring.Appendix.Listing8GlobalState.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalState.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalState.registers

#print axioms SmcTuring.Appendix.Listing8StateMemory.memory

#print axioms SmcTuring.Appendix.Listing8StateMemory.low_cursor

#print axioms SmcTuring.Appendix.Listing8StateMemory.high_cursor

#print axioms SmcTuring.Appendix.Listing8StateMemory.selected

#print axioms SmcTuring.Appendix.Listing8StateFields.field_span

#print axioms SmcTuring.Appendix.Listing8StateFields.new_input_outside

#print axioms SmcTuring.Appendix.Listing8StateFields.cursor_input_outside

#print axioms SmcTuring.Appendix.Listing8StateFields.first_cursor_before

#print axioms SmcTuring.Appendix.Listing8StateFields.cursor_selection_helpers

#print axioms SmcTuring.Appendix.Listing8StateFields.cursor_selection_packets

#print axioms SmcTuring.Appendix.Listing8StateFields.cursor_tail_xors

#print axioms SmcTuring.Appendix.Listing8StateFields.cursor_tail_packets

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.new_frame

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.neighbor_before

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.new_low

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.new_high

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.mask

#print axioms SmcTuring.Appendix.Listing8StateEntryValues.cursor

#print axioms SmcTuring.Appendix.Listing8StateValues.transition

#print axioms SmcTuring.Appendix.Listing8StateValues.head_frame

#print axioms SmcTuring.Appendix.Listing8StateValues.head

#print axioms SmcTuring.Appendix.Listing8StateValues.tape

#print axioms SmcTuring.Native.WordNegation.encode_length

#print axioms SmcTuring.Native.WordNegation.roundtrip

#print axioms SmcTuring.Native.WordNegation.fetch_encoding

#print axioms SmcTuring.Native.WordNegation.located_effect

#print axioms SmcTuring.Native.StringControl.previous_fetch

#print axioms SmcTuring.Native.StringControl.previous_trace

#print axioms SmcTuring.Native.StringControl.trace_append

#print axioms SmcTuring.Native.StringControl.wide_previous_none

#print axioms SmcTuring.Native.StringControl.negation_encoding

#print axioms SmcTuring.Native.StringControl.negation_execute

#print axioms SmcTuring.Native.WordMemoryArithmetic.form_length

#print axioms SmcTuring.Native.WordMemoryArithmetic.located_effect

#print axioms SmcTuring.Native.ControlPackets.bytes_length

#print axioms SmcTuring.Native.ControlPackets.fetched

#print axioms SmcTuring.Native.ControlPackets.execute_effect

#print axioms SmcTuring.Native.ControlPackets.effect_window

#print axioms SmcTuring.Native.ControlPackets.trace

#print axioms SmcTuring.Native.ControlPackets.initial_packets

#print axioms SmcTuring.Native.ControlPackets.endpoint

#print axioms SmcTuring.Native.ControlPackets.window

#print axioms SmcTuring.Native.ControlPackets.registers

#print axioms SmcTuring.Native.MixedFrames.word_after_word

#print axioms SmcTuring.Native.MixedFrames.word_after_dword

#print axioms SmcTuring.Native.MixedFrames.words_commute

#print axioms SmcTuring.Native.MixedFrames.sub_zero

#print axioms SmcTuring.Native.MixedFrames.restored_pair

#print axioms SmcTuring.Native.DwordOperands.shape

#print axioms SmcTuring.Native.DwordOperands.value

#print axioms SmcTuring.Appendix.Listing8FailComparison.span

#print axioms SmcTuring.Appendix.Listing8FailComparison.bytes_length

#print axioms SmcTuring.Appendix.Listing8FailComparison.chain

#print axioms SmcTuring.Appendix.Listing8FailComparison.valid

#print axioms SmcTuring.Appendix.Listing8FailComparison.code_separation

#print axioms SmcTuring.Appendix.Listing8FailComparison.trace

#print axioms SmcTuring.Appendix.Listing8FailComparison.endpoint

#print axioms SmcTuring.Appendix.Listing8FailComparison.instruction_count

#print axioms SmcTuring.Appendix.Listing8FailComparison.registers

#print axioms SmcTuring.Appendix.Listing8FailComparisonEffects.mask_from_carry

#print axioms SmcTuring.Appendix.Listing8FailComparisonEffects.effect

#print axioms SmcTuring.Appendix.Listing8FailComparisonEffects.cursor

#print axioms SmcTuring.Appendix.Listing8FailComparisonEffects.mask

#print axioms SmcTuring.Appendix.Listing8FailComparisonEffects.accumulator

#print axioms SmcTuring.Appendix.Listing8FailureLayout.comparison_end

#print axioms SmcTuring.Appendix.Listing8FailureLayout.source_end

#print axioms SmcTuring.Appendix.Listing8FailureLayout.positions

#print axioms SmcTuring.Appendix.Listing8FailureLayout.post_length

#print axioms SmcTuring.Appendix.Listing8FailureLayout.bytes_length

#print axioms SmcTuring.Appendix.Listing8FailureLayout.post_chain

#print axioms SmcTuring.Appendix.Listing8FailureLayout.post_span

#print axioms SmcTuring.Appendix.Listing8FailureLayout.printed_displacement

#print axioms SmcTuring.Appendix.Listing8FailureBounds.comparison_bounds

#print axioms SmcTuring.Appendix.Listing8FailureBounds.reset_effect

#print axioms SmcTuring.Appendix.Listing8FailureBounds.owner_fits

#print axioms SmcTuring.Appendix.Listing8FailureBounds.post_valid

#print axioms SmcTuring.Appendix.Listing8FailureBounds.post_outside_headers

#print axioms SmcTuring.Appendix.Listing8FailureBounds.mask_outside_post_headers

#print axioms SmcTuring.Appendix.Listing8FailureImage.reset_current

#print axioms SmcTuring.Appendix.Listing8FailureImage.owner_current

#print axioms SmcTuring.Appendix.Listing8FailureImage.comparison_current

#print axioms SmcTuring.Appendix.Listing8FailureImage.post_current

#print axioms SmcTuring.Appendix.Listing8FailureImage.post_initial

#print axioms SmcTuring.Appendix.Listing8FailureImage.reset_pc

#print axioms SmcTuring.Appendix.Listing8FailureImage.reset_window

#print axioms SmcTuring.Appendix.Listing8FailureImage.reset_owner

#print axioms SmcTuring.Appendix.Listing8FailureImage.owner_effect

#print axioms SmcTuring.Appendix.Listing8FailureImage.comparison_entry

#print axioms SmcTuring.Appendix.Listing8FailureImage.comparison_image

#print axioms SmcTuring.Appendix.Listing8FailureImage.comparison_zero

#print axioms SmcTuring.Appendix.Listing8FailureTrace.comparison_endpoint

#print axioms SmcTuring.Appendix.Listing8FailureTrace.post_headers

#print axioms SmcTuring.Appendix.Listing8FailureTrace.trace

#print axioms SmcTuring.Appendix.Listing8FailureTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8FailureTrace.endpoint

#print axioms SmcTuring.Appendix.Listing8FailureValues.owner_cursor

#print axioms SmcTuring.Appendix.Listing8FailureValues.owner_source

#print axioms SmcTuring.Appendix.Listing8FailureValues.mismatch

#print axioms SmcTuring.Appendix.Listing8FailureValues.comparison_memory

#print axioms SmcTuring.Appendix.Listing8FailureValues.store_operand

#print axioms SmcTuring.Appendix.Listing8FailureValues.mask_complement

#print axioms SmcTuring.Appendix.Listing8FailureValues.memory

#print axioms SmcTuring.Appendix.Listing8FailureValues.registers

#print axioms SmcTuring.Appendix.Listing8FailureValues.window

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.positions

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.local_bounds

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.pointer_outside

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.input_outside

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.state_helpers_before

#print axioms SmcTuring.Appendix.Listing8FailureGeometry.state_packets_before

#print axioms SmcTuring.Appendix.Listing8FailureFrames.state_before

#print axioms SmcTuring.Appendix.Listing8FailureFrames.after_state

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.region_end

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.backing_region

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.backing_call

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.image_window

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.initial_region

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.initial_call

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.current_region

#print axioms SmcTuring.Appendix.Listing8FailureGlobalImage.current_call

#print axioms SmcTuring.Appendix.Listing8GlobalFailure.entry

#print axioms SmcTuring.Appendix.Listing8GlobalFailure.trace

#print axioms SmcTuring.Appendix.Listing8GlobalFailure.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalFailure.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalFailure.registers

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.failure_condition

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.call_original

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.call_value

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.call_packet

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.call_fetch

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.before_window

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.transition

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.head

#print axioms SmcTuring.Appendix.Listing8FailureGlobalValues.tape

#print axioms SmcTuring.Native.WordAddImmediate.encode_length
#print axioms SmcTuring.Native.WordAddImmediate.roundtrip
#print axioms SmcTuring.Native.WordAddImmediate.fetch_encoding
#print axioms SmcTuring.Native.WordAddImmediate.located_effect
#print axioms SmcTuring.Native.WordAddImmediate.positive_four
#print axioms SmcTuring.Native.WordAddImmediate.positive_eighteen
#print axioms SmcTuring.Native.StringStack.previous_fetch
#print axioms SmcTuring.Native.StringStack.previous_trace
#print axioms SmcTuring.Native.StringStack.trace_append
#print axioms SmcTuring.Native.StringStack.add_previous_none
#print axioms SmcTuring.Native.StringStack.add_encoding
#print axioms SmcTuring.Native.StringStack.native_encoding
#print axioms SmcTuring.Native.StringStack.native_execute
#print axioms SmcTuring.Native.StackMemory.exchange_stack_effect
#print axioms SmcTuring.Native.StackMemory.store_acc_effect
#print axioms SmcTuring.Native.StackMemory.moffs_effect
#print axioms SmcTuring.Native.StackWindows.word_window
#print axioms SmcTuring.Appendix.Listing4StackLayout.first_displacement
#print axioms SmcTuring.Appendix.Listing4StackLayout.second_displacement
#print axioms SmcTuring.Appendix.Listing4StackLayout.bytes_length
#print axioms SmcTuring.Appendix.Listing4StackLayout.stptr_fits
#print axioms SmcTuring.Appendix.Listing4StackLayout.return_inside
#print axioms SmcTuring.Appendix.Listing4StackLayout.stptr_inside
#print axioms SmcTuring.Appendix.Listing4StackLayout.fields_separate
#print axioms SmcTuring.Appendix.Listing4StackLayout.initial_stptr
#print axioms SmcTuring.Appendix.Listing4StackLayout.initial_svptr
#print axioms SmcTuring.Appendix.Listing4StackInit.swapped_effect
#print axioms SmcTuring.Appendix.Listing4StackInit.restored_effect
#print axioms SmcTuring.Appendix.Listing4StackInit.stored_effect
#print axioms SmcTuring.Appendix.Listing4StackInit.effect
#print axioms SmcTuring.Appendix.Listing4StackInit.stptr_value
#print axioms SmcTuring.Appendix.Listing4StackInit.svptr_value
#print axioms SmcTuring.Appendix.Listing4StackInitTrace.trace
#print axioms SmcTuring.Appendix.Listing4StackInitTrace.initialized_trace
#print axioms SmcTuring.Appendix.Listing4JumpLayout.prefix_length
#print axioms SmcTuring.Appendix.Listing4JumpLayout.bytes_length
#print axioms SmcTuring.Appendix.Listing4JumpLayout.positions
#print axioms SmcTuring.Appendix.Listing4JumpLayout.first_reach
#print axioms SmcTuring.Appendix.Listing4JumpLayout.adjust_reach
#print axioms SmcTuring.Appendix.Listing4JumpLayout.saved_reach
#print axioms SmcTuring.Appendix.Listing4JumpLayout.stack_decrement
#print axioms SmcTuring.Appendix.Listing4JumpEffects.exchanged_effect
#print axioms SmcTuring.Appendix.Listing4JumpEffects.adjusted_effect
#print axioms SmcTuring.Appendix.Listing4JumpEffects.prefix_effect
#print axioms SmcTuring.Appendix.Listing4JumpEffects.called_effect
#print axioms SmcTuring.Appendix.Listing4Boot.bytes_length
#print axioms SmcTuring.Appendix.Listing4Boot.endpoint
#print axioms SmcTuring.Appendix.Listing4Boot.stack_before_jump
#print axioms SmcTuring.Appendix.Listing4Boot.return_before_jump
#print axioms SmcTuring.Appendix.Listing4Boot.initial_current
#print axioms SmcTuring.Appendix.Listing4Boot.stack_packet
#print axioms SmcTuring.Appendix.Listing4Boot.jump_packet
#print axioms SmcTuring.Appendix.Listing4Boot.trace
#print axioms SmcTuring.Appendix.Listing4Boot.initialized_trace
#print axioms SmcTuring.Appendix.Listing4Boot.instruction_count
#print axioms SmcTuring.Appendix.Listing4BootValues.effect
#print axioms SmcTuring.Appendix.Listing4BootValues.endpoint
#print axioms SmcTuring.Appendix.Listing4BootValues.stack
#print axioms SmcTuring.Appendix.Listing4BootValues.return_word
#print axioms SmcTuring.Appendix.Listing4BootValues.saved_stack
#print axioms SmcTuring.Appendix.Listing4BootValues.registers
#print axioms SmcTuring.Appendix.Listing4BootValues.later_window

#print axioms SmcTuring.Native.StackAdjust.subtract_encoding
#print axioms SmcTuring.Native.StackAdjust.subtract_effect
#print axioms SmcTuring.Native.ByteOverlay.commute
#print axioms SmcTuring.Native.ByteOverlay.run_put
#print axioms SmcTuring.Appendix.Listing4TargetLayout.positions
#print axioms SmcTuring.Appendix.Listing4TargetLayout.bytes_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.instruction_count
#print axioms SmcTuring.Appendix.Listing4TargetLayout.first_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.adjust_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.third_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.fourth_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.fifth_length
#print axioms SmcTuring.Appendix.Listing4TargetLayout.slot_adjustment
#print axioms SmcTuring.Appendix.Listing4TargetMemory.original_return
#print axioms SmcTuring.Appendix.Listing4TargetMemory.restore_return
#print axioms SmcTuring.Appendix.Listing4TargetEffects.swapped_effect
#print axioms SmcTuring.Appendix.Listing4TargetEffects.adjusted_effect
#print axioms SmcTuring.Appendix.Listing4TargetEffects.exchanged_effect
#print axioms SmcTuring.Appendix.Listing4TargetEffects.stored_effect
#print axioms SmcTuring.Appendix.Listing4TargetEffects.effect
#print axioms SmcTuring.Appendix.Listing4TargetTrace.windows
#print axioms SmcTuring.Appendix.Listing4TargetTrace.trace
#print axioms SmcTuring.Appendix.Listing4EntryLayout.bytes_length
#print axioms SmcTuring.Appendix.Listing4EntryLayout.endpoint
#print axioms SmcTuring.Appendix.Listing4EntryLayout.instruction_count
#print axioms SmcTuring.Appendix.Listing4EntryLayout.begin_ranges
#print axioms SmcTuring.Appendix.Listing4EntryLayout.target_after_stack
#print axioms SmcTuring.Appendix.Listing4EntryLayout.stack_capacity
#print axioms SmcTuring.Appendix.Listing4EntryLayout.boot_capacity
#print axioms SmcTuring.Appendix.Listing4EntryLayout.target_capacity
#print axioms SmcTuring.Appendix.Listing4Entry.initial_current
#print axioms SmcTuring.Appendix.Listing4Entry.boot_current
#print axioms SmcTuring.Appendix.Listing4Entry.stack_current
#print axioms SmcTuring.Appendix.Listing4Entry.target_current
#print axioms SmcTuring.Appendix.Listing4Entry.call_shape
#print axioms SmcTuring.Appendix.Listing4Entry.trace
#print axioms SmcTuring.Appendix.Listing4Entry.effect
#print axioms SmcTuring.Appendix.Listing4Entry.memory
#print axioms SmcTuring.Appendix.Listing4Entry.registers
#print axioms SmcTuring.Appendix.Listing4EntryValues.target_carry_clear
#print axioms SmcTuring.Appendix.Listing4EntryValues.stptr_value
#print axioms SmcTuring.Appendix.Listing4EntryValues.return_value
#print axioms SmcTuring.Appendix.Listing4EntryValues.code_current
#print axioms SmcTuring.Appendix.Listing8BootImage.memory_overlay
#print axioms SmcTuring.Appendix.Listing8BootImage.separated
#print axioms SmcTuring.Appendix.Listing8BootImage.memory_put
#print axioms SmcTuring.Appendix.Listing8GlobalBoot.entry_capacity
#print axioms SmcTuring.Appendix.Listing8GlobalBoot.body_entry
#print axioms SmcTuring.Appendix.Listing8GlobalBoot.trace
#print axioms SmcTuring.Appendix.Listing8GlobalBoot.instruction_count
#print axioms SmcTuring.Appendix.Listing8GlobalBoot.endpoint
#print axioms SmcTuring.Appendix.Listing8BootControl.call_positions
#print axioms SmcTuring.Appendix.Listing8BootControl.backedge_delta
#print axioms SmcTuring.Appendix.Listing8BootControl.backedge_reach
#print axioms SmcTuring.Appendix.Listing8BootControl.begin_capacity
#print axioms SmcTuring.Appendix.Listing8BootControl.failure_condition
#print axioms SmcTuring.Appendix.Listing8BootControl.call_value
#print axioms SmcTuring.Appendix.Listing8BootControl.call_fetch
#print axioms SmcTuring.Appendix.Listing8GlobalBootValues.transition
#print axioms SmcTuring.Appendix.Listing8GlobalBootValues.head
#print axioms SmcTuring.Appendix.Listing8GlobalBootValues.tape
#print axioms SmcTuring.Appendix.Listing8GlobalBootValues.registers

#print axioms SmcTuring.Appendix.Listing8EarlyOwners.patch_after
#print axioms SmcTuring.Appendix.Listing8EarlyOwners.input_after
#print axioms SmcTuring.Appendix.Listing8EarlyOwners.owners
#print axioms SmcTuring.Appendix.Listing8EarlyOwners.pointers

#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.pointer_targets
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.direction_start
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.first_cursor
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.second_cursor
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.direction_helpers
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.direction_packets
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.tail_xors
#print axioms SmcTuring.Appendix.Listing8EarlyGeometry.tail_packets

#print axioms SmcTuring.Appendix.Listing8EarlyStages.input_outside
#print axioms SmcTuring.Appendix.Listing8EarlyStages.input
#print axioms SmcTuring.Appendix.Listing8EarlyStages.direction
#print axioms SmcTuring.Appendix.Listing8EarlyStages.head

#print axioms SmcTuring.Appendix.Listing8EarlyState.state_start
#print axioms SmcTuring.Appendix.Listing8EarlyState.state_helpers
#print axioms SmcTuring.Appendix.Listing8EarlyState.state_packets
#print axioms SmcTuring.Appendix.Listing8EarlyState.state
#print axioms SmcTuring.Appendix.Listing8EarlyState.failure

#print axioms SmcTuring.Appendix.Listing8StackMetadata.window
#print axioms SmcTuring.Appendix.Listing8StackMetadata.code_current
#print axioms SmcTuring.Appendix.Listing8StackMetadata.stack_packet
#print axioms SmcTuring.Appendix.Listing8StackMetadata.stptr
#print axioms SmcTuring.Appendix.Listing8StackMetadata.return_field

#print axioms SmcTuring.Appendix.Listing8JumpLayout.prefix_length

#print axioms SmcTuring.Appendix.Listing8JumpLayout.instruction_count

#print axioms SmcTuring.Appendix.Listing8JumpLayout.positions

#print axioms SmcTuring.Appendix.Listing8JumpLayout.first_reach

#print axioms SmcTuring.Appendix.Listing8JumpLayout.adjust_reach

#print axioms SmcTuring.Appendix.Listing8JumpLayout.saved_reach

#print axioms SmcTuring.Appendix.Listing8JumpLayout.backedge_reach

#print axioms SmcTuring.Appendix.Listing8JumpLayout.slots_before

#print axioms SmcTuring.Appendix.Listing8JumpLayout.stack_capacity

#print axioms SmcTuring.Appendix.Listing8JumpEffects.exchanged_effect

#print axioms SmcTuring.Appendix.Listing8JumpEffects.adjusted_effect

#print axioms SmcTuring.Appendix.Listing8JumpEffects.prefix_effect

#print axioms SmcTuring.Appendix.Listing8JumpEffects.called_effect

#print axioms SmcTuring.Appendix.Listing8JumpImage.call_position

#print axioms SmcTuring.Appendix.Listing8JumpImage.end_position

#print axioms SmcTuring.Appendix.Listing8JumpImage.capacity

#print axioms SmcTuring.Appendix.Listing8JumpImage.current

#print axioms SmcTuring.Appendix.Listing8JumpTrace.trace

#print axioms SmcTuring.Appendix.Listing8GlobalJump.call_packet

#print axioms SmcTuring.Appendix.Listing8GlobalJump.trace

#print axioms SmcTuring.Appendix.Listing8GlobalJump.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalJump.effect

#print axioms SmcTuring.Appendix.Listing8BeginReturn.call_shape

#print axioms SmcTuring.Appendix.Listing8BeginReturn.target_current

#print axioms SmcTuring.Appendix.Listing8BeginReturn.trace

#print axioms SmcTuring.Appendix.Listing8BeginReturn.effect

#print axioms SmcTuring.Appendix.Listing8BeginReturn.instruction_count

#print axioms SmcTuring.Appendix.Listing8JumpValues.add_carry_clear

#print axioms SmcTuring.Appendix.Listing8JumpValues.failure_condition

#print axioms SmcTuring.Appendix.Listing8JumpValues.return_word

#print axioms SmcTuring.Appendix.Listing8JumpValues.endpoint

#print axioms SmcTuring.Appendix.Listing8JumpValues.saved_stack

#print axioms SmcTuring.Appendix.Listing8JumpValues.registers

#print axioms SmcTuring.Appendix.Listing8BeginValues.transition

#print axioms SmcTuring.Appendix.Listing8BeginValues.head

#print axioms SmcTuring.Appendix.Listing8BeginValues.tape

#print axioms SmcTuring.Appendix.Listing8BeginValues.registers

#print axioms SmcTuring.Appendix.Listing8LateFrames.input_outside

#print axioms SmcTuring.Appendix.Listing8LateFrames.after_state

#print axioms SmcTuring.Appendix.Listing8LateFrames.initial_image

#print axioms SmcTuring.Appendix.Listing8LateFrames.after_failure

#print axioms SmcTuring.Appendix.Listing8FailLayout.bytes_length

#print axioms SmcTuring.Appendix.Listing8FailLayout.end_offset

#print axioms SmcTuring.Appendix.Listing8FailLayout.origin_before

#print axioms SmcTuring.Appendix.Listing8FailLayout.placement

#print axioms SmcTuring.Appendix.Listing8FailLayout.ranges

#print axioms SmcTuring.Appendix.Listing8FailLayout.capacity

#print axioms SmcTuring.Appendix.Listing8FailLayout.source_windows

#print axioms SmcTuring.Appendix.Listing8FailImage.body_window

#print axioms SmcTuring.Appendix.Listing8FailImage.current

#print axioms SmcTuring.Appendix.Listing8FailReturn.trace

#print axioms SmcTuring.Appendix.Listing8FailReturn.effect

#print axioms SmcTuring.Appendix.Listing8FailReturn.instruction_count

#print axioms SmcTuring.Appendix.Listing8FailReturn.later_window

#print axioms SmcTuring.Appendix.Listing8OriginalPointer.trace

#print axioms SmcTuring.Appendix.Listing8OriginalPointer.unified_trace

#print axioms SmcTuring.Appendix.Listing8OriginalPointer.effect

#print axioms SmcTuring.Appendix.Listing8OriginalOwners.advance_effect

#print axioms SmcTuring.Appendix.Listing8OriginalOwners.advance_trace

#print axioms SmcTuring.Appendix.Listing8OriginalOwners.trace

#print axioms SmcTuring.Appendix.Listing8OriginalOwners.result

#print axioms SmcTuring.Appendix.Listing8TransitionSource.packed_bounds

#print axioms SmcTuring.Appendix.Listing8TransitionSource.initial_current

#print axioms SmcTuring.Appendix.Listing8TransitionSource.current

#print axioms SmcTuring.Appendix.Listing8TransitionSource.after_fail

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.contiguous

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.total

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.valid

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.current

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.trace

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.result

#print axioms SmcTuring.Appendix.Listing8TransitionBlock.instruction_count

#print axioms SmcTuring.Appendix.Listing8FailTransition.trace

#print axioms SmcTuring.Appendix.Listing8FailTransition.result

#print axioms SmcTuring.Appendix.Listing8FailTransition.instruction_count

#print axioms SmcTuring.Appendix.Listing8FailTransition.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8OriginalOwnerValues.accumulator_result

#print axioms SmcTuring.Appendix.Listing8OriginalOwnerValues.transition_accumulator

#print axioms SmcTuring.Appendix.Listing8FailTransitionValues.endpoint

#print axioms SmcTuring.Appendix.Listing8FailTransitionValues.accumulator

#print axioms SmcTuring.Appendix.Listing8FailTransitionValues.transition

#print axioms SmcTuring.Appendix.Listing8FailTransitionValues.head

#print axioms SmcTuring.Appendix.Listing8FailTransitionValues.tape

#print axioms SmcTuring.Native.WordCopyPacket.bytes_length

#print axioms SmcTuring.Native.WordCopyPacket.intact

#print axioms SmcTuring.Native.WordCopyPacket.trace

#print axioms SmcTuring.Native.WordCopyPacket.effect

#print axioms SmcTuring.Appendix.Listing8RetainedInputSource.current

#print axioms SmcTuring.Appendix.Listing8RetainedInputSource.body_current

#print axioms SmcTuring.Appendix.Listing8RetainedInputSource.body_value

#print axioms SmcTuring.Appendix.Listing8RetainedInputSource.after_ttape

#print axioms SmcTuring.Appendix.Listing8ResetLayout.positions

#print axioms SmcTuring.Appendix.Listing8ResetLayout.bytes_length

#print axioms SmcTuring.Appendix.Listing8ResetLayout.instruction_count

#print axioms SmcTuring.Appendix.Listing8ResetLayout.marker_bytes

#print axioms SmcTuring.Appendix.Listing8ResetLayout.owner_capacity

#print axioms SmcTuring.Appendix.Listing8ResetLayout.marker_capacity

#print axioms SmcTuring.Appendix.Listing8ResetPackets.store_current

#print axioms SmcTuring.Appendix.Listing8ResetPackets.input_current

#print axioms SmcTuring.Appendix.Listing8ResetPackets.owner_current

#print axioms SmcTuring.Appendix.Listing8ResetPackets.transition_current

#print axioms SmcTuring.Appendix.Listing8ResetPackets.marker_current

#print axioms SmcTuring.Appendix.Listing8ResetEffects.store_effect

#print axioms SmcTuring.Appendix.Listing8ResetEffects.input_effect

#print axioms SmcTuring.Appendix.Listing8ResetEffects.input_window

#print axioms SmcTuring.Appendix.Listing8ResetEffects.owner_current

#print axioms SmcTuring.Appendix.Listing8ResetEffects.owner_effect

#print axioms SmcTuring.Appendix.Listing8ResetEffects.owner_value

#print axioms SmcTuring.Appendix.Listing8ResetEffects.transition_effect

#print axioms SmcTuring.Appendix.Listing8ResetEffects.marker_current

#print axioms SmcTuring.Appendix.Listing8ResetEffects.effect

#print axioms SmcTuring.Appendix.Listing8ResetTrace.store_window

#print axioms SmcTuring.Appendix.Listing8ResetTrace.trace

#print axioms SmcTuring.Appendix.Listing8ResetImage.body_window

#print axioms SmcTuring.Appendix.Listing8ResetImage.current

#print axioms SmcTuring.Appendix.Listing8ResetImage.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8ResetGeometry.positions

#print axioms SmcTuring.Appendix.Listing8ResetGeometry.from_positions

#print axioms SmcTuring.Appendix.Listing8ResetGeometry.intervals

#print axioms SmcTuring.Appendix.Listing8ResetGeometry.reset_bounds

#print axioms SmcTuring.Appendix.Listing8ResetGeometry.original

#print axioms SmcTuring.Appendix.Listing8GlobalReset.trace

#print axioms SmcTuring.Appendix.Listing8GlobalReset.effect

#print axioms SmcTuring.Appendix.Listing8GlobalReset.instruction_count

#print axioms SmcTuring.Appendix.Listing8GlobalReset.endpoint

#print axioms SmcTuring.Appendix.Listing8GlobalReset.registers

#print axioms SmcTuring.Appendix.Listing8ResetValues.failure_condition

#print axioms SmcTuring.Appendix.Listing8ResetValues.input_cursor

#print axioms SmcTuring.Appendix.Listing8ResetValues.transition_cursor

#print axioms SmcTuring.Appendix.Listing8ResetValues.call_packet

#print axioms SmcTuring.Appendix.Listing8ResetValues.accumulator

#print axioms SmcTuring.Appendix.Listing8ResetValues.reset_reusable

#print axioms SmcTuring.Appendix.Listing8ResetValues.terminal_boundary

#print axioms SmcTuring.Appendix.Listing8ResetRun.trace

#print axioms SmcTuring.Appendix.Listing8ResetRun.packed_trace

#print axioms SmcTuring.Appendix.Listing8ResetRun.packed_result

#print axioms SmcTuring.Appendix.Listing8ResetFrames.node_window

#print axioms SmcTuring.Appendix.Listing8ResetFrames.tape

#print axioms SmcTuring.Appendix.Listing8TransitionTable.bytes_length

#print axioms SmcTuring.Appendix.Listing8TransitionTable.endpoint

#print axioms SmcTuring.Appendix.Listing8TransitionTable.initial_image

#print axioms SmcTuring.Appendix.Listing8TransitionTable.head_current

#print axioms SmcTuring.Appendix.Listing8TransitionTable.tail_current

#print axioms SmcTuring.Appendix.Listing8TransitionTable.selected_current

#print axioms SmcTuring.Appendix.Listing8TransitionTable.selected_overlay

#print axioms SmcTuring.Appendix.Listing8TransitionTable.selected_bounds

#print axioms SmcTuring.Appendix.Listing8TransitionTable.from_lookup

#print axioms SmcTuring.Appendix.Listing8TransitionTable.fields_current

#print axioms SmcTuring.Appendix.Listing8TransitionTable.fields_overlay

#print axioms SmcTuring.Appendix.Listing8TransitionTable.fields_bounds

#print axioms SmcTuring.Appendix.Listing8TableTrace.result

#print axioms SmcTuring.Appendix.Listing8TableTrace.trace

#print axioms SmcTuring.Appendix.Listing8TableTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8TableTrace.reusable

#print axioms SmcTuring.Appendix.Listing8TableImage.source_overlay

#print axioms SmcTuring.Appendix.Listing8TableImage.before_window

#print axioms SmcTuring.Appendix.Listing8TableImage.current

#print axioms SmcTuring.Appendix.Listing8FullTableImage.fail_bounds

#print axioms SmcTuring.Appendix.Listing8FullTableImage.extra_current

#print axioms SmcTuring.Appendix.Listing8FullTableImage.body_current

#print axioms SmcTuring.Appendix.Listing8FullTableImage.after_fail

#print axioms SmcTuring.Appendix.Listing8FullTable.trace

#print axioms SmcTuring.Appendix.Listing8FullTable.result

#print axioms SmcTuring.Appendix.Listing8FullTable.instruction_count

#print axioms SmcTuring.Appendix.Listing8FullTable.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8TableResetImage.current

#print axioms SmcTuring.Appendix.Listing8TableResetImage.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8FullTableReset.trace

#print axioms SmcTuring.Appendix.Listing8FullTableReset.effect

#print axioms SmcTuring.Appendix.Listing8FullTableReset.instruction_count

#print axioms SmcTuring.Appendix.Listing8FullTableReset.endpoint

#print axioms SmcTuring.Appendix.Listing8FullTableResetValues.failure_condition

#print axioms SmcTuring.Appendix.Listing8FullTableResetValues.input_cursor

#print axioms SmcTuring.Appendix.Listing8FullTableResetValues.transition_cursor

#print axioms SmcTuring.Appendix.Listing8FullTableResetValues.registers

#print axioms SmcTuring.Appendix.Listing8FullTableResetValues.terminal_boundary

#print axioms SmcTuring.Appendix.Listing8FullTableRun.run

#print axioms SmcTuring.Appendix.Listing8GraphLayout.table_before_input

#print axioms SmcTuring.Appendix.Listing8GraphLayout.transition_lower

#print axioms SmcTuring.Appendix.Listing8GraphLayout.transition_upper

#print axioms SmcTuring.Appendix.Listing8GraphLayout.node_lower

#print axioms SmcTuring.Appendix.Listing8GraphLayout.node_upper

#print axioms SmcTuring.Appendix.Listing8GraphLayout.transition_capacity

#print axioms SmcTuring.Appendix.Listing8GraphLayout.node_capacity

#print axioms SmcTuring.Appendix.Listing8GraphLayout.table_node_apart

#print axioms SmcTuring.Appendix.Listing8GraphLayout.nodes_apart

#print axioms SmcTuring.Appendix.Listing8GraphLayout.transitions_apart

#print axioms SmcTuring.Appendix.Listing8GraphReset.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphReset.capacity

#print axioms SmcTuring.Appendix.Listing8GraphReset.valid

#print axioms SmcTuring.Appendix.Listing8GraphReset.actual_region

#print axioms SmcTuring.Appendix.Listing8GraphReset.actual_valid

#print axioms SmcTuring.Appendix.Listing8SourceGraph.table_length

#print axioms SmcTuring.Appendix.Listing8SourceGraph.lookup

#print axioms SmcTuring.Appendix.Listing8SourceGraph.selected

#print axioms SmcTuring.Appendix.Listing8GraphPointers.node_capacity

#print axioms SmcTuring.Appendix.Listing8GraphPointers.rule_capacity

#print axioms SmcTuring.Appendix.Listing8GraphPointers.node_toNat

#print axioms SmcTuring.Appendix.Listing8GraphPointers.rule_toNat

#print axioms SmcTuring.Appendix.Listing8GraphPointers.state_capacity

#print axioms SmcTuring.Appendix.Listing8GraphPointers.state_toNat

#print axioms SmcTuring.Appendix.Listing8GraphPointers.next_capacity

#print axioms SmcTuring.Appendix.Listing8GraphPointers.next_toNat

#print axioms SmcTuring.Appendix.Listing8GraphPointers.node_monotone

#print axioms SmcTuring.Appendix.Listing8GraphPointers.rule_monotone

#print axioms SmcTuring.Appendix.Listing8GraphPointers.node_outside

#print axioms SmcTuring.Appendix.Listing8GraphPointers.next_after

#print axioms SmcTuring.Appendix.Listing8GraphPointers.state_outside

#print axioms SmcTuring.Appendix.Listing8GraphPointers.transition_bounds

#print axioms SmcTuring.Appendix.Listing8GraphTableBounds.valid_from_lookup

#print axioms SmcTuring.Appendix.Listing8GraphTableBounds.declarations_valid

#print axioms SmcTuring.Appendix.Listing8GraphTableBounds.table_bounds

#print axioms SmcTuring.Appendix.Listing8GraphTableBounds.reset_bounds

#print axioms SmcTuring.Appendix.Listing8NodeBlock.contiguous

#print axioms SmcTuring.Appendix.Listing8NodeBlock.total

#print axioms SmcTuring.Appendix.Listing8NodeBlock.valid

#print axioms SmcTuring.Appendix.Listing8NodeBlock.current

#print axioms SmcTuring.Appendix.Listing8NodeBlock.trace

#print axioms SmcTuring.Appendix.Listing8NodeBlock.result

#print axioms SmcTuring.Appendix.Listing8NodeBlock.instruction_count

#print axioms SmcTuring.Appendix.Listing8NodeTable.bytes_length

#print axioms SmcTuring.Appendix.Listing8NodeTable.endpoint

#print axioms SmcTuring.Appendix.Listing8NodeTable.initial_image

#print axioms SmcTuring.Appendix.Listing8NodeTable.head_current

#print axioms SmcTuring.Appendix.Listing8NodeTable.tail_current

#print axioms SmcTuring.Appendix.Listing8NodeTable.selected_current

#print axioms SmcTuring.Appendix.Listing8NodeTable.selected_overlay

#print axioms SmcTuring.Appendix.Listing8NodeTable.selected_bounds

#print axioms SmcTuring.Appendix.Listing8NodeTrace.result

#print axioms SmcTuring.Appendix.Listing8NodeTrace.trace

#print axioms SmcTuring.Appendix.Listing8NodeTrace.instruction_count

#print axioms SmcTuring.Appendix.Listing8NodeTrace.reusable

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.length

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.lookup

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.initial

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.current

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.fields

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.source_overlay

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.node_bounds

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.valid_from_lookup

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.valid

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.trace

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphNodeImage.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.code_before_table

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.node_after_table

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.state_after_table

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.next_after_table

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.graph

#print axioms SmcTuring.Appendix.Listing8GraphOwnerBounds.bounds

#print axioms SmcTuring.Appendix.Listing8GraphRun.chosen_iff

#print axioms SmcTuring.Appendix.Listing8GraphRun.halt_condition

#print axioms SmcTuring.Appendix.Listing8GraphRun.run

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.prefix_length

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.shape

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.symbol_bytes

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.windows

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.current

#print axioms SmcTuring.Appendix.Listing8LiveNodePacket.initial_from_packets

#print axioms SmcTuring.Appendix.Listing8FullTableNodeFrames.window

#print axioms SmcTuring.Appendix.Listing8FullTableNodeFrames.tape

#print axioms SmcTuring.Appendix.Listing8GraphInputContext.owners

#print axioms SmcTuring.Appendix.Listing8GraphInputContext.reset_bounds

#print axioms SmcTuring.Appendix.Listing8GraphInputInitial.call_before_input

#print axioms SmcTuring.Appendix.Listing8GraphInputInitial.extra_window

#print axioms SmcTuring.Appendix.Listing8GraphInputInitial.source_current

#print axioms SmcTuring.Appendix.Listing8GraphInputInitial.other_current

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.length

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.lookup

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.after_node

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.window

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.source_current

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.other_current

#print axioms SmcTuring.Appendix.Listing8GraphBodyNodes.current

#print axioms SmcTuring.Appendix.Listing8GraphResetNodes.current

#print axioms SmcTuring.Appendix.Listing8GraphResetNodes.initial

#print axioms SmcTuring.Appendix.Listing8GraphResetNodes.node_bounds

#print axioms SmcTuring.Appendix.Listing8GraphResetNodes.valid

#print axioms SmcTuring.Appendix.Listing8GraphResetNodes.fields

#print axioms SmcTuring.Appendix.Listing8GraphInputRun.entry

#print axioms SmcTuring.Appendix.Listing8GraphInputRun.trace

#print axioms SmcTuring.Appendix.Listing8GraphInputRun.result

#print axioms SmcTuring.Appendix.Listing8GraphInputRun.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphInputRun.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphInputValues.fields

#print axioms SmcTuring.Appendix.Listing8GraphInputValues.cursors

#print axioms SmcTuring.Appendix.Listing8GraphInputValues.registers

#print axioms SmcTuring.Appendix.Listing8GraphInputValues.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8GraphInputValues.run

#print axioms SmcTuring.Native.StringMacroSource.shape

#print axioms SmcTuring.Native.StringMacroSource.tail_length

#print axioms SmcTuring.Native.StringMacroSource.windows

#print axioms SmcTuring.Native.StringMacroSource.word_bytes

#print axioms SmcTuring.Native.StringMacroSource.current

#print axioms SmcTuring.Appendix.Listing8GraphStep.scan_pointer

#print axioms SmcTuring.Appendix.Listing8GraphStep.rule_pointer

#print axioms SmcTuring.Appendix.Listing8GraphStep.head_pointer

#print axioms SmcTuring.Appendix.Listing8GraphStep.halted_iff

#print axioms SmcTuring.Appendix.Listing8GraphStep.node_value

#print axioms SmcTuring.Appendix.Listing8GraphStep.node_declarations

#print axioms SmcTuring.Appendix.Listing8GraphStep.node_label

#print axioms SmcTuring.Appendix.Listing8GraphStep.rule_label

#print axioms SmcTuring.Appendix.Listing8GraphStep.native_bounds

#print axioms SmcTuring.Appendix.Listing8GraphStep.transition_bytes

#print axioms SmcTuring.Appendix.Listing8GraphLabels.rule_not_halt

#print axioms SmcTuring.Appendix.Listing8GraphLabels.state_halt_iff

#print axioms SmcTuring.Appendix.Listing8GraphLabels.native_halt_iff

#print axioms SmcTuring.Appendix.Listing8GraphLabels.nonhalt_rule

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.failed_iff

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.nonfailure

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.trace

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.effect

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphBackedge.registers

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeSources.node_current

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeSources.nodes_initial

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeSources.table_current

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeSources.rule_current

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeValues.head_cursor

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeValues.rule_cursor

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeValues.live_membership

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeValues.node_fields

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeValues.rule_fields

#print axioms SmcTuring.Appendix.Listing8GraphCopyResources.input_before_table

#print axioms SmcTuring.Appendix.Listing8GraphCopyResources.input_before_node

#print axioms SmcTuring.Appendix.Listing8GraphCopyResources.input_before_rule

#print axioms SmcTuring.Appendix.Listing8GraphCopyResources.source_resources

#print axioms SmcTuring.Appendix.Listing8GraphCopyResources.resources

#print axioms SmcTuring.Appendix.Listing8MainOwners.patch_after

#print axioms SmcTuring.Appendix.Listing8MainOwners.input_after

#print axioms SmcTuring.Appendix.Listing8MainOwners.owners

#print axioms SmcTuring.Appendix.Listing8MainOwners.pointers

#print axioms SmcTuring.Appendix.Listing8MainGeometry.pointer_targets

#print axioms SmcTuring.Appendix.Listing8MainGeometry.direction_start

#print axioms SmcTuring.Appendix.Listing8MainGeometry.direction_helpers

#print axioms SmcTuring.Appendix.Listing8MainGeometry.direction_packets

#print axioms SmcTuring.Appendix.Listing8MainGeometry.tail_xors

#print axioms SmcTuring.Appendix.Listing8MainGeometry.tail_packets

#print axioms SmcTuring.Appendix.Listing8MainStages.input_outside

#print axioms SmcTuring.Appendix.Listing8MainStages.input

#print axioms SmcTuring.Appendix.Listing8MainStages.direction

#print axioms SmcTuring.Appendix.Listing8MainStages.head

#print axioms SmcTuring.Appendix.Listing8MainState.state_start

#print axioms SmcTuring.Appendix.Listing8MainState.state_helpers

#print axioms SmcTuring.Appendix.Listing8MainState.state_packets

#print axioms SmcTuring.Appendix.Listing8MainState.state

#print axioms SmcTuring.Appendix.Listing8MainState.failure

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.window

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.initially_current

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.header_bounds

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.tail_bounds

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.header

#print axioms SmcTuring.Appendix.Listing8GraphMainFrames.tail

#print axioms SmcTuring.Appendix.Listing8GraphMacroImages.node_current

#print axioms SmcTuring.Appendix.Listing8GraphMacroImages.rule_current

#print axioms SmcTuring.Appendix.Listing8LiveCopies.first_ready

#print axioms SmcTuring.Appendix.Listing8LiveCopies.second_macro

#print axioms SmcTuring.Appendix.Listing8LiveCopies.second_ready

#print axioms SmcTuring.Appendix.Listing8LiveCopies.trace

#print axioms SmcTuring.Appendix.Listing8LiveCopies.effect

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.resources

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.copy_trace

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.trace

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.source_packets

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.effect

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.copied_packets

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphNextCopies.run

#print axioms SmcTuring.Appendix.Listing8GraphNextCopyFrames.window

#print axioms SmcTuring.Appendix.Listing8GraphNextCopyFrames.source_graph

#print axioms SmcTuring.Appendix.Listing8GraphNextCopyFrames.registers

#print axioms SmcTuring.Appendix.Listing8GraphNextCopyFrames.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphPatchBlock.patch_length

#print axioms SmcTuring.Appendix.Listing8GraphPatchBlock.after_backedge

#print axioms SmcTuring.Appendix.Listing8GraphPatchBlock.after_copies

#print axioms SmcTuring.Appendix.Listing8GraphPatchBlock.current

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.patch_trace

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.patched_tape

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.patched_pc

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.last_trace

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.trace

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.principal_effect

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.effect

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.frame

#print axioms SmcTuring.Appendix.Listing8LiveRetarget.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerBounds.direction_before_table

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerBounds.fields

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerBounds.owner_bounds

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerBounds.pointer_copies

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerBounds.boot

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.retarget_trace

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.trace

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.effect

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.registers

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphNextRetarget.instruction_count

#print axioms SmcTuring.Appendix.Listing8LiveOwnerImage.pointer_frame

#print axioms SmcTuring.Appendix.Listing8LiveOwnerImage.original_frame

#print axioms SmcTuring.Appendix.Listing8LiveOwnerImage.current

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerImage.source_packets

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerImage.current

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.owner_trace

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.trace

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.result

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.registers

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.retained_image

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphNextOwners.run

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerFrames.live_frame

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerFrames.window

#print axioms SmcTuring.Appendix.Listing8GraphNextOwnerFrames.source_graph

#print axioms SmcTuring.Appendix.Listing8GapOwners.pointer_targets

#print axioms SmcTuring.Appendix.Listing8GapOwners.pointers

#print axioms SmcTuring.Appendix.Listing8GapGeometry.direction_start

#print axioms SmcTuring.Appendix.Listing8GapGeometry.direction_helpers

#print axioms SmcTuring.Appendix.Listing8GapGeometry.direction_packets

#print axioms SmcTuring.Appendix.Listing8GapGeometry.tail_xors

#print axioms SmcTuring.Appendix.Listing8GapGeometry.tail_packets

#print axioms SmcTuring.Appendix.Listing8GapStages.input_outside

#print axioms SmcTuring.Appendix.Listing8GapStages.direction

#print axioms SmcTuring.Appendix.Listing8GapStages.head

#print axioms SmcTuring.Appendix.Listing8GapState.state_start

#print axioms SmcTuring.Appendix.Listing8GapState.state_helpers

#print axioms SmcTuring.Appendix.Listing8GapState.state_packets

#print axioms SmcTuring.Appendix.Listing8GapState.failure

#print axioms SmcTuring.Appendix.Listing8GraphNextHelperImage.helper_upper

#print axioms SmcTuring.Appendix.Listing8GraphNextHelperImage.after_backedge

#print axioms SmcTuring.Appendix.Listing8GraphNextHelperImage.current

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.helper_bytes

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.pointer_trace

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.trace

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.entry

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.registers

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphNextPointers.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerValues.sources

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerValues.transition_cursor

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerValues.x64_source_halves

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerValues.memory_effect

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.failure_before_table

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.window

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.source_graph

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.source_node

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.tape_symbol

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.owner_cursor

#print axioms SmcTuring.Appendix.Listing8GraphNextPointerFrames.head_cursor

#print axioms SmcTuring.Appendix.Listing8GapStages.input

#print axioms SmcTuring.Appendix.Listing8GapState.state

#print axioms SmcTuring.Appendix.Listing8InputReuseFields.mask_patch

#print axioms SmcTuring.Appendix.Listing8InputReuseFields.pending_spelling

#print axioms SmcTuring.Appendix.Listing8InputReuseFields.pending_position

#print axioms SmcTuring.Appendix.Listing8InputReuseFields.pending_patch

#print axioms SmcTuring.Appendix.Listing8InputReuseFields.head_bytes

#print axioms SmcTuring.Appendix.Listing8InputReuse.completed_image

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.direction_start

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.direction_helpers

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.direction_packets

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.tail_xors

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.tail_packets

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.state_start

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.state_helpers

#print axioms SmcTuring.Appendix.Listing8InputLateGeometry.state_packets

#print axioms SmcTuring.Appendix.Listing8InputBodyFrames.direction

#print axioms SmcTuring.Appendix.Listing8InputBodyFrames.head

#print axioms SmcTuring.Appendix.Listing8InputBodyFrames.state

#print axioms SmcTuring.Appendix.Listing8InputBodyFrames.failure

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeInput.after_input

#print axioms SmcTuring.Appendix.Listing8GraphBackedgeInput.current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputBounds.masks_before_table

#print axioms SmcTuring.Appendix.Listing8GraphNextInputBounds.fields

#print axioms SmcTuring.Appendix.Listing8GraphNextInputBounds.update

#print axioms SmcTuring.Appendix.Listing8GraphNextInputBounds.outside

#print axioms SmcTuring.Appendix.Listing8GraphNextInputImage.after_copies

#print axioms SmcTuring.Appendix.Listing8GraphNextInputImage.after_retargets

#print axioms SmcTuring.Appendix.Listing8GraphNextInputImage.after_owners

#print axioms SmcTuring.Appendix.Listing8GraphNextInputImage.current

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.input_trace

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.trace

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.tape_value

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.endpoint

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.instruction_count

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.registers

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.retained_image

#print axioms SmcTuring.Appendix.Listing8GraphNextInput.endpoint_offset

#print axioms SmcTuring.Appendix.Listing8GraphNextInputFrames.masks

#print axioms SmcTuring.Appendix.Listing8GraphNextInputFrames.window

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.before_current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.source_current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.other_current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.nodes_initial

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.table_current

#print axioms SmcTuring.Appendix.Listing8GraphNextInputNodes.source_graph
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.helper_size
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.xor_size
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.window_span
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.helper_outside
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.packet_outside
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.xor_outside
#print axioms SmcTuring.Appendix.Listing8DirectionWindows.tail_outside
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.state_helpers_outside
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.state_packets_outside
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.direction
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.head
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.state
#print axioms SmcTuring.Appendix.Listing8DirectionBodyFrames.failure
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionBounds.direction_before_table
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionBounds.call_before_table
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionBounds.direction
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionBounds.state
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionBounds.failure
#print axioms SmcTuring.Appendix.Listing8DirectionPrefixFrames.code_before
#print axioms SmcTuring.Appendix.Listing8DirectionPrefixFrames.direction_store_outside
#print axioms SmcTuring.Appendix.Listing8DirectionPrefixFrames.pointer_outside
#print axioms SmcTuring.Appendix.Listing8DirectionPrefixFrames.distribution_outside
#print axioms SmcTuring.Appendix.Listing8DirectionPrefixFrames.input_outside
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionFrames.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionFrames.after_owners
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionFrames.after_pointers
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionFrames.after_input
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionFrames.current
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionImage.helper_current
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionImage.arithmetic_current
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionImage.xor_current
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionImage.tail_current
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.direction_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextDirection.static_window
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.xor_current
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.tail_current
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.head_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextHead.static_window
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.input_frame
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.back_low
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.forward_low
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.back_high
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.forward_high
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionValues.direction
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionSelection.low_result
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionSelection.high_result
#print axioms SmcTuring.Appendix.Listing8GraphNextDirectionSelection.selected
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadEntry.input_mask
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadEntry.mask
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadEntry.input_cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadEntry.cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadValues.head_selection
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadValues.logical_head
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadFrames.direction_window
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadFrames.head_window
#print axioms SmcTuring.Appendix.Listing8GraphNextHeadFrames.source_graph
#print axioms SmcTuring.Appendix.Listing8StateReuseFrames.helper_outside
#print axioms SmcTuring.Appendix.Listing8StateReuseFrames.packet_outside
#print axioms SmcTuring.Appendix.Listing8StateReuseFrames.state
#print axioms SmcTuring.Appendix.Listing8StateReuseFrames.failure
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.code_before
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.after_owners
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.after_pointers
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.after_input
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.current
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.helper_current
#print axioms SmcTuring.Appendix.Listing8GraphNextStateImage.headers_current
#print axioms SmcTuring.Appendix.Listing8GraphNextState.state_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextState.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextState.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextState.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextState.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextState.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextState.static_window
#print axioms SmcTuring.Appendix.Listing8GraphNextStateEntry.new_frame
#print axioms SmcTuring.Appendix.Listing8GraphNextStateEntry.new_low
#print axioms SmcTuring.Appendix.Listing8GraphNextStateEntry.new_high
#print axioms SmcTuring.Appendix.Listing8GraphNextStateEntry.mask
#print axioms SmcTuring.Appendix.Listing8GraphNextStateEntry.cursor
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.from_initial
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.reset_owner
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.owner_effect
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.comparison_entry
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.comparison_image
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.comparison_zero
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.owner_cursor
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.owner_source
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.mismatch
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.comparison_memory
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.store_operand
#print axioms SmcTuring.Appendix.Listing8FailureReuseImage.post_headers
#print axioms SmcTuring.Appendix.Listing8GraphNextStateValues.transition
#print axioms SmcTuring.Appendix.Listing8GraphNextStateValues.state_label
#print axioms SmcTuring.Appendix.Listing8GraphNextStateValues.logical_transition
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.comparison_endpoint
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.trace
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.endpoint
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.memory
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.registers
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.window
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.prefix_window
#print axioms SmcTuring.Appendix.Listing8FailureReuseEffects.current_after
#print axioms SmcTuring.Appendix.Listing8GraphNextStateFrames.window
#print axioms SmcTuring.Appendix.Listing8GraphNextStateFrames.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextStateFrames.head_frame
#print axioms SmcTuring.Appendix.Listing8GraphNextStateFrames.head
#print axioms SmcTuring.Appendix.Listing8FailureReuseTransport.current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.code_before
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.after_owners
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.after_pointers
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.after_input
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.window
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureImage.current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.failure_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.failed_iff
#print axioms SmcTuring.Appendix.Listing8GraphNextFailure.memory_effect
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureFrames.before_window
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureFrames.after_table
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureFrames.transition
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureFrames.head
#print axioms SmcTuring.Appendix.Listing8GraphNextFailureFrames.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.first_nonfailure
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.entry_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.entry_operand
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.call_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextCallImage.call_fetch
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyPrefix.copies
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyPrefix.owners
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyPrefix.pointers
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyBody.input
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyBody.direction
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyBody.head
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyBody.state
#print axioms SmcTuring.Appendix.Listing8GraphNextEarlyBody.failure
#print axioms SmcTuring.Appendix.Listing8GraphNextStackImage.code_current
#print axioms SmcTuring.Appendix.Listing8GraphNextStackImage.stack_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextStackImage.begin_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextStackImage.jump_prefix
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.entry
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.call_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.jump_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.effect
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.saved_stack
#print axioms SmcTuring.Appendix.Listing8GraphNextJump.return_field
#print axioms SmcTuring.Appendix.Listing8JumpReturn.ranges
#print axioms SmcTuring.Appendix.Listing8JumpReturn.placement
#print axioms SmcTuring.Appendix.Listing8JumpReturn.call_shape
#print axioms SmcTuring.Appendix.Listing8JumpReturn.trace
#print axioms SmcTuring.Appendix.Listing8JumpReturn.effect
#print axioms SmcTuring.Appendix.Listing8JumpReturn.instruction_count
#print axioms SmcTuring.Appendix.Listing8JumpReturn.current_after
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.nonfailure
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.current
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.return_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.effect
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.transition
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.head
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.failure_current
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.code_current
#print axioms SmcTuring.Appendix.Listing8GraphNextBegin.control_current
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.code_before
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.after_owners
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.after_pointers
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.after_input
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.state_window
#print axioms SmcTuring.Appendix.Listing8GraphNextLateBody.after_failure
#print axioms SmcTuring.Appendix.Listing8GraphNextFailImage.tail_bounds
#print axioms SmcTuring.Appendix.Listing8GraphNextFailImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextFailImage.current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.failure
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.return_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.effect
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.endpoint_offset
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.transition
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.head
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.failure_current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.code_current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.control_current
#print axioms SmcTuring.Appendix.Listing8GraphNextFailReturn.halt_cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.table_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.result
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.memory_effect
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextTable.head
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.bounds
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.node_after
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.current
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.after_table
#print axioms SmcTuring.Appendix.Listing8GraphNextResetImage.source_value
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.reset_trace
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.effect
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.cursors_before_call
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.input_cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.transition_cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.window
#print axioms SmcTuring.Appendix.Listing8GraphNextReset.reset_current
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.tape_symbol
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.neighbors
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.call_packet
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.call_fetch
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.marker_current
#print axioms SmcTuring.Appendix.Listing8GraphNextResetOutput.bootstrap_current
#print axioms SmcTuring.Appendix.Listing8EntryPackets.stack_packet
#print axioms SmcTuring.Appendix.Listing8EntryPackets.begin_packet
#print axioms SmcTuring.Appendix.Listing8EntryPackets.stptr
#print axioms SmcTuring.Appendix.Listing8EntryPackets.return_field
#print axioms SmcTuring.Appendix.Listing8GraphNextResetControl.jump_prefix
#print axioms SmcTuring.Appendix.Listing8GraphNextResetControl.current
#print axioms SmcTuring.Appendix.Listing8GraphNextResetControl.stack_fields
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.nonhalt
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.trace
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.registers
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.source_graph
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.control_current
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.head_cursor
#print axioms SmcTuring.Appendix.Listing8GraphNextControl.transition_cursor
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.macro_current
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.macro_source
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.macro_from_packet
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.from_packets
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.node_current
#print axioms SmcTuring.Appendix.Listing8MainCopyImage.rule_current
#print axioms SmcTuring.Appendix.Listing8MainCopies.trace
#print axioms SmcTuring.Appendix.Listing8MainCopies.effect
#print axioms SmcTuring.Appendix.Listing8MainCopies.window
#print axioms SmcTuring.Appendix.Listing8MainCopies.exterior_window
#print axioms SmcTuring.Appendix.Listing8MainCopies.source_packets
#print axioms SmcTuring.Appendix.Listing8MainCopies.copied_packets
#print axioms SmcTuring.Appendix.Listing8MainCopies.patches
#print axioms SmcTuring.Appendix.Listing8MainCopies.retarget_current
#print axioms SmcTuring.Appendix.Listing8MainCopies.registers
#print axioms SmcTuring.Appendix.Listing8MainCopies.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainRetarget.retarget_trace
#print axioms SmcTuring.Appendix.Listing8MainRetarget.trace
#print axioms SmcTuring.Appendix.Listing8MainRetarget.effect
#print axioms SmcTuring.Appendix.Listing8MainRetarget.registers
#print axioms SmcTuring.Appendix.Listing8MainRetarget.owner_current
#print axioms SmcTuring.Appendix.Listing8MainRetarget.window
#print axioms SmcTuring.Appendix.Listing8MainRetarget.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.owner_trace
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.trace
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.result
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.registers
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.retained_image
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.window
#print axioms SmcTuring.Appendix.Listing8MainLiveOwners.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainPrefix.helper_current
#print axioms SmcTuring.Appendix.Listing8MainPrefix.pointer_trace
#print axioms SmcTuring.Appendix.Listing8MainPrefix.trace
#print axioms SmcTuring.Appendix.Listing8MainPrefix.stack_trace
#print axioms SmcTuring.Appendix.Listing8MainPrefix.entry
#print axioms SmcTuring.Appendix.Listing8MainPrefix.registers
#print axioms SmcTuring.Appendix.Listing8MainPrefix.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainPrefixFrames.window
#print axioms SmcTuring.Appendix.Listing8MainPrefixFrames.before_patch
#print axioms SmcTuring.Appendix.Listing8MainPrefixFrames.head_cursor
#print axioms SmcTuring.Appendix.Listing8MainPrefixFrames.patches_current
#print axioms SmcTuring.Appendix.Listing8MainInputImage.after_copies
#print axioms SmcTuring.Appendix.Listing8MainInputImage.after_retargets
#print axioms SmcTuring.Appendix.Listing8MainInputImage.after_owners
#print axioms SmcTuring.Appendix.Listing8MainInputImage.current
#print axioms SmcTuring.Appendix.Listing8MainPrefixSources.node_current
#print axioms SmcTuring.Appendix.Listing8MainPrefixSources.tape_symbol
#print axioms SmcTuring.Appendix.Listing8MainInput.input_trace
#print axioms SmcTuring.Appendix.Listing8MainInput.trace
#print axioms SmcTuring.Appendix.Listing8MainInput.stack_trace
#print axioms SmcTuring.Appendix.Listing8MainInput.tape_value
#print axioms SmcTuring.Appendix.Listing8MainInput.endpoint
#print axioms SmcTuring.Appendix.Listing8MainInput.registers
#print axioms SmcTuring.Appendix.Listing8MainInput.retained_image
#print axioms SmcTuring.Appendix.Listing8MainInput.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainGraphImage.source_packets
#print axioms SmcTuring.Appendix.Listing8MainGraphImage.input_current
#print axioms SmcTuring.Appendix.Listing8MainGraphImage.trace
#print axioms SmcTuring.Appendix.Listing8MainGraphImage.tape_value
#print axioms SmcTuring.Appendix.Listing8MainGraphTable.bytes_ofFn_congr
#print axioms SmcTuring.Appendix.Listing8MainGraphTable.updated_table_bytes
#print axioms SmcTuring.Appendix.Listing8MainGraphTable.updated_table_current
#print axioms SmcTuring.Appendix.Listing8MainGraphBackedgeEntry.current
#print axioms SmcTuring.Appendix.Listing8MainGraphBackedgeEntry.bounds
#print axioms SmcTuring.Appendix.Listing8MainGraphBackedgeEntry.generic_trace
#print axioms SmcTuring.Appendix.Listing8MainGraphBackedgeEntry.trace
#print axioms SmcTuring.Appendix.Listing8MainGraphBackedgeEntry.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainInputFrames.input_window
#print axioms SmcTuring.Appendix.Listing8MainInputFrames.before_patch
#print axioms SmcTuring.Appendix.Listing8MainInputFrames.head_cursor
#print axioms SmcTuring.Appendix.Listing8MainInputFrames.patches_current
#print axioms SmcTuring.Appendix.Listing8MainInputMacroWindows.header
#print axioms SmcTuring.Appendix.Listing8MainInputMacroWindows.tail
#print axioms SmcTuring.Appendix.Listing8MainInputMacroWindows.node_current
#print axioms SmcTuring.Appendix.Listing8MainGraphPrefix.bounds
#print axioms SmcTuring.Appendix.Listing8MainGraphPrefix.window
#print axioms SmcTuring.Appendix.Listing8MainGraphPrefix.source_graph
#print axioms SmcTuring.Appendix.Listing8MainGraphPrefix.input_window
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.before_current
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.source_current
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.other_current
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.current
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.nodes_initial
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.table_current
#print axioms SmcTuring.Appendix.Listing8MainGraphInputNodes.source_graph
#print axioms SmcTuring.Appendix.Listing8MainGraphInput.correct
#print axioms SmcTuring.Appendix.Listing8MainGraphInput.tape_symbol
#print axioms SmcTuring.Appendix.Listing8MainGraphInput.neighbors
#print axioms SmcTuring.Appendix.Listing8MainGraphInput.macro_current
#print axioms SmcTuring.Appendix.Listing8LoopDirectionImage.helper_member
#print axioms SmcTuring.Appendix.Listing8LoopDirectionImage.arithmetic_member
#print axioms SmcTuring.Appendix.Listing8LoopDirectionImage.xor_member
#print axioms SmcTuring.Appendix.Listing8LoopDirectionImage.tail_member
#print axioms SmcTuring.Appendix.Listing8LoopDirectionImage.transport
#print axioms SmcTuring.Appendix.Listing8LoopDirectionPrefix.prefix_window
#print axioms SmcTuring.Appendix.Listing8LoopDirectionPrefix.input_window
#print axioms SmcTuring.Appendix.Listing8LoopDirectionPrefix.window
#print axioms SmcTuring.Appendix.Listing8LoopDirectionPrefix.current_after_input
#print axioms SmcTuring.Appendix.Listing8LoopPointerValues.sources
#print axioms SmcTuring.Appendix.Listing8LoopPointerValues.transition_cursor
#print axioms SmcTuring.Appendix.Listing8LoopPointerValues.x64_source_halves
#print axioms SmcTuring.Appendix.Listing8LoopPointerValues.memory_effect
#print axioms SmcTuring.Appendix.Listing8LoopDirection.direction_trace
#print axioms SmcTuring.Appendix.Listing8LoopDirection.trace
#print axioms SmcTuring.Appendix.Listing8LoopDirection.stack_trace
#print axioms SmcTuring.Appendix.Listing8LoopDirection.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopDirection.registers
#print axioms SmcTuring.Appendix.Listing8LoopDirection.window
#print axioms SmcTuring.Appendix.Listing8LoopDirection.current_after
#print axioms SmcTuring.Appendix.Listing8LoopDirection.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.input_frame
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.back_low
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.forward_low
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.back_high
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.forward_high
#print axioms SmcTuring.Appendix.Listing8LoopDirectionValues.direction
#print axioms SmcTuring.Appendix.Listing8LoopDirectionSelection.low_result
#print axioms SmcTuring.Appendix.Listing8LoopDirectionSelection.high_result
#print axioms SmcTuring.Appendix.Listing8LoopDirectionSelection.selected
#print axioms SmcTuring.Appendix.Listing8LoopHead.head_trace
#print axioms SmcTuring.Appendix.Listing8LoopHead.trace
#print axioms SmcTuring.Appendix.Listing8LoopHead.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopHead.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopHead.registers
#print axioms SmcTuring.Appendix.Listing8LoopHead.static_window
#print axioms SmcTuring.Appendix.Listing8LoopHead.current_after
#print axioms SmcTuring.Appendix.Listing8LoopHead.stack_trace
#print axioms SmcTuring.Appendix.Listing8LoopHeadEntry.input_mask
#print axioms SmcTuring.Appendix.Listing8LoopHeadEntry.mask
#print axioms SmcTuring.Appendix.Listing8LoopHeadEntry.input_cursor
#print axioms SmcTuring.Appendix.Listing8LoopHeadEntry.cursor
#print axioms SmcTuring.Appendix.Listing8LoopHeadValues.head_selection
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeImage.helper_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeImage.arithmetic_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeImage.xor_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeImage.tail_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeImage.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.input_current
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.direction_window
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.head_window
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopGraphHead.correct
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.generic_trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeHead.retained_fragments
#print axioms SmcTuring.Appendix.Listing8LoopStateImage.helper_member
#print axioms SmcTuring.Appendix.Listing8LoopStateImage.header_member
#print axioms SmcTuring.Appendix.Listing8LoopStateImage.transport
#print axioms SmcTuring.Appendix.Listing8LoopStatePrefix.code_before
#print axioms SmcTuring.Appendix.Listing8LoopStatePrefix.prefix_window
#print axioms SmcTuring.Appendix.Listing8LoopStatePrefix.head_window
#print axioms SmcTuring.Appendix.Listing8LoopStatePrefix.window
#print axioms SmcTuring.Appendix.Listing8LoopStatePrefix.current_after_head
#print axioms SmcTuring.Appendix.Listing8LoopState.state_trace
#print axioms SmcTuring.Appendix.Listing8LoopState.trace
#print axioms SmcTuring.Appendix.Listing8LoopState.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopState.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopState.registers
#print axioms SmcTuring.Appendix.Listing8LoopState.static_window
#print axioms SmcTuring.Appendix.Listing8LoopState.current_after
#print axioms SmcTuring.Appendix.Listing8LoopState.stack_trace
#print axioms SmcTuring.Appendix.Listing8LoopStateEntry.new_frame
#print axioms SmcTuring.Appendix.Listing8LoopStateEntry.new_low
#print axioms SmcTuring.Appendix.Listing8LoopStateEntry.new_high
#print axioms SmcTuring.Appendix.Listing8LoopStateEntry.mask
#print axioms SmcTuring.Appendix.Listing8LoopStateEntry.cursor
#print axioms SmcTuring.Appendix.Listing8LoopStateValues.transition
#print axioms SmcTuring.Appendix.Listing8LoopStateFrames.head_frame
#print axioms SmcTuring.Appendix.Listing8LoopStateFrames.direction_fragments
#print axioms SmcTuring.Appendix.Listing8LoopStateFrames.window
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeStateImage.helper_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeStateImage.headers_current
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeStateImage.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.input_current
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.window
#print axioms SmcTuring.Appendix.Listing8LoopGraphState.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.generic_trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.retained_fragments
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeState.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopFailurePrefix.code_before
#print axioms SmcTuring.Appendix.Listing8LoopFailurePrefix.prefix_window
#print axioms SmcTuring.Appendix.Listing8LoopFailurePrefix.window
#print axioms SmcTuring.Appendix.Listing8LoopFailurePrefix.current_after_state
#print axioms SmcTuring.Appendix.Listing8LoopFailure.failure_trace
#print axioms SmcTuring.Appendix.Listing8LoopFailure.trace
#print axioms SmcTuring.Appendix.Listing8LoopFailure.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopFailure.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopFailure.registers
#print axioms SmcTuring.Appendix.Listing8LoopFailure.memory_effect
#print axioms SmcTuring.Appendix.Listing8LoopFailure.current_after
#print axioms SmcTuring.Appendix.Listing8LoopFailure.window
#print axioms SmcTuring.Appendix.Listing8LoopFailure.stack_trace
#print axioms SmcTuring.Appendix.Listing8LoopFailureFrames.before_window
#print axioms SmcTuring.Appendix.Listing8LoopFailureFrames.direction_fragments
#print axioms SmcTuring.Appendix.Listing8LoopFailureFrames.state_fragments
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.input_current
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.failed_iff
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.after_table
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopGraphFailure.correct
#print axioms SmcTuring.Appendix.Listing8LoopCallImage.entry_packet
#print axioms SmcTuring.Appendix.Listing8LoopCallImage.entry_operand
#print axioms SmcTuring.Appendix.Listing8LoopCallImage.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopCallImage.call_fetch
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.bounds
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.generic_trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.retained_fragments
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.failed_iff
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure.call_fetch
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.main_prefix
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.input
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.direction
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.head
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.state
#print axioms SmcTuring.Appendix.Listing8LoopEarlyFrames.failure
#print axioms SmcTuring.Appendix.Listing8LoopLateFrames.state_window
#print axioms SmcTuring.Appendix.Listing8LoopLateFrames.failure_window
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.entry_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.stack_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.begin_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.prefix_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.fail_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlImage.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopControl.current
#print axioms SmcTuring.Appendix.Listing8LoopControl.entry
#print axioms SmcTuring.Appendix.Listing8LoopControl.target_capacity
#print axioms SmcTuring.Appendix.Listing8LoopControl.return_trace
#print axioms SmcTuring.Appendix.Listing8LoopControl.trace
#print axioms SmcTuring.Appendix.Listing8LoopControl.target_endpoint
#print axioms SmcTuring.Appendix.Listing8LoopControl.effect
#print axioms SmcTuring.Appendix.Listing8LoopControl.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopControl.memory
#print axioms SmcTuring.Appendix.Listing8LoopControl.registers
#print axioms SmcTuring.Appendix.Listing8LoopControl.failed_iff
#print axioms SmcTuring.Appendix.Listing8LoopControl.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.direction_fragments
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.state_fragments
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.failure_fragments
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.entry_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.prefix_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.fail_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlFrames.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopControlCases.nonfailure
#print axioms SmcTuring.Appendix.Listing8LoopControlCases.failure
#print axioms SmcTuring.Appendix.Listing8LoopControlCases.nonhalt_effect
#print axioms SmcTuring.Appendix.Listing8LoopControlCases.halt_effect
#print axioms SmcTuring.Appendix.Listing8LoopControlCases.halt_cursor
#print axioms SmcTuring.Appendix.Listing8LoopGraphContext.next
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeControlImage.entry_packet
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeControlImage.prefix_packet
#print axioms SmcTuring.Appendix.Listing8LoopBackedgeControlImage.current
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.generic_trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.trace
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.failed_iff
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopGraphBackedgeControl.registers
#print axioms SmcTuring.Appendix.Listing8LoopPrefixBodyFrames.direction
#print axioms SmcTuring.Appendix.Listing8LoopPrefixBodyFrames.head
#print axioms SmcTuring.Appendix.Listing8LoopPrefixBodyFrames.state_window
#print axioms SmcTuring.Appendix.Listing8LoopPrefixBodyFrames.failure
#print axioms SmcTuring.Appendix.Listing8LoopControlMacros.header
#print axioms SmcTuring.Appendix.Listing8LoopControlMacros.tail
#print axioms SmcTuring.Appendix.Listing8LoopControlMacros.node_current
#print axioms SmcTuring.Appendix.Listing8LoopControlMacros.rule_current
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.direction_start
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.direction_helpers
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.direction_packets
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.tail_xors
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.tail_packets
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.state_start
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.state_helpers
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyGeometry.state_packets
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyFrames.direction
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyFrames.head
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyFrames.state_window
#print axioms SmcTuring.Appendix.Listing8LoopInputBodyFrames.failure
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.cursors_before_code
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.patches_current
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.helpers_after_prefix
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.helpers_after_input
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.helpers_current
#print axioms SmcTuring.Appendix.Listing8LoopControlReentryFields.input_current
#print axioms SmcTuring.Appendix.Listing8LoopReentry.main_current
#print axioms SmcTuring.Appendix.Listing8LoopReentry.current
#print axioms SmcTuring.Appendix.Listing8LoopReentry.exists_next
#print axioms SmcTuring.Appendix.Listing8LoopIteration.execute
#print axioms SmcTuring.Appendix.Listing8LoopIterationAnchor.execute
#print axioms SmcTuring.Appendix.Listing8LoopIterationTables.table_bytes
#print axioms SmcTuring.Appendix.Listing8LoopIterationTables.execute
#print axioms SmcTuring.Appendix.Listing8LoopIterationTables.original_execute
#print axioms SmcTuring.Appendix.Listing8LoopTable.table_entry
#print axioms SmcTuring.Appendix.Listing8LoopTable.table_trace
#print axioms SmcTuring.Appendix.Listing8LoopTable.trace
#print axioms SmcTuring.Appendix.Listing8LoopTable.result
#print axioms SmcTuring.Appendix.Listing8LoopTable.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopTable.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopTable.registers
#print axioms SmcTuring.Appendix.Listing8LoopTable.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopTable.logical_head
#print axioms SmcTuring.Appendix.Listing8LoopTable.logical_transition
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.region_next
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.after_control
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.after_control_source
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.after_table
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.after_table_source
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.reentry
#print axioms SmcTuring.Appendix.Listing8LoopHaltImage.after_backedge
#print axioms SmcTuring.Appendix.Listing8LoopReset.reset_trace
#print axioms SmcTuring.Appendix.Listing8LoopReset.trace
#print axioms SmcTuring.Appendix.Listing8LoopReset.effect
#print axioms SmcTuring.Appendix.Listing8LoopReset.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopReset.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopReset.registers
#print axioms SmcTuring.Appendix.Listing8LoopReset.input_cursor
#print axioms SmcTuring.Appendix.Listing8LoopReset.transition_cursor
#print axioms SmcTuring.Appendix.Listing8LoopReset.window
#print axioms SmcTuring.Appendix.Listing8LoopReset.reset_current
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.tape_symbol
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.neighbors
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.all_symbols
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.logical_head_output
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.call_fetch
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.marker_current
#print axioms SmcTuring.Appendix.Listing8LoopResetOutput.bootstrap_current
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.input_entry
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.input_trace
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.trace
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.result
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.registers
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.all_symbols
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.logical_head_output
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.reset_cursors
#print axioms SmcTuring.Appendix.Listing8LoopTerminal.call_packet
#print axioms SmcTuring.Appendix.Listing8LoopHaltIteration.execute
#print axioms SmcTuring.Appendix.Listing8LoopInterpreter.execute
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterAnchor.execute
#print axioms SmcTuring.Appendix.Listing8LoopFirstHaltFrames.window
#print axioms SmcTuring.Appendix.Listing8LoopFirstHaltFrames.rules
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.initial_same
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.input_entry
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.input_trace
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.trace
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.result
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.endpoint
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.registers
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.source_graph
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.tape_symbol
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.all_symbols
#print axioms SmcTuring.Appendix.Listing8LoopFirstHalt.logical_head_output
#print axioms SmcTuring.Appendix.Listing8LoopOriginalInterpreter.execute
#print axioms SmcTuring.Appendix.Listing8LoopTailGeometry.input_before_end
#print axioms SmcTuring.Appendix.Listing8LoopTailGeometry.call_before_end
#print axioms SmcTuring.Appendix.Listing8LoopTailGeometry.source_node_before_end
#print axioms SmcTuring.Appendix.Listing8LoopTailGeometry.source_rule_before_end
#print axioms SmcTuring.Appendix.Listing8LoopTailFrames.control
#print axioms SmcTuring.Appendix.Listing8LoopTailFrames.terminal
#print axioms SmcTuring.Appendix.Listing8LoopTailIteration.execute
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterTail.counts
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterTail.execute
#print axioms SmcTuring.Appendix.Listing8LoopOriginalTailFrames.initial_window
#print axioms SmcTuring.Appendix.Listing8LoopOriginalTailFrames.body_window
#print axioms SmcTuring.Appendix.Listing8LoopOriginalTailFrames.backedge_window
#print axioms SmcTuring.Appendix.Listing8LoopOriginalTailFrames.first_halt_window
#print axioms SmcTuring.Appendix.Listing8LoopOriginalInterpreterTail.execute
#print axioms SmcTuring.Appendix.Listing8LoopOriginalImage.initial_memory
#print axioms SmcTuring.Appendix.Listing8LoopOriginalImage.patch_point
#print axioms SmcTuring.Appendix.Listing8LoopOriginalImage.image_point
#print axioms SmcTuring.Appendix.Listing8LoopOriginalImage.point_after
#print axioms SmcTuring.Appendix.Listing8LoopOriginalImage.image_put_word
#print axioms SmcTuring.Appendix.Listing8AccumulatorEntry.state_ext
#print axioms SmcTuring.Appendix.Listing8AccumulatorEntry.saved_eq
#print axioms SmcTuring.Appendix.Listing8AccumulatorEntry.trace
#print axioms SmcTuring.Native.AccumulatorFinalization.body
#print axioms SmcTuring.Appendix.Listing8AccumulatorExit.trace
#print axioms SmcTuring.Appendix.Listing8AccumulatorExit.effect
#print axioms SmcTuring.Appendix.Listing8AccumulatorRestored.execute
#print axioms SmcTuring.Appendix.Listing9EarlyImage.overlay_window
#print axioms SmcTuring.Appendix.Listing9EarlyImage.input_after_origin
#print axioms SmcTuring.Appendix.Listing9EarlyImage.sites_after_origin
#print axioms SmcTuring.Appendix.Listing9EarlyImage.initial_window
#print axioms SmcTuring.Appendix.Listing9PackedLayout.positions
#print axioms SmcTuring.Appendix.Listing9PackedLayout.bounds_order
#print axioms SmcTuring.Appendix.Listing9PackedLayout.admissible
#print axioms SmcTuring.Appendix.Listing9PackedLayout.owner_capacity
#print axioms SmcTuring.Appendix.Listing9Image.prologue
#print axioms SmcTuring.Appendix.Listing9Image.prologue_before_epilogue
#print axioms SmcTuring.Appendix.Listing9Image.epilogue_current
#print axioms SmcTuring.Appendix.Listing9Image.later_window
#print axioms SmcTuring.Appendix.Listing9Image.save_current
#print axioms SmcTuring.Appendix.Listing9Image.pointer_current
#print axioms SmcTuring.Appendix.Listing9Image.initial_values
#print axioms SmcTuring.Appendix.Listing9Execution.prologue_current
#print axioms SmcTuring.Appendix.Listing9Execution.execute
#print axioms SmcTuring.Appendix.Listing9SelfReader.trace
#print axioms SmcTuring.Appendix.Listing9SelfDeclaration.x64_forms
#print axioms SmcTuring.Appendix.Listing9SelfDeclaration.x64_bytes
#print axioms SmcTuring.Appendix.Listing9SelfDeclaration.trace
#print axioms SmcTuring.Appendix.Listing9SelfDeclaration.effect
#print axioms SmcTuring.Appendix.Listing9PatchWindows.patch_window
#print axioms SmcTuring.Appendix.Listing9PatchWindows.overwrite
#print axioms SmcTuring.Appendix.Listing9PatchWindows.word_overwrite
#print axioms SmcTuring.Appendix.Listing9FinalImage.execute
#print axioms SmcTuring.Appendix.Listing9ExecutionImage.prologue_current
#print axioms SmcTuring.Appendix.Listing9ExecutionImage.execute
#print axioms SmcTuring.Appendix.Listing9MetadataPackets.save_current
#print axioms SmcTuring.Appendix.Listing9MetadataPackets.pointer_current
#print axioms SmcTuring.Appendix.Listing9MetadataPackets.save_value
#print axioms SmcTuring.Appendix.Listing9Fields.operand_field
#print axioms SmcTuring.Appendix.Listing9Fields.save_field
#print axioms SmcTuring.Appendix.Listing9Fields.pointer_field
#print axioms SmcTuring.Appendix.Listing9Fields.x86_header_not_operand
#print axioms SmcTuring.Appendix.Listing9Fields.corrected_pointer
#print axioms SmcTuring.Native.StringWrites.string_memory
#print axioms SmcTuring.Native.StringWrites.mixed_memory
#print axioms SmcTuring.Native.StringWrites.dword_memory
#print axioms SmcTuring.Native.StringWrites.control_memory
#print axioms SmcTuring.Native.StringWrites.execute_memory
#print axioms SmcTuring.Native.StringWrites.code_write_nonempty
#print axioms SmcTuring.Native.StringWrites.code_write_bytes
#print axioms SmcTuring.Native.StringWrites.execute_frame
#print axioms SmcTuring.Native.StringWrites.run_append
#print axioms SmcTuring.Native.StringWrites.run_lift_string
#print axioms SmcTuring.Native.StringWrites.trace_run_eq
#print axioms SmcTuring.Native.StringWrites.owned_run_append
#print axioms SmcTuring.Native.StringWrites.run_frame
#print axioms SmcTuring.Native.StringWrites.native_code_write
#print axioms SmcTuring.Native.StringWrites.native_owned_run
#print axioms SmcTuring.Appendix.Listing9Storage.current_of_retained
#print axioms SmcTuring.Appendix.Listing9Storage.after_save_effect
#print axioms SmcTuring.Appendix.Listing9Storage.pointer_entry
#print axioms SmcTuring.Appendix.Listing9Storage.trace
#print axioms SmcTuring.Appendix.Listing9Storage.effect
#print axioms SmcTuring.Appendix.Listing9Storage.instruction_count
#print axioms SmcTuring.Appendix.Listing9FullExecution.execute
#print axioms SmcTuring.Appendix.Listing9Fallthrough.save_positive
#print axioms SmcTuring.Appendix.Listing9Fallthrough.save_fits
#print axioms SmcTuring.Appendix.Listing9Fallthrough.encoded_save_nonzero
#print axioms SmcTuring.Appendix.Listing9Fallthrough.x64_preserved_iff
#print axioms SmcTuring.Appendix.Listing9Fallthrough.zero_seed_trace
#print axioms SmcTuring.Appendix.Listing9DeclarationWrites.owned
#print axioms SmcTuring.Appendix.Listing9StorageWrites.fields
#print axioms SmcTuring.Appendix.Listing9StorageWrites.owned
#print axioms SmcTuring.Appendix.Listing9FullStorageWrites.execute
#print axioms SmcTuring.Appendix.Listing9SurroundWrites.fields
#print axioms SmcTuring.Appendix.Listing9SurroundWrites.prologue
#print axioms SmcTuring.Appendix.Listing9SurroundWrites.epilogue
#print axioms SmcTuring.Appendix.Listing9BodyExitWrites.execute
#print axioms SmcTuring.Native.StringFieldWrites.word_owned
#print axioms SmcTuring.Native.StringFieldWrites.exchange
#print axioms SmcTuring.Native.StringFieldWrites.exchange_pc
#print axioms SmcTuring.Native.StringFieldWrites.subtract_address
#print axioms SmcTuring.Native.StringFieldWrites.subtract_size
#print axioms SmcTuring.Native.StringFieldWrites.subtract
#print axioms SmcTuring.Native.StringMoveWrites.move
#print axioms SmcTuring.Native.StringMoveWrites.owned
#print axioms SmcTuring.Native.StringRestoreWrites.owned
#print axioms SmcTuring.Appendix.Listing8SetupWrites.source
#print axioms SmcTuring.Appendix.Listing8SetupWrites.owned
#print axioms SmcTuring.Appendix.Listing8MacroWriteBounds.fields
#print axioms SmcTuring.Appendix.Listing8MacroWriteBounds.buffers
#print axioms SmcTuring.Appendix.Listing8MacroWriteBounds.copied_bounds
#print axioms SmcTuring.Appendix.Listing8MacroWrites.setup
#print axioms SmcTuring.Appendix.Listing8MacroWrites.moves
#print axioms SmcTuring.Appendix.Listing8MacroWrites.destination_endpoint
#print axioms SmcTuring.Appendix.Listing8MacroWrites.restores
#print axioms SmcTuring.Appendix.Listing8MacroWrites.owned
#print axioms SmcTuring.Appendix.Listing8CopyWriteBounds.spans
#print axioms SmcTuring.Appendix.Listing8CopyWriteBounds.node
#print axioms SmcTuring.Appendix.Listing8CopyWriteBounds.transition
#print axioms SmcTuring.Appendix.Listing8CopyWrites.owned
#print axioms SmcTuring.Appendix.Listing8CopyWrites.copies
#print axioms SmcTuring.Appendix.Listing8GraphCopyWriteBounds.lower
#print axioms SmcTuring.Appendix.Listing8GraphCopyWriteBounds.copy_before_call
#print axioms SmcTuring.Appendix.Listing8GraphCopyWriteBounds.placement
#print axioms SmcTuring.Appendix.Listing8GraphCopyWrites.body_entry
#print axioms SmcTuring.Appendix.Listing8GraphCopyWrites.copies
#print axioms SmcTuring.Appendix.Listing8GraphCopyWrites.execute
#print axioms SmcTuring.Native.StringStoreWrites.address
#print axioms SmcTuring.Native.StringStoreWrites.length
#print axioms SmcTuring.Native.StringStoreWrites.located
#print axioms SmcTuring.Native.StringStoreWrites.next_pc
#print axioms SmcTuring.Native.StringRetargetWrites.owned
#print axioms SmcTuring.Appendix.Listing8CopiedPointerWrites.field
#print axioms SmcTuring.Appendix.Listing8CopiedPointerWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.node_word
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.rule_word
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.state_word
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.next_word
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.graph_words
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.input
#print axioms SmcTuring.Appendix.Listing8GraphFieldWriteBounds.direction
#print axioms SmcTuring.Appendix.Listing8InitializerWrites.patch_fields
#print axioms SmcTuring.Appendix.Listing8InitializerWrites.tape_bounds
#print axioms SmcTuring.Appendix.Listing8InitializerWrites.owned
#print axioms SmcTuring.Native.StringDwordWritesBridge.trace
#print axioms SmcTuring.Appendix.Listing8OwnerSequenceWrites.advance_run
#print axioms SmcTuring.Appendix.Listing8OwnerSequenceWrites.advance_owned
#print axioms SmcTuring.Appendix.Listing8OwnerSequenceWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWriteBounds.window
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWriteBounds.pointer
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWriteBounds.placement
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWrites.initialized
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphCopiedWrites.endpoint
#print axioms SmcTuring.Native.StringCopyWrites.copy_address
#print axioms SmcTuring.Native.StringCopyWrites.copy_length
#print axioms SmcTuring.Native.StringCopyWrites.copy_write
#print axioms SmcTuring.Native.StringCopyWrites.copy_run
#print axioms SmcTuring.Native.StringCopyWrites.word
#print axioms SmcTuring.Native.StringCopyWrites.dword
#print axioms SmcTuring.Native.StringSequenceWrites.word_run
#print axioms SmcTuring.Native.StringSequenceWrites.dword_run
#print axioms SmcTuring.Native.StringSequenceWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphPointerWriteBounds.word
#print axioms SmcTuring.Appendix.Listing8GraphPointerWriteBounds.dwords
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.pointer_owned
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.copied_run
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphPointerWrites.endpoint
#print axioms SmcTuring.Native.StringMixedWrites.address
#print axioms SmcTuring.Native.StringMixedWrites.length
#print axioms SmcTuring.Native.StringMixedWrites.code_write
#print axioms SmcTuring.Native.StringMixedWrites.owned_run
#print axioms SmcTuring.Native.MixedWriteRuns.run_append
#print axioms SmcTuring.Native.MixedWriteRuns.trace_run_eq
#print axioms SmcTuring.Native.MixedWriteRuns.owned_run_append
#print axioms SmcTuring.Native.MixedWriteRuns.canonical_run
#print axioms SmcTuring.Native.MixedWriteRuns.arithmetic_owned
#print axioms SmcTuring.Native.MixedWriteRuns.copy_owned
#print axioms SmcTuring.Native.MixedLocatedWrites.field
#print axioms SmcTuring.Appendix.DwordComparisonTailWrites.instruction
#print axioms SmcTuring.Appendix.DwordComparisonTailWrites.owned
#print axioms SmcTuring.Native.DwordMixedWrites.copy_run
#print axioms SmcTuring.Native.DwordMixedWrites.copy_owned
#print axioms SmcTuring.Native.DwordMixedWrites.sequence_owned
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.fields
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.prefix_owned
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.owned
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.canonical_owned
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.mask_owned
#print axioms SmcTuring.Appendix.Listing8LiteralInputWrites.mask_canonical_owned
#print axioms SmcTuring.Appendix.Listing8GraphInputWriteBounds.cursor_tape
#print axioms SmcTuring.Appendix.Listing8GraphInputWriteBounds.masks
#print axioms SmcTuring.Appendix.Listing8GraphInputWriteBounds.placement
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.pointer_state
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.pointer_run
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.input_owned
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphInputWrites.endpoint
#print axioms SmcTuring.Native.DwordPacketWrites.code_write
#print axioms SmcTuring.Native.DwordPacketWrites.owned
#print axioms SmcTuring.Native.DwordPacketWrites.run
#print axioms SmcTuring.Appendix.Listing8DirectionWrites.helper_fields
#print axioms SmcTuring.Appendix.Listing8DirectionWrites.arithmetic_fields
#print axioms SmcTuring.Appendix.Listing8DirectionWrites.helper_run
#print axioms SmcTuring.Appendix.Listing8DirectionWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.region_bounds
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.input_state
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.input_run
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.direction_owned
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphDirectionWrites.endpoint
#print axioms SmcTuring.Native.DwordXorWrites.address
#print axioms SmcTuring.Native.DwordXorWrites.length
#print axioms SmcTuring.Native.DwordXorWrites.xor_write
#print axioms SmcTuring.Native.DwordXorWrites.exchange_write
#print axioms SmcTuring.Native.DwordXorWrites.helper_run
#print axioms SmcTuring.Native.DwordXorWrites.helper_owned
#print axioms SmcTuring.Native.DwordXorWrites.sequence_run
#print axioms SmcTuring.Native.DwordXorWrites.sequence_owned
#print axioms SmcTuring.Appendix.Listing8HeadTailWrites.xor_fields
#print axioms SmcTuring.Appendix.Listing8HeadTailWrites.packet_fields
#print axioms SmcTuring.Appendix.Listing8HeadTailWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.direction_state
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.direction_run
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.head_owned
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphHeadWrites.endpoint
#print axioms SmcTuring.Native.StringDwordRuns.run
#print axioms SmcTuring.Appendix.Listing8StateWrites.helper_fields
#print axioms SmcTuring.Appendix.Listing8StateWrites.packet_fields
#print axioms SmcTuring.Appendix.Listing8StateWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.region_bounds
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.cursor_bounds
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.head_state
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.head_run
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.state_owned
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphStateWrites.endpoint
#print axioms SmcTuring.Native.ControlPacketWrites.length
#print axioms SmcTuring.Native.ControlPacketWrites.address
#print axioms SmcTuring.Native.ControlPacketWrites.code_write
#print axioms SmcTuring.Native.ControlPacketWrites.run
#print axioms SmcTuring.Native.ControlPacketWrites.owned
#print axioms SmcTuring.Native.StringInitWrites.owned
#print axioms SmcTuring.Appendix.Listing8FailureWrites.fields
#print axioms SmcTuring.Appendix.Listing8FailureWrites.comparison_fields
#print axioms SmcTuring.Appendix.Listing8FailureWrites.post_fields
#print axioms SmcTuring.Appendix.Listing8FailureWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.placement
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.state_state
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.state_run
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.failure_owned
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphFailureWrites.endpoint
#print axioms SmcTuring.Appendix.Listing8JumpWrites.native_write
#print axioms SmcTuring.Appendix.Listing8JumpWrites.exchange_write
#print axioms SmcTuring.Appendix.Listing8JumpWrites.adjust_write
#print axioms SmcTuring.Appendix.Listing8JumpWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.stack_inside
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.failure_state
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.failure_run
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.jump_owned
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.body_owned
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.trace
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphJumpWrites.endpoint
#print axioms SmcTuring.Native.StackFieldWrites.memory
#print axioms SmcTuring.Native.StackFieldWrites.add
#print axioms SmcTuring.Native.StackFieldWrites.owned_append
#print axioms SmcTuring.Appendix.Listing4StackWrites.slots
#print axioms SmcTuring.Appendix.Listing4StackWrites.initialize_owned
#print axioms SmcTuring.Appendix.Listing4StackWrites.initialize_run
#print axioms SmcTuring.Appendix.Listing4StackWrites.jump_owned
#print axioms SmcTuring.Appendix.Listing4StackWrites.boot_owned
#print axioms SmcTuring.Appendix.Listing4TargetWrites.owned
#print axioms SmcTuring.Appendix.Listing4TargetWrites.run
#print axioms SmcTuring.Appendix.Listing4TargetWrites.entry_owned
#print axioms SmcTuring.Appendix.Listing8GraphEntryWrites.boot_owned
#print axioms SmcTuring.Appendix.Listing8GraphEntryWrites.boot_run
#print axioms SmcTuring.Appendix.Listing8GraphEntryWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphEntryWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.jump_state
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.return_owned
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.trace
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphReturnWrites.registers
#print axioms SmcTuring.Appendix.Listing8JumpReturnWrites.target_owned
#print axioms SmcTuring.Appendix.Listing8JumpReturnWrites.owned
#print axioms SmcTuring.Appendix.Listing8JumpReturnWrites.execute
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerWrites.advance_run
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerWrites.advance_owned
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerWrites.owned
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.node_fields
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.node_owned
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.transition_fields
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.transition_owned
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.nodes_owned
#print axioms SmcTuring.Appendix.Listing8DeclarationWrites.transitions_owned
#print axioms SmcTuring.Appendix.Listing8ResetWrites.owner_field
#print axioms SmcTuring.Appendix.Listing8ResetWrites.marker_field
#print axioms SmcTuring.Appendix.Listing8ResetWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds.nodes_from_lookup
#print axioms SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds.transitions_from_lookup
#print axioms SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds.nodes
#print axioms SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds.transitions
#print axioms SmcTuring.Appendix.Listing8GraphResetWriteBounds.placement
#print axioms SmcTuring.Appendix.Listing8GraphHaltReturnWrites.call_shape
#print axioms SmcTuring.Appendix.Listing8GraphHaltReturnWrites.return_owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltReturnWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltReturnWrites.trace
#print axioms SmcTuring.Appendix.Listing8GraphHaltReturnWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.table_trace
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.table_owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.reset_entry
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.reset_current
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.reset_trace
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.reset_owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.nodes_trace
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.nodes_owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.trace
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.owned
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.execute
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8LoopReturnWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopReturnWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.table_owned
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.reset_owned
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.nodes_owned
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.trace
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopTerminalWrites.instruction_count
#print axioms SmcTuring.Appendix.Listing8MainCopyWrites.owned
#print axioms SmcTuring.Appendix.Listing8MainCopyWrites.execute
#print axioms SmcTuring.Appendix.Listing8MainRetargetWrites.retarget_owned
#print axioms SmcTuring.Appendix.Listing8MainRetargetWrites.owned
#print axioms SmcTuring.Appendix.Listing8MainRetargetWrites.execute
#print axioms SmcTuring.Appendix.Listing8MainOwnerWrites.owner_owned
#print axioms SmcTuring.Appendix.Listing8MainOwnerWrites.owned
#print axioms SmcTuring.Appendix.Listing8MainOwnerWrites.execute
#print axioms SmcTuring.Appendix.Listing8MainPrefixWrites.owned
#print axioms SmcTuring.Appendix.Listing8MainPrefixWrites.execute
#print axioms SmcTuring.Appendix.Listing8MainInputWrites.input_owned
#print axioms SmcTuring.Appendix.Listing8MainInputWrites.owned
#print axioms SmcTuring.Appendix.Listing8MainInputWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopHeadWrites.direction_owned
#print axioms SmcTuring.Appendix.Listing8LoopHeadWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopHeadWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopStateWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopStateWrites.execute
#print axioms SmcTuring.Appendix.Listing8FailureReuseWrites.owned
#print axioms SmcTuring.Appendix.Listing8FailureReuseWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopFailureWrites.failure_owned
#print axioms SmcTuring.Appendix.Listing8LoopFailureWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopFailureWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopControlWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopControlWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopTerminalBodyWrites.program_split
#print axioms SmcTuring.Appendix.Listing8LoopTerminalBodyWrites.owned
#print axioms SmcTuring.Appendix.Listing8LoopIterationWrites.counts
#print axioms SmcTuring.Appendix.Listing8LoopIterationWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterAnchorWrites.execute
#print axioms SmcTuring.Appendix.Listing8LoopOriginalInterpreterWrites.execute
#print axioms SmcTuring.Native.StringWriteRegions.code_mono
#print axioms SmcTuring.Native.StringWriteRegions.owned_mono
#print axioms SmcTuring.Native.StringWriteRegions.trace_window
#print axioms SmcTuring.Appendix.Listing8OriginalInterpreterWriteFrames.execute
#print axioms SmcTuring.Native.AccumulatorBodyWrites.body
#print axioms SmcTuring.Appendix.Listing9FinalImageWrites.epilogue_owned
#print axioms SmcTuring.Appendix.Listing9FinalImageWrites.execute
#print axioms SmcTuring.Appendix.Listing9ExecutionWrites.execute
#print axioms SmcTuring.Appendix.Listing9FullExecutionWrites.execute
#print axioms SmcTuring.Appendix.Listing8TMRules.encode_toNat
#print axioms SmcTuring.Appendix.Listing8TMRules.encode_injective
#print axioms SmcTuring.Appendix.Listing8TMRules.sentinel_ne
#print axioms SmcTuring.Appendix.Listing8TMRules.index_lookup
#print axioms SmcTuring.Appendix.Listing8TMRules.index_value
#print axioms SmcTuring.Appendix.Listing8TMRules.entry_value
#print axioms SmcTuring.Appendix.Listing8TMRules.active
#print axioms SmcTuring.Appendix.Listing8TMRules.missing
#print axioms SmcTuring.Appendix.Listing8TMRules.terminal
#print axioms SmcTuring.Appendix.Listing8TMRules.scan_allowed
#print axioms SmcTuring.Appendix.Listing8TMRules.different_symbol
#print axioms SmcTuring.Appendix.Listing8TMRules.missing_symbol
#print axioms SmcTuring.Appendix.Listing8TMRules.terminal_symbol
#print axioms SmcTuring.Appendix.Listing8TMRules.frozen_rule
#print axioms SmcTuring.Appendix.Listing8TMRules.empty_frozen_row
#print axioms SmcTuring.Appendix.Listing8TMGraph.scan
#print axioms SmcTuring.Appendix.Listing8TMGraph.stop_scan
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_chosen
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_node
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_updated
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_symbols
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_symbol
#print axioms SmcTuring.Appendix.Listing8TMGraph.mismatch_next
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_chosen
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_next
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_node
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_updated
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_symbols
#print axioms SmcTuring.Appendix.Listing8TMGraph.selected_symbol
#print axioms SmcTuring.Appendix.Listing8TMGraph.terminal_halted
#print axioms SmcTuring.Appendix.Listing8TMScan.steps_append
#print axioms SmcTuring.Appendix.Listing8TMScan.scan_to
#print axioms SmcTuring.Appendix.Listing8TMScan.before_input
#print axioms SmcTuring.Appendix.Listing8TMScan.missing_scan
#print axioms SmcTuring.Appendix.Listing8TMScan.empty_state_halts
#print axioms SmcTuring.Appendix.Listing8TMScan.transition
#print axioms SmcTuring.Appendix.Listing8TMWindow.position_injective
#print axioms SmcTuring.Appendix.Listing8TMWindow.position_headIndex
#print axioms SmcTuring.Appendix.Listing8TMWindow.position_back
#print axioms SmcTuring.Appendix.Listing8TMWindow.position_forward
#print axioms SmcTuring.Appendix.Listing8TMWindow.tape_write
#print axioms SmcTuring.Appendix.Listing8TMWindow.step
#print axioms SmcTuring.Appendix.Listing8TMRun.run
#print axioms SmcTuring.Appendix.Listing8TMRun.positive
#print axioms SmcTuring.Appendix.Listing8TMRun.first_head
#print axioms SmcTuring.Appendix.Listing8TMRun.finite_prefix
#print axioms SmcTuring.Appendix.Listing8TMRun.finite_halt
#print axioms SmcTuring.Appendix.Listing9TMExecution.execute
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.labels
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.joined
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.input_end
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.direction_region
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.direction_labels
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.state_region
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.state_labels
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.failure_region
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.failure_end
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.before_table
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.copy_positions
#print axioms SmcTuring.Appendix.Listing8PackedBodyLayout.word_positions
#print axioms SmcTuring.Appendix.Listing8PackedResources.body_capacity
#print axioms SmcTuring.Appendix.Listing8PackedResources.fixed_range
#print axioms SmcTuring.Appendix.Listing8PackedResources.node_resources
#print axioms SmcTuring.Appendix.Listing8PackedResources.transition_resources
#print axioms SmcTuring.Appendix.Listing8PackedResources.resources
#print axioms SmcTuring.Appendix.Listing8PackedPointerBounds.dword_layouts
#print axioms SmcTuring.Appendix.Listing8PackedPointerBounds.word_valid
#print axioms SmcTuring.Appendix.Listing8PackedPointerBounds.dword_valid
#print axioms SmcTuring.Appendix.Listing8PackedPointerBounds.bounds
#print axioms SmcTuring.Appendix.Listing8PackedFieldBounds.masks
#print axioms SmcTuring.Appendix.Listing8PackedFieldBounds.input_fields
#print axioms SmcTuring.Appendix.Listing8PackedFieldBounds.graph_fields
#print axioms SmcTuring.Appendix.Listing8PackedContext.input_bounds
#print axioms SmcTuring.Appendix.Listing8PackedContext.direction_bounds
#print axioms SmcTuring.Appendix.Listing8PackedContext.state_bounds
#print axioms SmcTuring.Appendix.Listing8PackedContext.failure_bounds
#print axioms SmcTuring.Appendix.Listing8PackedContext.boot_bounds
#print axioms SmcTuring.Appendix.Listing8PackedContext.context
#print axioms SmcTuring.Appendix.Listing9PackedCapacity.endPC_exact
#print axioms SmcTuring.Appendix.Listing9PackedCapacity.bounds
#print axioms SmcTuring.Appendix.Listing9PackedCapacity.graph_bounds
#print axioms SmcTuring.Appendix.Listing9PackedCapacity.context
#print axioms SmcTuring.Appendix.Listing9TMStaticExecution.execute
#print axioms SmcTuring.Appendix.Listing8TMObservedRun.finite_prefix
#print axioms SmcTuring.Appendix.Listing8TMObservedRun.finite_halt
#print axioms SmcTuring.Appendix.Listing8TMOutputWindow.run_frame
#print axioms SmcTuring.Appendix.Listing8TMOutputWindow.initial_outside_blank
#print axioms SmcTuring.Appendix.Listing8TMOutputWindow.terminal_outside_blank
#print axioms SmcTuring.Appendix.Listing8TMOutputWindow.reconstruct
#print axioms SmcTuring.Appendix.Listing9TMObservedExecution.execute
#print axioms SmcTuring.Appendix.Listing9TMObservedExecution.complete_input
#print axioms SmcTuring.Native.StringTraceChecks.split_trace
#print axioms SmcTuring.Native.StringTraceChecks.split_owned
#print axioms SmcTuring.Native.StringTraceChecks.next_store
#print axioms SmcTuring.Native.StringTraceChecks.next_mapped_store
#print axioms SmcTuring.Appendix.Listing8TMFixedObservation.observe_graph
#print axioms SmcTuring.Appendix.Listing8TMFixedObservation.configuration_independent
#print axioms SmcTuring.Appendix.Listing8TMFixedObservation.reconstruct
#print axioms SmcTuring.Appendix.Listing9CanonicalMapping.fits
#print axioms SmcTuring.Appendix.Listing9CanonicalMapping.mapped
#print axioms SmcTuring.Appendix.Listing9CanonicalMapping.endpoint_valid
#print axioms SmcTuring.Appendix.Listing9TMFixedOutput.complete_input
#print axioms SmcTuring.Appendix.Listing9TMCheckedStores.complete_input
#print axioms SmcTuring.Appendix.Listing9EntryProjection.initial_registers
#print axioms SmcTuring.Appendix.Listing9EntryProjection.initial_direction
#print axioms SmcTuring.Appendix.Listing9EntryProjection.initial_pc
#print axioms SmcTuring.Appendix.Listing9EntryProjection.initial_address

#print axioms SmcTuring.Native.StringReadWindows.native_local
#print axioms SmcTuring.Native.StringReadWindows.string_local
#print axioms SmcTuring.Native.StringReadWindows.mixed_local
#print axioms SmcTuring.Native.StringReadWindows.dword_local
#print axioms SmcTuring.Native.StringReadWindows.control_local
#print axioms SmcTuring.Native.StringReadWindows.read_local
#print axioms SmcTuring.Native.StringReadWindows.within_of_owned
#print axioms SmcTuring.Native.StringReadAgreement.dword_agree
#print axioms SmcTuring.Native.StringReadAgreement.native_within
#print axioms SmcTuring.Native.StringReadAgreement.string_agrees
#print axioms SmcTuring.Native.StringReadAgreement.arithmetic_address_agrees
#print axioms SmcTuring.Native.StringReadAgreement.arithmetic_agrees
#print axioms SmcTuring.Native.StringReadAgreement.copy_agrees
#print axioms SmcTuring.Native.StringReadAgreement.mixed_agrees
#print axioms SmcTuring.Native.StringReadAgreement.dword_effect_agrees
#print axioms SmcTuring.Native.StringReadAgreement.control_agrees
#print axioms SmcTuring.Native.StringReadAgreement.execute_agrees
#print axioms SmcTuring.Native.StringReadRuns.append
#print axioms SmcTuring.Native.StringReadRuns.local_of_owned
#print axioms SmcTuring.Native.StringReadRuns.append_trace
#print axioms SmcTuring.Native.StringReadRuns.mono
#print axioms SmcTuring.Native.StringReadRuns.effects_agree
#print axioms SmcTuring.Native.StringReadRuns.next_read
#print axioms SmcTuring.Native.StringMoveReads.contained
#print axioms SmcTuring.Appendix.Listing8MacroReads.setup_local
#print axioms SmcTuring.Appendix.Listing8MacroReads.restore_local
#print axioms SmcTuring.Appendix.Listing8MacroReads.setup
#print axioms SmcTuring.Appendix.Listing8MacroReads.moves
#print axioms SmcTuring.Appendix.Listing8MacroReads.restores
#print axioms SmcTuring.Appendix.Listing8MacroReads.contained
#print axioms SmcTuring.Appendix.Listing8CopyReads.original
#print axioms SmcTuring.Appendix.Listing8CopyReads.live
#print axioms SmcTuring.Native.StringReadClasses.mixed
#print axioms SmcTuring.Native.StringReadClasses.copy
#print axioms SmcTuring.Native.StringReadClasses.native
#print axioms SmcTuring.Native.StringReadClasses.negation
#print axioms SmcTuring.Native.StringReadClasses.add
#print axioms SmcTuring.Native.StringScalarLists.mixed
#print axioms SmcTuring.Native.StringScalarLists.word
#print axioms SmcTuring.Native.StringScalarLists.dword
#print axioms SmcTuring.Native.StringScalarLists.sequence
#print axioms SmcTuring.Native.StringScalarLists.retargets
#print axioms SmcTuring.Appendix.Listing8ScalarReadClasses.owners
#print axioms SmcTuring.Appendix.Listing8ScalarReadClasses.pointers
#print axioms SmcTuring.Appendix.Listing8ScalarReadClasses.retarget
#print axioms SmcTuring.Appendix.Listing8MainReads.retarget
#print axioms SmcTuring.Appendix.Listing8MainReads.owners
#print axioms SmcTuring.Appendix.Listing8MainReads.main_prefix
#print axioms SmcTuring.Appendix.Listing8MainReads.input
#print axioms SmcTuring.Native.StringPacketReadClasses.arithmetic
#print axioms SmcTuring.Native.StringPacketReadClasses.initializers
#print axioms SmcTuring.Native.StringPacketReadClasses.packets
#print axioms SmcTuring.Native.StringPacketReadClasses.xors
#print axioms SmcTuring.Native.StringPacketReadClasses.controls
#print axioms SmcTuring.Appendix.Listing8TailReadClasses.direction
#print axioms SmcTuring.Appendix.Listing8TailReadClasses.head
#print axioms SmcTuring.Appendix.Listing8TailReadClasses.state
#print axioms SmcTuring.Appendix.Listing8TailReadClasses.failure
#print axioms SmcTuring.Appendix.Listing8TailReadClasses.jump_return
#print axioms SmcTuring.Appendix.Listing8LoopReads.direction
#print axioms SmcTuring.Appendix.Listing8LoopReads.head
#print axioms SmcTuring.Appendix.Listing8LoopReads.state
#print axioms SmcTuring.Appendix.Listing8LoopReads.failure
#print axioms SmcTuring.Appendix.Listing8LoopReads.control

#print axioms SmcTuring.Native.StringReadSuffix.contained
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.original_owners
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.nodes
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.transitions
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.reset
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.target
#print axioms SmcTuring.Appendix.Listing8TerminalReadClasses.entry
#print axioms SmcTuring.Appendix.Listing8LoopIterationReads.execute
#print axioms SmcTuring.Appendix.Listing8LoopTerminalReads.tail_local
#print axioms SmcTuring.Appendix.Listing8LoopTerminalReads.contained
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterReads.execute
#print axioms SmcTuring.Appendix.Listing8GraphEntryReads.program_split
#print axioms SmcTuring.Appendix.Listing8GraphEntryReads.input_local
#print axioms SmcTuring.Appendix.Listing8GraphEntryReads.tail_local
#print axioms SmcTuring.Appendix.Listing8GraphEntryReads.copies
#print axioms SmcTuring.Appendix.Listing8GraphEntryReads.contained
#print axioms SmcTuring.Appendix.Listing8GraphReturnReads.contained
#print axioms SmcTuring.Appendix.Listing8GraphReturnReads.halted
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalReads.program_split
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalReads.tail_local
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalReads.contained
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterAnchorReads.execute
#print axioms SmcTuring.Appendix.Listing8LoopOriginalInterpreterReads.execute
#print axioms SmcTuring.Appendix.Listing8OriginalInterpreterReadFrames.execute
#print axioms SmcTuring.Native.AccumulatorReadClasses.prologue
#print axioms SmcTuring.Native.AccumulatorReadClasses.epilogue
#print axioms SmcTuring.Native.AccumulatorBodyReads.body
#print axioms SmcTuring.Appendix.Listing9FinalImageReads.execute
#print axioms SmcTuring.Appendix.Listing9ExecutionReads.execute
#print axioms SmcTuring.Appendix.Listing9FullExecutionReads.storage_local
#print axioms SmcTuring.Appendix.Listing9FullExecutionReads.execute

#print axioms SmcTuring.Native.StringReadPermissions.of_contained
#print axioms SmcTuring.Native.StringReadPermissions.next_read
#print axioms SmcTuring.Native.StringReadPermissions.next_access
#print axioms SmcTuring.Appendix.Listing9TMExecutionReads.execute
#print axioms SmcTuring.Appendix.Listing9TMStaticExecutionReads.execute
#print axioms SmcTuring.Appendix.Listing9TMObservedExecutionReads.execute
#print axioms SmcTuring.Appendix.Listing9TMObservedExecutionReads.complete_input
#print axioms SmcTuring.Appendix.Listing9TMFixedReadOutput.complete_input
#print axioms SmcTuring.Appendix.Listing9TMCheckedReadAccess.complete_input

#print axioms SmcTuring.Native.StringPCSteps.native_pc
#print axioms SmcTuring.Native.StringPCSteps.string_pc
#print axioms SmcTuring.Native.StringPCSteps.arithmetic_pc
#print axioms SmcTuring.Native.StringPCSteps.copy_pc
#print axioms SmcTuring.Native.StringPCSteps.mixed_pc
#print axioms SmcTuring.Native.StringPCSteps.dword_pc
#print axioms SmcTuring.Native.StringPCSteps.control_pc
#print axioms SmcTuring.Native.StringPCSteps.step_pc
#print axioms SmcTuring.Native.StringPCSteps.located_pc
#print axioms SmcTuring.Native.StringPCSteps.total_append
#print axioms SmcTuring.Native.StringPCSteps.run_pc
#print axioms SmcTuring.Native.StringPCWindows.append
#print axioms SmcTuring.Native.StringPCWindows.guard_prefix
#print axioms SmcTuring.Native.StringPCWindows.guard_last
#print axioms SmcTuring.Native.StringPCWindows.sequential
#print axioms SmcTuring.Native.StringPCWindows.append_trace
#print axioms SmcTuring.Native.StringPCWindows.next_window
#print axioms SmcTuring.Native.StringPCEncoding.string_size
#print axioms SmcTuring.Native.StringPCEncoding.string_total
#print axioms SmcTuring.Native.StringPCEncoding.program_total
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.setup_sequential
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.restore_sequential
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.forms_sequential
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.subtract_margin
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.guard
#print axioms SmcTuring.Appendix.Listing8MacroPCWindows.contained

#print axioms SmcTuring.Native.StringDecodeImage.core
#print axioms SmcTuring.Native.StringDecodeImage.packet
#print axioms SmcTuring.Native.StringDecodeImage.extra
#print axioms SmcTuring.Native.StringDecodeImage.decode
#print axioms SmcTuring.Native.StringDecodeImage.fetch
#print axioms SmcTuring.Native.WordDecodeImage.negation
#print axioms SmcTuring.Native.WordDecodeImage.negation_fetch
#print axioms SmcTuring.Native.WordDecodeImage.add_payload
#print axioms SmcTuring.Native.WordDecodeImage.addition
#print axioms SmcTuring.Native.WordDecodeImage.addition_fetch
#print axioms SmcTuring.Native.StringStackImage.mixed_fetch
#print axioms SmcTuring.Native.StringStackImage.dword_fetch
#print axioms SmcTuring.Native.StringStackImage.control_fetch
#print axioms SmcTuring.Native.StringStackImage.fetch
#print axioms SmcTuring.Native.StringStackImage.string_size
#print axioms SmcTuring.Native.StringStackImage.dword_size
#print axioms SmcTuring.Native.StringStackImage.control_size
#print axioms SmcTuring.Native.StringStackImage.size
#print axioms SmcTuring.Native.StringFetchRequests.packet_minimum
#print axioms SmcTuring.Native.StringFetchRequests.packet_string_count
#print axioms SmcTuring.Native.StringMixedRequests.header
#print axioms SmcTuring.Native.StringMixedRequests.string_count
#print axioms SmcTuring.Native.StringMixedRequests.mixed_counts
#print axioms SmcTuring.Native.StringRequestBounds.string_classified
#print axioms SmcTuring.Native.StringRequestBounds.string_fetched
#print axioms SmcTuring.Native.StringRequestBounds.packet_string
#print axioms SmcTuring.Native.StringRequestBounds.packet_dword
#print axioms SmcTuring.Native.StringRequestBounds.packet_control
#print axioms SmcTuring.Native.StringRequestBounds.dword_fetched
#print axioms SmcTuring.Native.StringRequestBounds.control_fetched
#print axioms SmcTuring.Native.StringRequestBounds.fetched
#print axioms SmcTuring.Native.StringFetchWindows.lift_string_trace
#print axioms SmcTuring.Native.StringFetchWindows.of_envelope
#print axioms SmcTuring.Native.StringFetchWindows.of_pc_run
#print axioms SmcTuring.Native.StringFetchWindows.append
#print axioms SmcTuring.Native.StringFetchWindows.append_trace
#print axioms SmcTuring.Native.StringFetchWindows.next_request
#print axioms SmcTuring.Native.StringFetchPermissions.of_contained
#print axioms SmcTuring.Native.StringFetchPermissions.next_request
#print axioms SmcTuring.Native.StringFetchPermissions.next_access
#print axioms SmcTuring.Native.StringPCBranches.last_instruction
#print axioms SmcTuring.Appendix.Listing8MacroFetch.actual
#print axioms SmcTuring.Appendix.Listing8MacroFetch.contained
#print axioms SmcTuring.Appendix.Listing8MacroFetch.complete
#print axioms SmcTuring.Appendix.Listing8MacroFetch.next_access
#print axioms SmcTuring.Appendix.Listing8CopyFetch.original
#print axioms SmcTuring.Appendix.Listing8CopyFetch.live
#print axioms SmcTuring.Appendix.Listing8CopyFetch.complete_original
#print axioms SmcTuring.Appendix.Listing8CopyFetch.complete_live
#print axioms SmcTuring.Appendix.Listing8CopyFetch.next_live_access
#print axioms SmcTuring.Appendix.Listing8GraphCopyFetch.original
#print axioms SmcTuring.Appendix.Listing8GraphCopyFetch.live
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.prefix_sequential
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.prefix_total
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.prefix_guard
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.call_size
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.jump
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.target_sequential
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.target_total
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.target_guard
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.target
#print axioms SmcTuring.Appendix.Listing8JumpPCWindows.complete
#print axioms SmcTuring.Appendix.Listing8JumpFetch.actual
#print axioms SmcTuring.Appendix.Listing8JumpFetch.contained
#print axioms SmcTuring.Appendix.Listing8JumpFetch.complete
#print axioms SmcTuring.Appendix.Listing8JumpFetch.target_access
#print axioms SmcTuring.Appendix.Listing8JumpFetch.next_access
#print axioms SmcTuring.Appendix.Listing8LoopReturnFetch.table_before_end
#print axioms SmcTuring.Appendix.Listing8LoopReturnFetch.placement
#print axioms SmcTuring.Appendix.Listing8LoopReturnFetch.contained
#print axioms SmcTuring.Appendix.Listing8LoopReturnFetch.complete
#print axioms SmcTuring.Appendix.Listing8LoopReturnFetch.target_access

#print axioms SmcTuring.Native.StringInstructionSizes.string
#print axioms SmcTuring.Native.StringInstructionSizes.dword
#print axioms SmcTuring.Native.StringInstructionSizes.control
#print axioms SmcTuring.Native.StringInstructionSizes.size
#print axioms SmcTuring.Native.StringInstructionSizes.fetched
#print axioms SmcTuring.Native.StringInstructionSizes.trace_total
#print axioms SmcTuring.Native.StringPCMargins.sequential
#print axioms SmcTuring.Native.StringPCMargins.encode_span
#print axioms SmcTuring.Native.StringPCMargins.endpoint_span
#print axioms SmcTuring.Native.StringPCMargins.of_trace
#print axioms SmcTuring.Native.StringSequentialFamilies.mixed
#print axioms SmcTuring.Native.StringSequentialFamilies.word
#print axioms SmcTuring.Native.StringSequentialFamilies.dword
#print axioms SmcTuring.Native.StringSequentialFamilies.sequence
#print axioms SmcTuring.Native.StringSequentialFamilies.retargets
#print axioms SmcTuring.Native.StringSequentialPackets.arithmetic
#print axioms SmcTuring.Native.StringSequentialPackets.initializers
#print axioms SmcTuring.Native.StringSequentialPackets.packets
#print axioms SmcTuring.Native.StringSequentialPackets.xors
#print axioms SmcTuring.Native.StringSequentialPackets.controls
#print axioms SmcTuring.Appendix.Listing8SequentialScalars.owners
#print axioms SmcTuring.Appendix.Listing8SequentialScalars.pointers
#print axioms SmcTuring.Appendix.Listing8SequentialScalars.retarget
#print axioms SmcTuring.Appendix.Listing8SequentialTails.direction
#print axioms SmcTuring.Appendix.Listing8SequentialTails.head
#print axioms SmcTuring.Appendix.Listing8SequentialTails.state
#print axioms SmcTuring.Appendix.Listing8SequentialTails.failure
#print axioms SmcTuring.Appendix.Listing8BodySequential.copies
#print axioms SmcTuring.Appendix.Listing8BodySequential.retarget
#print axioms SmcTuring.Appendix.Listing8BodySequential.owners
#print axioms SmcTuring.Appendix.Listing8BodySequential.main_prefix
#print axioms SmcTuring.Appendix.Listing8BodySequential.input
#print axioms SmcTuring.Appendix.Listing8BodySequential.direction
#print axioms SmcTuring.Appendix.Listing8BodySequential.head
#print axioms SmcTuring.Appendix.Listing8BodySequential.state
#print axioms SmcTuring.Appendix.Listing8BodySequential.failure
#print axioms SmcTuring.Appendix.Listing8BodyFetch.endpoint
#print axioms SmcTuring.Appendix.Listing8BodyFetch.short
#print axioms SmcTuring.Appendix.Listing8BodyFetch.ordered
#print axioms SmcTuring.Appendix.Listing8BodyFetch.margin
#print axioms SmcTuring.Appendix.Listing8BodyFetch.pc_windows
#print axioms SmcTuring.Appendix.Listing8BodyFetch.byte_total
#print axioms SmcTuring.Appendix.Listing8BodyFetch.contained
#print axioms SmcTuring.Appendix.Listing8BodyFetch.complete
#print axioms SmcTuring.Appendix.Listing8LoopControlFetch.contained
#print axioms SmcTuring.Appendix.Listing8LoopControlFetch.complete
#print axioms SmcTuring.Appendix.Listing8LoopControlFetch.next_access
#print axioms SmcTuring.Appendix.Listing8LoopIterationFetch.execute

#print axioms SmcTuring.Native.StringPCGuards.append
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.sequential_form
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.total_form
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.guard_form
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.sequential
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.total
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerPC.guard
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.nodes_sequential
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.transitions_sequential
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.nodes_total
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.transitions_total
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.nodes_guard
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.transitions_guard
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.nodes_windows
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.transitions_windows
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.nodes_contained
#print axioms SmcTuring.Appendix.Listing8DeclarationPC.transitions_contained
#print axioms SmcTuring.Appendix.Listing8ResetPC.sequential
#print axioms SmcTuring.Appendix.Listing8ResetPC.total
#print axioms SmcTuring.Appendix.Listing8ResetPC.guard
#print axioms SmcTuring.Appendix.Listing8ResetPC.windows
#print axioms SmcTuring.Appendix.Listing8ResetPC.contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.table_placement
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.reset_placement
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.node_placement
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.table_contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.reset_contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.nodes_contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.tail_contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.contained
#print axioms SmcTuring.Appendix.Listing8LoopTerminalFetch.complete
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterFetch.execute
#print axioms SmcTuring.Appendix.Listing4EntryFetch.sequential
#print axioms SmcTuring.Appendix.Listing4EntryFetch.total
#print axioms SmcTuring.Appendix.Listing4EntryFetch.boot_guard
#print axioms SmcTuring.Appendix.Listing4EntryFetch.guard
#print axioms SmcTuring.Appendix.Listing4EntryFetch.windows
#print axioms SmcTuring.Appendix.Listing4EntryFetch.contained
#print axioms SmcTuring.Appendix.Listing8GraphBodySequential.input_sequential
#print axioms SmcTuring.Appendix.Listing8GraphBodySequential.split
#print axioms SmcTuring.Appendix.Listing8GraphBodySequential.tail_sequential
#print axioms SmcTuring.Appendix.Listing8GraphBodySequential.sequential
#print axioms SmcTuring.Appendix.Listing8GraphBodyFetch.short
#print axioms SmcTuring.Appendix.Listing8GraphBodyFetch.endpoint
#print axioms SmcTuring.Appendix.Listing8GraphBodyFetch.windows
#print axioms SmcTuring.Appendix.Listing8GraphBodyFetch.byte_total
#print axioms SmcTuring.Appendix.Listing8GraphBodyFetch.contained
#print axioms SmcTuring.Appendix.Listing8GraphEntryFetch.split
#print axioms SmcTuring.Appendix.Listing8GraphEntryFetch.windows
#print axioms SmcTuring.Appendix.Listing8GraphEntryFetch.contained
#print axioms SmcTuring.Appendix.Listing8GraphEntryFetch.complete
#print axioms SmcTuring.Appendix.Listing8GraphReturnFetch.target_windows
#print axioms SmcTuring.Appendix.Listing8GraphReturnFetch.backedge_windows
#print axioms SmcTuring.Appendix.Listing8GraphReturnFetch.halt_windows
#print axioms SmcTuring.Appendix.Listing8GraphReturnFetch.contained
#print axioms SmcTuring.Appendix.Listing8GraphReturnFetch.halted
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalFetch.table_contained
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalFetch.reset_contained
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalFetch.nodes_contained
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalFetch.contained
#print axioms SmcTuring.Appendix.Listing8GraphHaltTerminalFetch.complete
#print axioms SmcTuring.Appendix.Listing8LoopInterpreterAnchorFetch.execute
#print axioms SmcTuring.Appendix.Listing8LoopOriginalInterpreterFetch.execute
#print axioms SmcTuring.Appendix.Listing8OriginalInterpreterFetchFrames.execute
#print axioms SmcTuring.Appendix.Listing8OriginalInterpreterAllAccess.execute
#print axioms SmcTuring.Native.StringFetchWiden.within
#print axioms SmcTuring.Native.StringFetchWiden.run
#print axioms SmcTuring.Native.AccumulatorPC.prologue_size
#print axioms SmcTuring.Native.AccumulatorPC.prologue_windows
#print axioms SmcTuring.Native.AccumulatorPC.epilogue_sequential
#print axioms SmcTuring.Native.AccumulatorPC.epilogue_total
#print axioms SmcTuring.Native.AccumulatorPC.epilogue_guard
#print axioms SmcTuring.Native.AccumulatorPC.epilogue_windows
#print axioms SmcTuring.Native.AccumulatorBodyFetch.body
#print axioms SmcTuring.Appendix.Listing9FinalImageFetch.execute
#print axioms SmcTuring.Native.StringInitPC.total
#print axioms SmcTuring.Native.StringInitPC.guard
#print axioms SmcTuring.Native.StringInitPC.windows
#print axioms SmcTuring.Appendix.Listing9ExecutionFetch.execute
#print axioms SmcTuring.Appendix.Listing9StorageFetch.mapped
#print axioms SmcTuring.Appendix.Listing9StorageFetch.sequential
#print axioms SmcTuring.Appendix.Listing9StorageFetch.total
#print axioms SmcTuring.Appendix.Listing9StorageFetch.guard
#print axioms SmcTuring.Appendix.Listing9StorageFetch.windows
#print axioms SmcTuring.Appendix.Listing9StorageFetch.contained
#print axioms SmcTuring.Appendix.Listing9FullExecutionFetch.execute
#print axioms SmcTuring.Appendix.Listing9TMExecutionFetch.execute
#print axioms SmcTuring.Appendix.Listing9TMStaticExecutionFetch.execute
#print axioms SmcTuring.Appendix.Listing9TMObservedExecutionFetch.execute
#print axioms SmcTuring.Appendix.Listing9TMObservedExecutionFetch.complete_input
#print axioms SmcTuring.Appendix.Listing9TMFixedFetchOutput.complete_input
#print axioms SmcTuring.Appendix.Listing9TMCheckedFetchAccess.complete_input

#print axioms SmcTuring.Native.PayloadTemplate.current
#print axioms SmcTuring.Native.PayloadTemplate.frame
#print axioms SmcTuring.Native.PayloadTemplate.operand_store
#print axioms SmcTuring.Native.PayloadTemplate.replace
#print axioms SmcTuring.Native.StringTemplateStates.append
#print axioms SmcTuring.Native.StringTemplateStates.at_prefix
#print axioms SmcTuring.Native.StringTemplateStates.monotone
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.fixed_length
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.initial
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.current
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.operand_store
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.frame
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.string_fetch
#print axioms SmcTuring.Appendix.Listing8PointerTemplate.decodes
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.fixed_length
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.initial
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.current
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.operand_store
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.frame
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.decodes
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.original
#print axioms SmcTuring.Appendix.Listing8ScalarTemplate.located_store
#print axioms SmcTuring.Appendix.Listing8OriginalPointerTemplates.run
#print axioms SmcTuring.Appendix.Listing8OriginalPointerTemplates.original
#print axioms SmcTuring.Appendix.Listing8OriginalPointerTemplates.prefix_decodes
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.decodes
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.field_bounds
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.operand_store
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.frame
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.operand_apart
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.store_all
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.store_outside
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.original_current
#print axioms SmcTuring.Appendix.Listing8OwnerTemplateCollection.copied_current
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.packet_certificate
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.unchanged
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.pointer_run
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.advance_run
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.run_fragment
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.at_prefix
#print axioms SmcTuring.Appendix.Listing8OriginalOwnerRegions.region_inside
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.total_append
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.program_append
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.contiguous_append
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.nodes_total
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.nodes_chain
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.nodes_valid
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.nodes_current
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.nodes_program
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.transitions_total
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.transitions_chain
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.transitions_valid
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.transitions_current
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerGeometry.transitions_program
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.nodes
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.nodes_prefix
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.transitions
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.transitions_prefix
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.nodes_placed
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.nodes_checked_prefix
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.transitions_placed
#print axioms SmcTuring.Appendix.Listing8DeclarationOwnerRegions.transitions_checked_prefix

#print axioms SmcTuring.Native.StringCopyPrefixes.snapshot_window
#print axioms SmcTuring.Native.StringCopyPrefixes.apart_prefix
#print axioms SmcTuring.Native.StringCopyPrefixes.memory
#print axioms SmcTuring.Native.StringCopyPrefixes.indices
#print axioms SmcTuring.Native.StringCopyPrefixes.copied_window
#print axioms SmcTuring.Native.StringCopyPrefixes.source_window
#print axioms SmcTuring.Native.StringCopyPrefixes.next_packet
#print axioms SmcTuring.Native.StringCopyPrefixes.cut
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.geometry
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.source_window
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.prefix_bounds
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.memory
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.indices
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.copied_window
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.source_window_after
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.next_packet
#print axioms SmcTuring.Native.StringMacroCopyPrefixes.whole_prefix
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.header_bounds
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.copied_header
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.copied_decodes
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.outside_decodes
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.macro_header
#print axioms SmcTuring.Appendix.Listing8CopyTemplateWindows.macro_source
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.constructed
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.node_current
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.transition_current
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.node_bounded
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.transition_bounded
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.node_live
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.transition_source_after_first
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.transition_live
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.transition_snapshot
#print axioms SmcTuring.Appendix.Listing8CopyOwnerPrefixes.pair
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.subwindow
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.template
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.all
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.node
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.transition
#print axioms SmcTuring.Appendix.Listing8CopyOwnerFinal.sources
#print axioms SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes.original_current
#print axioms SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes.original
#print axioms SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes.live
#print axioms SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes.next_prefixes

#print axioms SmcTuring.Native.PairedPayloadTemplate.current
#print axioms SmcTuring.Native.PairedPayloadTemplate.initial
#print axioms SmcTuring.Native.PairedPayloadTemplate.frame
#print axioms SmcTuring.Native.PairedPayloadTemplate.operand_store
#print axioms SmcTuring.Native.PairedPayloadTemplate.store
#print axioms SmcTuring.Native.StringMacroTemplates.shape
#print axioms SmcTuring.Native.StringMacroTemplates.fields
#print axioms SmcTuring.Native.StringMacroTemplates.extent
#print axioms SmcTuring.Native.StringMacroTemplates.initial
#print axioms SmcTuring.Native.StringMacroTemplates.current
#print axioms SmcTuring.Native.StringMacroTemplates.operand_store
#print axioms SmcTuring.Native.StringMacroTemplates.frame
#print axioms SmcTuring.Native.StringMacroTemplates.buffer_store
#print axioms SmcTuring.Native.StringPacketRegions.append
#print axioms SmcTuring.Native.StringPacketRegions.word_packet
#print axioms SmcTuring.Native.StringPacketRegions.native_run
#print axioms SmcTuring.Native.StringPacketRegions.interval_run
#print axioms SmcTuring.Native.StringPacketRegions.execute_intact
#print axioms SmcTuring.Native.StringPacketRegions.all_states
#print axioms SmcTuring.Native.StringMacroTemplateWrites.initializer
#print axioms SmcTuring.Native.StringMacroTemplateWrites.field_interval
#print axioms SmcTuring.Native.StringMacroTemplateWrites.exchange
#print axioms SmcTuring.Native.StringMacroTemplateWrites.restore
#print axioms SmcTuring.Native.StringMacroTemplateWrites.setup
#print axioms SmcTuring.Native.StringMacroTemplateWrites.moves
#print axioms SmcTuring.Native.StringMacroTemplateWrites.restores
#print axioms SmcTuring.Native.StringMacroTemplateWrites.complete
#print axioms SmcTuring.Native.StringMacroTemplateWrites.templates
#print axioms SmcTuring.Native.StringEncodedTemplates.string_fetch
#print axioms SmcTuring.Native.StringEncodedTemplates.fetch_split
#print axioms SmcTuring.Native.StringEncodedTemplates.fetch_index
#print axioms SmcTuring.Native.StringEncodedTemplates.offset_sum
#print axioms SmcTuring.Native.StringEncodedTemplates.macro_lengths
#print axioms SmcTuring.Native.StringEncodedTemplates.macro_decodes
#print axioms SmcTuring.Native.StringEncodedTemplates.all_states
#print axioms SmcTuring.Native.StringEncodedTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.constructed
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.at_prefix
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.pair
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.live
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.original
#print axioms SmcTuring.Appendix.Listing8MacroTemplateTransfers.next_pair

#print axioms SmcTuring.Native.DwordOperandTemplates.header_length
#print axioms SmcTuring.Native.DwordOperandTemplates.shape
#print axioms SmcTuring.Native.DwordOperandTemplates.length
#print axioms SmcTuring.Native.DwordOperandTemplates.initial
#print axioms SmcTuring.Native.DwordOperandTemplates.current
#print axioms SmcTuring.Native.DwordOperandTemplates.decodes
#print axioms SmcTuring.Native.DwordOperandTemplates.mutable_store
#print axioms SmcTuring.Native.DwordOperandTemplates.frame
#print axioms SmcTuring.Native.DwordUnaryTemplates.shape
#print axioms SmcTuring.Native.DwordUnaryTemplates.length
#print axioms SmcTuring.Native.DwordUnaryTemplates.initial
#print axioms SmcTuring.Native.DwordUnaryTemplates.current
#print axioms SmcTuring.Native.DwordUnaryTemplates.decodes
#print axioms SmcTuring.Native.DwordUnaryTemplates.mutable_store
#print axioms SmcTuring.Native.DwordUnaryTemplates.frame
#print axioms SmcTuring.Native.DwordTemplateCollection.field_bounds
#print axioms SmcTuring.Native.DwordTemplateCollection.decodes
#print axioms SmcTuring.Native.DwordTemplateCollection.store
#print axioms SmcTuring.Native.DwordTemplateCollection.store_all
#print axioms SmcTuring.Native.DwordTemplateCollection.execute
#print axioms SmcTuring.Native.DwordTemplateCollection.all_states
#print axioms SmcTuring.Native.DwordTemplateCollection.all_decodes
#print axioms SmcTuring.Native.MixedFieldOwnership.located
#print axioms SmcTuring.Native.MixedFieldOwnership.copy_lift
#print axioms SmcTuring.Native.MixedFieldOwnership.copy
#print axioms SmcTuring.Native.MixedFieldOwnership.sequence
#print axioms SmcTuring.Appendix.Listing8InputTemplateRegions.comparison
#print axioms SmcTuring.Appendix.Listing8InputTemplateRegions.prefix_owned
#print axioms SmcTuring.Appendix.Listing8InputTemplateRegions.complete
#print axioms SmcTuring.Appendix.Listing8InputTemplateRegions.mask_complete
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.bounds
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.internal_fields
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.exterior
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.owned_fields
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.mask_operand
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.mask_initial
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.mask_templates
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.mask_decodes
#print axioms SmcTuring.Appendix.Listing8InputExecutableTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.bounds
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.patch_compatible
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.owned
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8RetargetExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8InputRetargetTemplateBindings.retarget_forms
#print axioms SmcTuring.Appendix.Listing8InputRetargetTemplateBindings.retarget
#print axioms SmcTuring.Appendix.Listing8InputRetargetTemplateBindings.input
#print axioms SmcTuring.Appendix.Listing8InputRetargetTemplateBindings.graph_input

#print axioms SmcTuring.Native.MixedFixedTemplates.decodes
#print axioms SmcTuring.Native.MixedFixedTemplates.frame
#print axioms SmcTuring.Native.MixedFixedTemplates.store_all
#print axioms SmcTuring.Native.MixedFixedTemplates.execute
#print axioms SmcTuring.Native.MixedFixedTemplates.all_states
#print axioms SmcTuring.Native.MixedFixedTemplates.all_decodes
#print axioms SmcTuring.Native.MixedFixedTemplates.copy_bounds
#print axioms SmcTuring.Native.MixedFixedTemplates.copy_initial
#print axioms SmcTuring.Native.MixedTemplateGeometry.conjunction
#print axioms SmcTuring.Native.MixedTemplateGeometry.copy_windows
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.first_copy_bounds
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.distribution_bounds
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.bounds
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.internal_fields
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.exterior
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.owned_fields
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.initial
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.mask_initial
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8InputFixedTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.actual_x86
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.actual_x64
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.templates_x86
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.templates_x64
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.coverage
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.valid_windows
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.all_windows
#print axioms SmcTuring.Appendix.Listing8InputJointTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8RetargetTapeTemplates.tape_field
#print axioms SmcTuring.Appendix.Listing8RetargetTapeTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8RetargetTapeTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8RetargetTapeTemplates.actual_copies
#print axioms SmcTuring.Appendix.Listing8JointTemplateBindings.input
#print axioms SmcTuring.Appendix.Listing8JointTemplateBindings.graph_input

#print axioms SmcTuring.Native.DwordPacketTemplateRuns.initial
#print axioms SmcTuring.Native.DwordPacketTemplateRuns.located
#print axioms SmcTuring.Native.DwordPacketTemplateRuns.all_states
#print axioms SmcTuring.Native.DwordPacketTemplateRuns.fixed_states
#print axioms SmcTuring.Native.MixedSequenceTemplateRuns.forms
#print axioms SmcTuring.Native.MixedSequenceTemplateRuns.all_states
#print axioms SmcTuring.Native.MixedSequenceTemplateRuns.fixed_states
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.arithmetic_bounds
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.fixed_bounds
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.compatible
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.frames
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.helper_fields
#print axioms SmcTuring.Appendix.Listing8StateTemplateFields.packet_fields
#print axioms SmcTuring.Appendix.Listing8StateExecutableTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8StateExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8StateExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8StateExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8StateExecutableTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8StateTemplateBindings.original
#print axioms SmcTuring.Appendix.Listing8StateTemplateBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8StateTemplateBindings.maintained
#print axioms SmcTuring.Native.StringStoreRegions.append
#print axioms SmcTuring.Native.StringStoreRegions.bounded_packet
#print axioms SmcTuring.Native.StringStoreRegions.mixed
#print axioms SmcTuring.Native.StringStoreRegions.arithmetic_states
#print axioms SmcTuring.Native.StringStoreRegions.fixed_states
#print axioms SmcTuring.Native.DwordXorRegionRuns.helper
#print axioms SmcTuring.Native.DwordXorRegionRuns.sequence
#print axioms SmcTuring.Native.DwordXorRegionRuns.packets
#print axioms SmcTuring.Native.DwordXorTemplates.frame
#print axioms SmcTuring.Native.DwordXorTemplates.all_states
#print axioms SmcTuring.Native.DwordXorTemplates.decodes
#print axioms SmcTuring.Native.DwordXorTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.arithmetic_bounds
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.xor_bounds
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.compatible
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.frames
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.helper_fields
#print axioms SmcTuring.Appendix.Listing8HeadTemplateFields.packet_fields
#print axioms SmcTuring.Appendix.Listing8HeadExecutableTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8HeadExecutableTemplates.regions
#print axioms SmcTuring.Appendix.Listing8HeadExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8HeadExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8HeadExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8HeadTemplateBindings.original
#print axioms SmcTuring.Appendix.Listing8HeadTemplateBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8HeadTemplateBindings.maintained
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.template_bounds
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.fixed_bounds
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.compatible
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.fixed_frames
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.xor_frames
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.helper_fields
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.packet_fields
#print axioms SmcTuring.Appendix.Listing8DirectionTemplateFields.xor_fields
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.regions
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.initial
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8WholeHeadTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.current
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.original_xor
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.original_tail
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.original
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8WholeHeadBindings.maintained

#print axioms SmcTuring.Native.StringInitTemplates.extent
#print axioms SmcTuring.Native.StringInitTemplates.initial
#print axioms SmcTuring.Native.StringInitTemplates.current
#print axioms SmcTuring.Native.StringInitTemplates.lengths
#print axioms SmcTuring.Native.StringInitTemplates.legal
#print axioms SmcTuring.Native.StringInitTemplates.decodes
#print axioms SmcTuring.Native.StringInitTemplates.frame
#print axioms SmcTuring.Native.StringStoreTemplateRuns.native
#print axioms SmcTuring.Native.StringStoreTemplateRuns.initializer
#print axioms SmcTuring.Native.StringStoreTemplateRuns.control
#print axioms SmcTuring.Native.StringStoreTemplateRuns.preserve
#print axioms SmcTuring.Native.RelativeCallTemplate.initial
#print axioms SmcTuring.Native.RelativeCallTemplate.current
#print axioms SmcTuring.Native.RelativeCallTemplate.decodes
#print axioms SmcTuring.Native.RelativeCallTemplate.frame
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.arithmetic_bounds
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.compatible
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.comparison_bounds
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.comparison_frames
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.owner_frames
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.call_frames
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.comparison_fields
#print axioms SmcTuring.Appendix.Listing8FailureTemplateFields.post_fields
#print axioms SmcTuring.Appendix.Listing8FailureTemplateRegions.reset_field
#print axioms SmcTuring.Appendix.Listing8FailureTemplateRegions.regions
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.store
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.decodes
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8FailureExecutableTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8FailureTemplateBindings.sentinel_after
#print axioms SmcTuring.Appendix.Listing8FailureTemplateBindings.original
#print axioms SmcTuring.Appendix.Listing8FailureTemplateBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8FailureTemplateBindings.maintained
#print axioms SmcTuring.Native.StringTracePrefixes.tail
#print axioms SmcTuring.Appendix.Listing8NativeHeadBoundary.pointer_position
#print axioms SmcTuring.Appendix.Listing8NativeHeadBoundary.after_failure
#print axioms SmcTuring.Appendix.Listing8NativeHeadBoundary.terminal_cut
#print axioms SmcTuring.Appendix.Listing8NativeHeadBoundary.terminal
#print axioms SmcTuring.Appendix.Listing8NativeHeadBoundary.iterations
#print axioms SmcTuring.Appendix.Listing8OriginalNativeHead.original_body
#print axioms SmcTuring.Appendix.Listing8OriginalNativeHead.original_graph
#print axioms SmcTuring.Appendix.Listing9NativeHeadObservation.execute
#print axioms SmcTuring.Appendix.Listing9NativeHeadObservation.complete_input

#print axioms SmcTuring.Native.FixedStackTemplates.decodes
#print axioms SmcTuring.Native.FixedStackTemplates.frame
#print axioms SmcTuring.Native.FixedStackTemplates.store_all
#print axioms SmcTuring.Native.FixedStackTemplates.all_states
#print axioms SmcTuring.Native.FixedStackTemplates.all_decodes
#print axioms SmcTuring.Native.FixedStackTemplates.placed_initial
#print axioms SmcTuring.Native.FixedStackTemplates.placed_bounds
#print axioms SmcTuring.Native.FixedStackTemplates.placed_count
#print axioms SmcTuring.Native.FixedStackTemplates.placed_legal
#print axioms SmcTuring.Appendix.Listing4StackTemplates.front_length
#print axioms SmcTuring.Appendix.Listing4StackTemplates.fields
#print axioms SmcTuring.Appendix.Listing4StackTemplates.initial
#print axioms SmcTuring.Appendix.Listing4StackTemplates.current
#print axioms SmcTuring.Appendix.Listing4StackTemplates.decodes
#print axioms SmcTuring.Appendix.Listing4StackTemplates.store
#print axioms SmcTuring.Appendix.Listing4StackTemplates.all_states
#print axioms SmcTuring.Native.BoundedStoreRegions.native_length
#print axioms SmcTuring.Native.BoundedStoreRegions.packet
#print axioms SmcTuring.Native.BoundedStoreRegions.interval
#print axioms SmcTuring.Native.BoundedStoreRegions.monotone
#print axioms SmcTuring.Appendix.Listing4TargetSlotRegions.at_field
#print axioms SmcTuring.Appendix.Listing4TargetSlotRegions.regions
#print axioms SmcTuring.Appendix.Listing8JumpSlotRegions.jump
#print axioms SmcTuring.Appendix.Listing8JumpSlotRegions.complete
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.prefix_encoding
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.target_encoding
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.descriptor_count
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.legal
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.initial
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.bounds
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.slot_upper
#print axioms SmcTuring.Appendix.Listing8ControlTemplateLayout.frames
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.store
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.decodes
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8ControlExecutableTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8ControlTemplateBindings.original_current
#print axioms SmcTuring.Appendix.Listing8ControlTemplateBindings.original
#print axioms SmcTuring.Appendix.Listing8ControlTemplateBindings.selected_current
#print axioms SmcTuring.Appendix.Listing8ControlTemplateBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8ControlTemplateBindings.maintained

#print axioms SmcTuring.Native.WordCopyStoreRegions.regions
#print axioms SmcTuring.Native.WordCopyTemplates.encoding
#print axioms SmcTuring.Native.WordCopyTemplates.count
#print axioms SmcTuring.Native.WordCopyTemplates.legal
#print axioms SmcTuring.Native.WordCopyTemplates.initial
#print axioms SmcTuring.Native.WordCopyTemplates.bounds
#print axioms SmcTuring.Appendix.Listing8ResetStoreRegions.field_count
#print axioms SmcTuring.Appendix.Listing8ResetStoreRegions.regions
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.fixed_count
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.fixed_legal
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.fixed_initial
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.fixed_frames
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.arithmetic_compatible
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.owner_frames
#print axioms SmcTuring.Appendix.Listing8ResetTemplateFields.call_frames
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.initial
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.store
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.decodes
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8ResetExecutableTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing8ResetTemplateBindings.graph_separation
#print axioms SmcTuring.Appendix.Listing8ResetTemplateBindings.actual_separation
#print axioms SmcTuring.Appendix.Listing8ResetTemplateBindings.original_graph
#print axioms SmcTuring.Appendix.Listing8ResetTemplateBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8ResetTemplateBindings.maintained
#print axioms SmcTuring.Native.AccumulatorStoreRegions.prologue
#print axioms SmcTuring.Native.AccumulatorStoreRegions.epilogue
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.count
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.legal
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.entry_bounds
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.fixed_frames
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.owner_frames
#print axioms SmcTuring.Appendix.Listing9TailTemplateFields.initial_fixed
#print axioms SmcTuring.Appendix.Listing9TailTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing9TailTemplates.from_image
#print axioms SmcTuring.Appendix.Listing9TailTemplates.store
#print axioms SmcTuring.Appendix.Listing9TailTemplates.decodes
#print axioms SmcTuring.Appendix.Listing9TailTemplates.all_states
#print axioms SmcTuring.Appendix.Listing9TailTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing9TailTemplates.at_prefix
#print axioms SmcTuring.Appendix.Listing9TailTemplateRegions.storage
#print axioms SmcTuring.Appendix.Listing9TailTemplateRegions.prologue
#print axioms SmcTuring.Appendix.Listing9TailTemplateRegions.epilogue
#print axioms SmcTuring.Appendix.Listing9TailTemplateRegions.body
#print axioms SmcTuring.Appendix.Listing9TailTemplateInitial.retained
#print axioms SmcTuring.Appendix.Listing9TailTemplateInitial.original
#print axioms SmcTuring.Appendix.Listing9TailTemplateEpilogue.packets
#print axioms SmcTuring.Appendix.Listing9TailTemplateEpilogue.storage_current
#print axioms SmcTuring.Appendix.Listing9TailTemplateExecution.execute
#print axioms SmcTuring.Appendix.Listing9TMTemplateExecution.complete_input

#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.ordered
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.count
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.legal
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.bounds
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.fixed_frames
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.call_frames
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.stack_frames
#print axioms SmcTuring.Appendix.Listing8GlobalControlLayout.initial
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.descriptor_count
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.initial
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.store
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.decodes
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.all_states
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8GlobalControlTemplates.at_prefix
#print axioms SmcTuring.Native.JointTemplateStates.join
#print axioms SmcTuring.Appendix.Listing8GlobalControlRegions.jump
#print axioms SmcTuring.Appendix.Listing8GlobalControlRegions.reset_fields
#print axioms SmcTuring.Appendix.Listing8GlobalControlRegions.reset
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.original_current
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.original_jump
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.selected_current
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.selected_jump
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.maintained_current
#print axioms SmcTuring.Appendix.Listing8GlobalControlBindings.maintained_jump
#print axioms SmcTuring.Appendix.Listing8GlobalResetBindings.original_graph
#print axioms SmcTuring.Appendix.Listing8GlobalResetBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8GlobalResetBindings.maintained

#print axioms SmcTuring.Appendix.Listing8FailureStoreRegions.comparison_fields
#print axioms SmcTuring.Appendix.Listing8FailureStoreRegions.post_fields
#print axioms SmcTuring.Appendix.Listing8FailureStoreRegions.reset_field
#print axioms SmcTuring.Appendix.Listing8FailureStoreRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalFailureRegions.fields
#print axioms SmcTuring.Appendix.Listing8GlobalFailureRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalFailureRegions.graph_geometry
#print axioms SmcTuring.Appendix.Listing8GlobalControlReconstruction.window
#print axioms SmcTuring.Appendix.Listing8GlobalControlReconstruction.prefix_iff
#print axioms SmcTuring.Appendix.Listing8GlobalControlReconstruction.stack_iff
#print axioms SmcTuring.Appendix.Listing8GlobalControlReconstruction.store_iff
#print axioms SmcTuring.Appendix.Listing8GlobalControlReconstruction.all_states
#print axioms SmcTuring.Appendix.Listing8LateGraphFieldBounds.node_word
#print axioms SmcTuring.Appendix.Listing8LateGraphFieldBounds.rule_word
#print axioms SmcTuring.Appendix.Listing8LateGraphFieldBounds.state_word
#print axioms SmcTuring.Appendix.Listing8LateGraphFieldBounds.next_word
#print axioms SmcTuring.Appendix.Listing8GlobalFailureBindings.catalog
#print axioms SmcTuring.Appendix.Listing8GlobalFailureBindings.original_graph
#print axioms SmcTuring.Appendix.Listing8GlobalFailureBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8GlobalFailureBindings.maintained
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationRegions.nodes
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationRegions.transitions
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationRegions.node_regions
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationRegions.transition_regions
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationBindings.nodes
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationBindings.transitions
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationBindings.original_graph
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationBindings.selected_graph
#print axioms SmcTuring.Appendix.Listing8GlobalDeclarationBindings.maintained
#print axioms SmcTuring.Appendix.Listing8TerminalControlTemplates.instruction_count
#print axioms SmcTuring.Appendix.Listing8TerminalControlTemplates.execute
#print axioms SmcTuring.Appendix.Listing8TerminalControlTemplates.at_prefix

#print axioms SmcTuring.Appendix.Listing8GlobalStoreSubregions.within
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.copy
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.input
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.direction
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.state
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.cursor
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.state_cursor
#print axioms SmcTuring.Appendix.Listing8GlobalMainBounds.originals
#print axioms SmcTuring.Appendix.Listing8GlobalMacroRegions.allowed
#print axioms SmcTuring.Appendix.Listing8GlobalMacroRegions.convert
#print axioms SmcTuring.Appendix.Listing8GlobalMacroRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalCopyRegions.placements
#print axioms SmcTuring.Appendix.Listing8GlobalCopyRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalRetargetRegions.patch_fields
#print axioms SmcTuring.Appendix.Listing8GlobalRetargetRegions.retarget
#print axioms SmcTuring.Appendix.Listing8GlobalRetargetRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedPointerRegions.field
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedPointerRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions.window
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions.graph_word
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions.advance_regions
#print axioms SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalMainOwnerRegions.pointer
#print axioms SmcTuring.Appendix.Listing8GlobalMainOwnerRegions.placements
#print axioms SmcTuring.Appendix.Listing8GlobalMainOwnerRegions.owner_regions
#print axioms SmcTuring.Appendix.Listing8GlobalMainOwnerRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalInputRegions.masks
#print axioms SmcTuring.Appendix.Listing8GlobalInputRegions.fields
#print axioms SmcTuring.Appendix.Listing8GlobalInputRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalPointerRegions.word
#print axioms SmcTuring.Appendix.Listing8GlobalPointerRegions.dwords
#print axioms SmcTuring.Appendix.Listing8GlobalPointerRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalSelectionRegions.direction
#print axioms SmcTuring.Appendix.Listing8GlobalSelectionRegions.head
#print axioms SmcTuring.Appendix.Listing8GlobalSelectionRegions.state
#print axioms SmcTuring.Appendix.Listing8GlobalMainPrefixRegions.regions
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.lift_dword
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.input
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.direction
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.head
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.state
#print axioms SmcTuring.Appendix.Listing8GlobalLoopMainRegions.failure
#print axioms SmcTuring.Appendix.Listing8GlobalMainControlTemplates.regions
#print axioms SmcTuring.Appendix.Listing8GlobalMainControlTemplates.reconstruct
#print axioms SmcTuring.Appendix.Listing8GlobalMainControlTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalMainControlTemplates.terminal
#print axioms SmcTuring.Appendix.Listing8GlobalMainControlTemplates.at_prefix

#print axioms SmcTuring.Native.StringStackTraceDeterminism.initial_segment
#print axioms SmcTuring.Native.StringStackTraceDeterminism.equal_length
#print axioms SmcTuring.Native.StringStackTraceDeterminism.transport
#print axioms SmcTuring.Appendix.Listing8GlobalIterationTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.entry
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.prefix_image
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.call_image
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.fail_image
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.current
#print axioms SmcTuring.Appendix.Listing8GlobalInitialControl.decodes
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalPrefix.copying
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalPrefix.current
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalPrefix.regions
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalPrefix.forms_regions
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.input_phase
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.input
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.direction
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.head
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.state
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions.failure
#print axioms SmcTuring.Appendix.Listing4EntrySlotRegions.initial_slots
#print axioms SmcTuring.Appendix.Listing4EntrySlotRegions.jump
#print axioms SmcTuring.Appendix.Listing4EntrySlotRegions.entry
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.body_regions
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.body_decodes
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.return_current
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.return_entry
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.target_capacity
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.instruction_count
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates.nonhalt
#print axioms SmcTuring.Appendix.Listing8GlobalControlProperties.after_trace
#print axioms SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates.reset_property
#print axioms SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates.nodes
#print axioms SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates.property
#print axioms SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalMaintainedInterpreterTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates.halt_return
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates.reset_property
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates.nodes
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates.property
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates.execute
#print axioms SmcTuring.Appendix.Listing8GlobalOriginalInterpreterTemplates.execute
#print axioms SmcTuring.Appendix.Listing9GlobalControlRegions.metadata
#print axioms SmcTuring.Appendix.Listing9GlobalControlRegions.prologue
#print axioms SmcTuring.Appendix.Listing9GlobalControlRegions.epilogue
#print axioms SmcTuring.Appendix.Listing9GlobalControlRegions.storage
#print axioms SmcTuring.Appendix.Listing9GlobalControlExecution.execute
#print axioms SmcTuring.Appendix.Listing9TMGlobalControlExecution.complete_input

#print axioms SmcTuring.Native.StringTemplateTraceSegments.segment
#print axioms SmcTuring.Native.StringTemplateTraceSegments.join_segment
#print axioms SmcTuring.Appendix.Listing8MaintainedJointPhases.input
#print axioms SmcTuring.Appendix.Listing8MaintainedJointPhases.head
#print axioms SmcTuring.Appendix.Listing8MaintainedJointPhases.state
#print axioms SmcTuring.Appendix.Listing8MaintainedJointPhases.failure
#print axioms SmcTuring.Appendix.Listing8JointMacroControl.initial_property
#print axioms SmcTuring.Appendix.Listing8JointMacroControl.pair
#print axioms SmcTuring.Appendix.Listing8JointMacroControl.maintained
#print axioms SmcTuring.Appendix.Listing8JointMacroControl.original
#print axioms SmcTuring.Native.StringMacroCrossTemplates.outside
#print axioms SmcTuring.Native.StringMacroCrossTemplates.execute
#print axioms SmcTuring.Native.StringMacroCrossTemplates.all_states
#print axioms SmcTuring.Native.StringMacroCrossTemplates.all_decodes
#print axioms SmcTuring.Appendix.Listing8CrossMacroCatalog.separation
#print axioms SmcTuring.Appendix.Listing8CrossMacroCatalog.pair
#print axioms SmcTuring.Appendix.Listing8CrossMacroCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8CrossMacroCatalog.original
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes.macro_prefix
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes.pair
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes.maintained
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes.original

#print axioms SmcTuring.Appendix.Listing8CopiedPointerActiveRegions.packet_certificate
#print axioms SmcTuring.Appendix.Listing8CopiedPointerActiveRegions.unchanged
#print axioms SmcTuring.Appendix.Listing8CopiedPointerActiveRegions.run
#print axioms SmcTuring.Appendix.Listing8CopiedPointerActiveRegions.own_template
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerCatalog.current
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerCatalog.all_current
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerCatalog.window
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerCatalog.retained
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerActiveRun.empty
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerActiveRun.pointer_certificate
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerActiveRun.advance
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerActiveRun.run_fragment
#print axioms SmcTuring.Appendix.Listing8CopiedOwnerActiveRun.run
#print axioms SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates.execute
#print axioms SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates.endpoint
#print axioms SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates.main
#print axioms SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates.maintained
#print axioms SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates.original
#print axioms SmcTuring.Appendix.Listing8JointRetargetControl.shape
#print axioms SmcTuring.Appendix.Listing8JointRetargetControl.maintained
#print axioms SmcTuring.Appendix.Listing8JointRetargetControl.original

#print axioms SmcTuring.Appendix.Listing8OwnerStoreRegions.pointer
#print axioms SmcTuring.Appendix.Listing8OwnerStoreRegions.advance
#print axioms SmcTuring.Appendix.Listing8OwnerStoreRegions.regions
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.after_code
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.copied_self_x64
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.self
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.target_words
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.scalar_targets
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerFields.placements
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerCatalog.initial
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerCatalog.regions
#print axioms SmcTuring.Appendix.Listing8RetargetOwnerCatalog.main
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.prefix_window
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.initial
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.self_after
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.word_after
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.placements
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.regions
#print axioms SmcTuring.Appendix.Listing8MacroOwnerFrames.all_decodes
#print axioms SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog.instruction_count
#print axioms SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog.descriptor_count
#print axioms SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog.main
#print axioms SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog.original

#print axioms SmcTuring.Native.CopyStoreRegions.native
#print axioms SmcTuring.Native.CopyStoreRegions.copy
#print axioms SmcTuring.Native.CopyStoreRegions.word
#print axioms SmcTuring.Native.CopyStoreRegions.dword
#print axioms SmcTuring.Native.CopyStoreRegions.sequence
#print axioms SmcTuring.Appendix.Listing8RetargetPointerFields.before_patch
#print axioms SmcTuring.Appendix.Listing8RetargetPointerFields.word_fields
#print axioms SmcTuring.Appendix.Listing8RetargetPointerFields.dword_sources
#print axioms SmcTuring.Appendix.Listing8RetargetPointerFields.dword_fields
#print axioms SmcTuring.Appendix.Listing8RetargetPointerFields.regions
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.word_fields
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.dword_fields
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.regions
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.store
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.all_states
#print axioms SmcTuring.Appendix.Listing8MacroPointerFrames.all_decodes
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerCatalog.owner_pointer
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerCatalog.instruction_count
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerCatalog.original
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.store
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.ranges
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.word_fields
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.dword_sources
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.dword_fields
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.regions
#print axioms SmcTuring.Appendix.Listing8OwnerPointerFrames.all_states
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerPurity.main
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerPurity.maintained
#print axioms SmcTuring.Appendix.Listing8JointOwnerPointerPurity.original

#print axioms SmcTuring.Appendix.Listing8InputStoreFields.masks
#print axioms SmcTuring.Appendix.Listing8InputStoreFields.fields
#print axioms SmcTuring.Appendix.Listing8InputStoreFields.regions
#print axioms SmcTuring.Appendix.Listing8InputCrossCatalogFields.cursor_before_second
#print axioms SmcTuring.Appendix.Listing8InputCrossCatalogFields.retarget
#print axioms SmcTuring.Appendix.Listing8InputCrossCatalogFields.macros_store
#print axioms SmcTuring.Appendix.Listing8InputCrossCatalogFields.owners
#print axioms SmcTuring.Appendix.Listing8InputCatalogInitial.endpoint
#print axioms SmcTuring.Appendix.Listing8InputCatalogInitial.retarget
#print axioms SmcTuring.Appendix.Listing8InputCatalogInitial.macros
#print axioms SmcTuring.Appendix.Listing8InputCatalogInitial.owners
#print axioms SmcTuring.Appendix.Listing8InputCatalogInitial.initial
#print axioms SmcTuring.Appendix.Listing8JointInputCatalog.store
#print axioms SmcTuring.Appendix.Listing8JointInputCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointInputCatalog.owner_pointer_input
#print axioms SmcTuring.Appendix.Listing8JointInputCatalog.maintained

#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.inside
#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.direction
#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.xor_fields
#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.packet_fields
#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.head
#print axioms SmcTuring.Appendix.Listing8HeadStoreFields.complete
#print axioms SmcTuring.Appendix.Listing8HeadCrossCatalogFields.retarget
#print axioms SmcTuring.Appendix.Listing8HeadCrossCatalogFields.macros_store
#print axioms SmcTuring.Appendix.Listing8HeadCrossCatalogFields.owners
#print axioms SmcTuring.Appendix.Listing8HeadCrossCatalogFields.store
#print axioms SmcTuring.Appendix.Listing8JointHeadCatalog.initial
#print axioms SmcTuring.Appendix.Listing8JointHeadCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointHeadCatalog.owner_pointer_input_head
#print axioms SmcTuring.Appendix.Listing8JointHeadCatalog.maintained

#print axioms SmcTuring.Appendix.Listing8MainCatalogTransport.retarget
#print axioms SmcTuring.Appendix.Listing8MainCatalogTransport.macros_store
#print axioms SmcTuring.Appendix.Listing8MainCatalogTransport.owners
#print axioms SmcTuring.Appendix.Listing8MainCatalogTransport.store
#print axioms SmcTuring.Appendix.Listing8StateStoreFields.inside
#print axioms SmcTuring.Appendix.Listing8StateStoreFields.helper_fields
#print axioms SmcTuring.Appendix.Listing8StateStoreFields.packet_fields
#print axioms SmcTuring.Appendix.Listing8StateStoreFields.regions
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.prefix_forms
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.prefix_trace
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.initial
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.through_state
#print axioms SmcTuring.Appendix.Listing8JointStateCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8SentinelCatalogTransport.late
#print axioms SmcTuring.Appendix.Listing8SentinelCatalogTransport.owners
#print axioms SmcTuring.Appendix.Listing8SentinelCatalogTransport.store
#print axioms SmcTuring.Appendix.Listing8FailureCrossCatalogFields.fields
#print axioms SmcTuring.Appendix.Listing8FailureCrossCatalogFields.regions
#print axioms SmcTuring.Appendix.Listing8FailureCrossCatalogFields.store
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.prefix_forms
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.prefix_trace
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.initial
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.through_failure
#print axioms SmcTuring.Appendix.Listing8JointFailureCatalog.maintained

#print axioms SmcTuring.Appendix.Listing8ControlStoreFields.slot_bound
#print axioms SmcTuring.Appendix.Listing8ControlStoreFields.regions
#print axioms SmcTuring.Appendix.Listing8ControlStoreFields.all_states
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.prefix_forms
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.prefix_trace
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.initial
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.through_control
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.endpoint
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.instruction_count
#print axioms SmcTuring.Appendix.Listing8JointControlCatalog.returned

#print axioms SmcTuring.Appendix.Listing8MacroRetargetFrames.prefix_window
#print axioms SmcTuring.Appendix.Listing8MacroRetargetFrames.initial
#print axioms SmcTuring.Appendix.Listing8MacroRetargetFrames.regions
#print axioms SmcTuring.Appendix.Listing8MacroRetargetFrames.all_states
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.retarget
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.copy_retarget
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.main
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.after_copies
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8JointMainMacroCatalog.original_prefix

#print axioms SmcTuring.Appendix.Listing8RetargetPointerOwners.catalog_member
#print axioms SmcTuring.Appendix.Listing8RetargetPointerOwners.initial
#print axioms SmcTuring.Appendix.Listing8RetargetPointerOwners.patch_fields
#print axioms SmcTuring.Appendix.Listing8RetargetPointerOwners.regions
#print axioms SmcTuring.Appendix.Listing8RetargetPointerOwners.all_states
#print axioms SmcTuring.Appendix.Listing8PhaseOwnerCatalog.scalar_current
#print axioms SmcTuring.Appendix.Listing8PhaseOwnerCatalog.from_fixed
#print axioms SmcTuring.Appendix.Listing8PhaseOwnerCatalog.from_catalogs
#print axioms SmcTuring.Appendix.Listing8PhaseOwnerCatalog.empty
#print axioms SmcTuring.Appendix.Listing8PhaseOwnerCatalog.from_fixed_certificate
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.retarget
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.after_copies
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.maintained
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.fixed_endpoint
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.instruction_count
#print axioms SmcTuring.Appendix.Listing8JointRetargetOwnerPhase.original_retarget

#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.original_current
#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.node_current
#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.rule_current
#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.from_initial
#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.node_bounds
#print axioms SmcTuring.Appendix.Listing8OriginalGraphCatalog.rule_bounds
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInputFields.lower
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInputFields.node_symbol
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInputFields.symbol
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInputFields.allowed
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInputFields.store
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphInput.initial
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphInput.all_states
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphInput.main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphInput.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalGraphTransport.compatible
#print axioms SmcTuring.Appendix.Listing8OriginalGraphTransport.store
#print axioms SmcTuring.Appendix.Listing8OriginalGraphTransport.head_allowed
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.input_endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.head_trace
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.head_main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.head_endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.state_main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.through_state
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphState.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.empty
#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.x64_forms
#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.x64_bytes
#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.from_reader
#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.initializer
#print axioms SmcTuring.Appendix.Listing8OriginalGraphSentinel.restored
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.before_field
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.store
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.reset_all
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.comparison_states
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.post_states
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.whole
#print axioms SmcTuring.Appendix.Listing8OriginalGraphFailureRun.endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.from_owner
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.from_sentinel
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.limit
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.initial
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.prefix_trace
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.through_failure
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.control_main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.through_control
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphFailure.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial.window
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial.initial
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial.scalar_targets
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial.pointer_regions
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerRun.empty
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerRun.retained_originals
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerRun.advance
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerRun.run_fragment
#print axioms SmcTuring.Appendix.Listing8OriginalGraphOwnerRun.run
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.forms_shape
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.owner_main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.owner_endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.pointer_main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.owner_pointer
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.through_control
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphOwner.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalGraphInitializer.empty
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInitializer.from_reader
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInitializer.initializer
#print axioms SmcTuring.Appendix.Listing8OriginalGraphInitializer.restored
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.empty
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.from_initializer
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.exchange
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.setup
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.setup_endpoint
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.moves
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.restores
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.complete
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMacroRun.endpoint
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphCopies.from_macro
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphCopies.pair
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphCopies.maintained
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphCopies.movs_joint

#print axioms SmcTuring.Appendix.Listing8OriginalGraphRetarget.copies_endpoint
#print axioms SmcTuring.Appendix.Listing8OriginalGraphRetarget.regions
#print axioms SmcTuring.Appendix.Listing8OriginalGraphRetarget.all_states
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphRetarget.from_phase
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphRetarget.from_fixed
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphRetarget.retarget
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphRetarget.after_copies
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphRetarget.maintained
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphMain.from_copy
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphMain.from_phase
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphMain.forms_shape
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphMain.main
#print axioms SmcTuring.Appendix.Listing8JointOriginalGraphMain.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.nodes_initial
#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.rules_initial
#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.initial
#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.regions
#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.window
#print axioms SmcTuring.Appendix.Listing8OriginalGraphBootstrap.all_states
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMainEntry.nodes
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMainEntry.rules
#print axioms SmcTuring.Appendix.Listing8OriginalGraphMainEntry.current
#print axioms SmcTuring.Appendix.Listing8OriginalGraphContinuations.global_after_boot
#print axioms SmcTuring.Appendix.Listing8OriginalGraphContinuations.copies
#print axioms SmcTuring.Appendix.Listing8OriginalGraphContinuations.retarget
#print axioms SmcTuring.Appendix.Listing8OriginalGraphContinuations.owner_pointer
#print axioms SmcTuring.Appendix.Listing8OriginalGraphContinuations.through_pointer

#print axioms SmcTuring.Appendix.Listing8InactiveLocalCatalog.geometry
#print axioms SmcTuring.Appendix.Listing8InactiveLocalCatalog.fields
#print axioms SmcTuring.Appendix.Listing8InactiveLocalCatalog.store
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.decodes
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.initial
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.regions
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.snapshots
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.from_snapshot
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.all_states
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.all_decodes
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.main
#print axioms SmcTuring.Appendix.Listing8InactiveLocalInput.maintained

#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.decodes
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.store
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.ordering
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.exterior
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.head_write
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.state_write
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.head_slot
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.state_slot
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.head_helpers
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.head_xors
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.head_packets
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.state_helpers
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.state_packets
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.input_windows
#print axioms SmcTuring.Appendix.Listing8JointLocalCatalog.descriptor_count
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.head_tail_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.head_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.state_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.failure_fields
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.failure_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.from_snapshot
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.input_templates
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.input
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.input_trace
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.through_head
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.through_state
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.through_failure
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.control_fields
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.through_control
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.all_decodes
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.main
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.maintained
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.trace
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.endpoint
#print axioms SmcTuring.Appendix.Listing8JointLocalContinuation.at_prefix

#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.exterior
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.fresh_arithmetic
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.fresh_fixed
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.before_head
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.input_fields
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.macro_packet
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.macro_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.call_before_table
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.copy_placements
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.pointer_self
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.pointer_targets
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.owner_placements
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.head_pointer_arithmetic
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.head_pointer_field
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.state_pointer_field
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.copied_field
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.copied_halves
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.word_fields
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixFields.dword_fields
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.initial
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.copy_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.retarget_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.owner_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.pointer_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.through_retarget_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.prefix_regions
#print axioms SmcTuring.Appendix.Listing8JointLocalPrefixRun.all_states
#print axioms SmcTuring.Appendix.Listing8JointLocalMain.forms_shape
#print axioms SmcTuring.Appendix.Listing8JointLocalMain.local_states
#print axioms SmcTuring.Appendix.Listing8JointLocalMain.maintained
#print axioms SmcTuring.Appendix.Listing8JointLocalMain.endpoint
#print axioms SmcTuring.Appendix.Listing8JointLocalMain.at_prefix

#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.property
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.store
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.regions
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.macro_frame
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.reached_inventory
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.endpoint_inventory
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.restore_frame
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.copied_inventory
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.inventory_start
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.restorations
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.inventory_full
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimes.inventory_unborn
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.inventory_bounds
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.second_outside
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.node_restorations
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.node_second_macro
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.rule_restorations
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.patch_bounds
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.patches_initial
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.patch_packet
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.patch_macro
#print axioms SmcTuring.Appendix.Listing8CopyOwnerLifetimeRun.patches_copies
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.from_all
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.property_append
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.macros
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.restore_slice
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.first_restorations
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.second_macro
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.moves_cut
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.first_moves
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.second_moves
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.second_restorations
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.after_copies
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.copies
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.maintained
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.restoration_start
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.macro_endpoint
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.append_cut
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.macro_shape
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.birth_coverage
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.coverage
#print axioms SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes.complete

#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.snapshot
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.store
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.inactive_states
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.joined
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.catalog_updated
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.endpoint_seed
#print axioms SmcTuring.Appendix.Listing8JointDeclarationCatalog.transitions
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.local_fields
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.field_classes
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.retarget_fields
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.macro_fields
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.store
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.states
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.maintained
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.endpoint
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.observer_store
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.cursor_ends
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.observers_endpoint
#print axioms SmcTuring.Appendix.Listing8JointResetCatalog.nodes
#print axioms SmcTuring.Appendix.Listing8JointInitializerCatalog.empty
#print axioms SmcTuring.Appendix.Listing8JointInitializerCatalog.from_reader
#print axioms SmcTuring.Appendix.Listing8JointInitializerCatalog.initializer
#print axioms SmcTuring.Appendix.Listing8JointInitializerCatalog.restored
#print axioms SmcTuring.Appendix.Listing8JointObserverGeometry.node_member
#print axioms SmcTuring.Appendix.Listing8JointObserverGeometry.rule_member
#print axioms SmcTuring.Appendix.Listing8JointObserverGeometry.copied_classification
#print axioms SmcTuring.Appendix.Listing8JointObserverGeometry.graph_gap
#print axioms SmcTuring.Appendix.Listing8JointObserverGeometry.outside

#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.empty
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.from_initializer
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.fields
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.all_states
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.call_not_target
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.input_not_target
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.call_states
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.input_states
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.owner_states
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.complete
#print axioms SmcTuring.Appendix.Listing8JointResetObserverRun.maintained

#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.memory
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.direction
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.state
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.failure
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.current
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.main
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.pre_catalog
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.early_store
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.bootstrap
#print axioms SmcTuring.Appendix.Listing8OriginalControlImage.bootstrap_then_main

#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.original_upper
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.table_before_end
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.owner_upper
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.observer_store
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.store
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.decodes
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.epilogue
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.terminal_seed
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.maintained_epilogue
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.before_store
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.prologue
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.saved_bootstrap
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.saved_bootstrap_main
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.declaration_certificate
#print axioms SmcTuring.Appendix.Listing8JointAccumulatorCatalog.terminal_tail

#print axioms SmcTuring.Appendix.Listing8OriginalResetBinding.reset
#print axioms SmcTuring.Appendix.Listing8OriginalResetBinding.current
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.cut_append
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.coverage
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.returned
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.complete
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.observations
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.terminal_shape
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.epilogue_current
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.trace
#print axioms SmcTuring.Appendix.Listing8BoundarySummary.complete_trace

#print axioms SmcTuring.Appendix.Listing8JointIteration.trace
#print axioms SmcTuring.Appendix.Listing8JointIteration.execute
#print axioms SmcTuring.Appendix.Listing8JointIteration.at_prefix
#print axioms SmcTuring.Appendix.Listing8JointInterpreter.shape
#print axioms SmcTuring.Appendix.Listing8JointInterpreter.main_prefix
#print axioms SmcTuring.Appendix.Listing8JointInterpreter.execute
#print axioms SmcTuring.Appendix.Listing8JointInterpreter.original
#print axioms SmcTuring.Appendix.Listing8JointInterpreter.complete_input

#print axioms SmcTuring.Appendix.Listing9JointFullExecution.final_catalog
#print axioms SmcTuring.Appendix.Listing9JointFullExecution.epilogue_packets
#print axioms SmcTuring.Appendix.Listing9JointFullExecution.execute
#print axioms SmcTuring.Appendix.Listing9JointFullExecution.complete_input
#print axioms SmcTuring.CorrectedPaper.observations
#print axioms SmcTuring.CorrectedPaper.bounded_appendix
#print axioms SmcTuring.CorrectedPaper.full_paper

#print axioms SmcTuring.Appendix.Listing9SameTraceBinding.head_cut
#print axioms SmcTuring.Appendix.Listing9SameTraceBinding.execute
#print axioms SmcTuring.Appendix.Listing9SameTraceBinding.complete_input
#print axioms SmcTuring.Native.PhysicalImageBinding.normalized_target
#print axioms SmcTuring.Native.PhysicalImageBinding.normalized_bytes
#print axioms SmcTuring.Native.PhysicalImageBinding.site_target
#print axioms SmcTuring.Native.PhysicalImageBinding.normalize_frame
#print axioms SmcTuring.Native.PhysicalImageBinding.normalize_targets
#print axioms SmcTuring.Native.PhysicalImageBinding.present_eq
#print axioms SmcTuring.Native.PhysicalImageBinding.projected
#print axioms SmcTuring.Native.PhysicalImageBinding.current_pc
#print axioms SmcTuring.Native.PhysicalImageBinding.realize
#print axioms SmcTuring.Native.PhysicalImageBinding.at_prefix
#print axioms SmcTuring.Appendix.Listing9PhysicalBinding.complete_input
#print axioms SmcTuring.Appendix.Listing9PhysicalBinding.full_paper

#print axioms PalomarSMC.mathematical_result
