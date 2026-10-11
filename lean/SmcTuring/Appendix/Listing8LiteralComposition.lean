module
public import SmcTuring.Appendix.Listing8LiteralMaskTrace

public section
namespace SmcTuring.Appendix.Listing8LiteralComposition
open Native Listing8LiteralInput
abbrev Dword := BitVec 32

/-- The node fields and later mask destinations are disjoint. Full Listing 8
initialization must derive these static placements and the cursor value. -/
structure DataOutside (mode : Mode) (layout : Layout) : Prop where
  cursor : layout.cursor+mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.cursor
  tape : layout.head+10 ≤ layout.start ∨ endPC mode layout ≤ layout.head+6
  maskCursor : ∀ helper ∈ distributionLayouts mode layout,
    helper.destination+4 ≤ layout.cursor ∨ layout.cursor+mode.wordBytes ≤ helper.destination
  maskTape : ∀ helper ∈ distributionLayouts mode layout,
    helper.destination+4 ≤ layout.head+6 ∨ layout.head+10 ≤ helper.destination

@[expose] def distributedState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword)
    (state : Execution.State mode) :=
  Listing8LiteralMaskTrace.finish mode layout (prefixState mode layout candidate ruleOld state)
@[expose] def finish (mode : Mode) (layout : Layout) (candidate ruleOld fresh : Dword)
    (state : Execution.State mode) :=
  InputUpdate.finish mode (updateLayout mode layout) ruleOld fresh (chosen candidate ruleOld)
    (distributedState mode layout candidate ruleOld state)
@[expose] def program (mode : Mode) (layout : Layout) (candidate ruleOld fresh : Dword) :=
  prefixProgram mode layout candidate ruleOld ++ Listing8LiteralMaskTrace.program mode layout ++
    InputUpdate.program mode (updateLayout mode layout) ruleOld fresh (chosen candidate ruleOld)

theorem field_bounds (mode : Mode) (layout : Layout) :
    (layout.start ≤ scalarField mode layout ∧ scalarField mode layout+4 ≤ endPC mode layout) ∧
    (layout.start ≤ maskField mode layout ∧ maskField mode layout+4 ≤ endPC mode layout) ∧
    (layout.start ≤ pendingField mode layout ∧ pendingField mode layout+4 ≤ endPC mode layout) := by
  have ⟨owner,scalar,source,dist,update,mask,pending,ending⟩ := positions mode layout
  rw [scalar,mask,pending,ending]
  cases mode <;> simp

theorem cursor_field_frame (mode : Mode) (layout : Layout) (outside : DataOutside mode layout)
    (field : Nat) (within : layout.start ≤ field ∧ field+4 ≤ endPC mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    MixedMemory.getWord mode (DwordCode.put memory field value) layout.cursor =
      MixedMemory.getWord mode memory layout.cursor := by
  apply MixedMemory.wide_after_dword
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases outside.cursor with before | after <;> omega

theorem tape_field_frame (mode : Mode) (layout : Layout) (outside : DataOutside mode layout)
    (field : Nat) (within : layout.start ≤ field ∧ field+4 ≤ endPC mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    DwordCode.get (DwordCode.put memory field value) (layout.head+6) =
      DwordCode.get memory (layout.head+6) := by
  apply DwordCode.get_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases outside.tape with before | after <;> omega

theorem prefix_cursor (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedMemory.getWord mode (prefixState mode layout candidate ruleOld state).memory layout.cursor =
      MixedMemory.getWord mode state.memory layout.cursor := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have ⟨scalar,mask,pending⟩ := field_bounds mode layout
  rw [cursor_field_frame mode layout outside _ mask,cursor_field_frame mode layout outside _ scalar,
    cursor_field_frame mode layout outside _ pending,cursor_field_frame mode layout outside _ mask]

theorem prefix_tape (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (prefixState mode layout candidate ruleOld state).memory (layout.head+6) =
      DwordCode.get state.memory (layout.head+6) := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have ⟨scalar,mask,pending⟩ := field_bounds mode layout
  rw [tape_field_frame mode layout outside _ mask,tape_field_frame mode layout outside _ scalar,
    tape_field_frame mode layout outside _ pending,tape_field_frame mode layout outside _ mask]

theorem distribution_memory (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Listing8LiteralMaskTrace.Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    (distributedState mode layout candidate ruleOld state).memory =
      DwordMixedSequence.putFields (prefixState mode layout candidate ruleOld state).memory
        (distributionLayouts mode layout) (InputUpdate.mask (chosen candidate ruleOld)) :=
  Listing8LiteralMaskTrace.memory_effect mode layout capacity valid _ _
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_mask mode layout candidate ruleOld targetOld fresh capacity state entry intact)

theorem distribution_cursor (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Listing8LiteralMaskTrace.Valid mode layout)
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedMemory.getWord mode (distributedState mode layout candidate ruleOld state).memory layout.cursor =
      MixedMemory.getWord mode state.memory layout.cursor := by
  rw [distribution_memory mode layout candidate ruleOld targetOld fresh capacity valid state entry intact]
  unfold MixedMemory.getWord
  rw [DwordMixedSequence.putFields_window _ _ _ _ _ outside.maskCursor]
  exact prefix_cursor mode layout candidate ruleOld targetOld fresh capacity outside state entry intact

theorem distribution_tape (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Listing8LiteralMaskTrace.Valid mode layout)
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (distributedState mode layout candidate ruleOld state).memory (layout.head+6) =
      DwordCode.get state.memory (layout.head+6) := by
  rw [distribution_memory mode layout candidate ruleOld targetOld fresh capacity valid state entry intact]
  unfold DwordCode.get
  rw [DwordMixedSequence.putFields_window _ _ _ _ _ outside.maskTape]
  exact prefix_tape mode layout candidate ruleOld targetOld fresh capacity outside state entry intact

theorem distribution_update_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Listing8LiteralMaskTrace.Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh (chosen candidate ruleOld)
      (distributedState mode layout candidate ruleOld state).memory := by
  rw [distribution_memory mode layout candidate ruleOld targetOld fresh capacity valid state entry intact]
  change ByteMemory.bytesAt (DwordMixedSequence.putFields _ _ _) (updateStart mode layout) (InputUpdate.span mode) = _
  rw [DwordMixedSequence.putFields_window]
  · exact prefix_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact
  · intro helper member
    have coords := positions mode layout
    have lower : layout.start ≤ updateStart mode layout := by
      rw [coords.2.2.2.2.1]
      omega
    rcases valid.outsideInput helper member with before | after
    · left; omega
    · right; exact after

theorem distribution_pc (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Listing8LiteralMaskTrace.Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    (distributedState mode layout candidate ruleOld state).pc = Arithmetic.encodeNat mode (updateStart mode layout) :=
  Listing8LiteralMaskTrace.endpoint mode layout capacity valid _
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)

/-- Every instruction in the literal corrected input region fetches from one
initial whole image. No later fetch, mask equality, or copy effect is assumed. -/
theorem trace (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    MixedDword.Trace mode state (program mode layout candidate ruleOld fresh) (finish mode layout candidate ruleOld fresh state) := by
  have first := prefix_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have second := Listing8LiteralMaskTrace.trace mode layout capacity masks _
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_distribution_current mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have third := InputUpdateTrace.trace mode (updateLayout mode layout) update ruleOld fresh (chosen candidate ruleOld)
    (distributedState mode layout candidate ruleOld state)
    (distribution_pc mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    (distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    ((distribution_cursor mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans cursor)
  exact MixedDword.trace_append mode (MixedDword.trace_append mode first second) third

theorem instruction_count (mode : Mode) (layout : Layout) (candidate ruleOld fresh : Dword) :
    (program mode layout candidate ruleOld fresh).length = if mode = .x86 then 20 else 26 := by
  cases mode <;> simp [program,prefixProgram,DwordComparisonTail.program,DwordLayout.program,
    Listing8LiteralMaskTrace.program,DwordMixedSequence.program,distributionLayouts,
    Listing8MaskCopy.distributionLayouts,InputUpdate.program,CursorLayout.program]

/-- Candidate/tape specialization: the tape initially equals `candidate`.
The printed initializer instead supplies tape to the SUB immediate and rule
to the scalar; Listing8SourceEffects proves that source binding separately. -/
theorem effect (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    finish mode layout candidate ruleOld fresh state =
      { distributedState mode layout candidate ruleOld state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put
          (DwordCode.put (distributedState mode layout candidate ruleOld state).memory (pendingField mode layout)
            (CursorEffects.delta ruleOld fresh (chosen candidate ruleOld)))
          (layout.head+6) (if chosen candidate ruleOld then fresh else candidate) } := by
  have result := InputUpdateTrace.effect_rule mode (updateLayout mode layout) update ruleOld candidate fresh
    (chosen candidate ruleOld) (distributedState mode layout candidate ruleOld state)
    (distribution_pc mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    (distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    ((distribution_cursor mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans cursor)
    ((distribution_tape mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans tape)
    (Listing8InputComposition.chosen_matches_tape candidate ruleOld candidate rfl)
  rw [InputUpdate.endpoint] at result
  exact result

theorem retained (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    InputUpdate.Intact mode (updateLayout mode layout) (CursorEffects.delta ruleOld fresh (chosen candidate ruleOld))
      fresh (chosen candidate ruleOld) (finish mode layout candidate ruleOld fresh state).memory :=
  InputUpdateTrace.retained_image_rule mode (updateLayout mode layout) update ruleOld candidate fresh
    (chosen candidate ruleOld) (distributedState mode layout candidate ruleOld state)
    (distribution_pc mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    (distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    ((distribution_cursor mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans cursor)
    ((distribution_tape mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans tape)
    (Listing8InputComposition.chosen_matches_tape candidate ruleOld candidate rfl)

/-- The source word is restored before the actual AND packet is fetched. -/
theorem restored_mask_source (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (distributedState mode layout candidate ruleOld state).memory (maskField mode layout) =
      InputUpdate.mask (chosen candidate ruleOld) := by
  have packet := InputUpdateTrace.second_current mode (updateLayout mode layout) ruleOld fresh (chosen candidate ruleOld) _
    (distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
  have source := Listing8MaskCopy.mask_operand (distributedState mode layout candidate ruleOld state).memory
    (updateStart mode layout+10)
    (Relocation.memoryDisp mode (updateStart mode layout+20) (pendingField mode layout)) (chosen candidate ruleOld)
    (by simpa [InputUpdate.andForm,updateLayout,pendingField,DwordArithmetic.encode_length,DwordArithmetic.located,
      DwordArithmetic.relocate,DwordArithmetic.length,DwordArithmetic.encode,Nat.add_assoc] using packet)
  simpa only [maskField,Nat.add_assoc] using source

theorem destination_values (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (separate : Listing8LiteralMaskTrace.Separate mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate)
    (reader : DwordLayout.Layout) (member : reader ∈ distributionLayouts mode layout) :
    DwordCode.get (finish mode layout candidate ruleOld fresh state).memory reader.destination =
      InputUpdate.mask (chosen candidate ruleOld) := by
  rw [effect mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor tape]
  have tapeSeparate := outside.maskTape reader member
  have placement := masks.outsideInput reader member
  have bounds := (field_bounds mode layout).2.2
  rw [DwordCode.get_frame _ _ _ _ (by
    intro index
    have bound := index.isLt
    simp only [ByteMemory.Inside]
    rcases tapeSeparate with before | after <;> omega),
    DwordCode.get_frame _ _ _ _ (by
      intro index
      have bound := index.isLt
      simp only [ByteMemory.Inside]
      rcases placement with before | after <;> omega)]
  exact Listing8LiteralMaskTrace.destinations mode layout capacity masks separate _ _
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_mask mode layout candidate ruleOld targetOld fresh capacity state entry intact) reader member

theorem tape_value (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    DwordCode.get (finish mode layout candidate ruleOld fresh state).memory (layout.head+6) =
      (if chosen candidate ruleOld then fresh else candidate) := by
  rw [effect mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor tape,
    DwordCode.get_put]

theorem region_size (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword) :
    (bytes mode layout candidate ruleOld targetOld fresh).length = if mode = .x86 then 139 else 180 := by
  have size := bytes_length mode layout candidate ruleOld targetOld fresh
  rw [(positions mode layout).2.2.2.2.2.2.2] at size
  omega

/-- DWORD helpers restore EAX and zero-extend RAX; the full-width cursor
pair restores that post-helper accumulator. SP is unchanged and XOR clears CF. -/
theorem registers (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    (finish mode layout candidate ruleOld fresh state).accumulator = DwordCode.lift mode (DwordCode.low mode state.accumulator) ∧
    (finish mode layout candidate ruleOld fresh state).stack = state.stack ∧
    (finish mode layout candidate ruleOld fresh state).carry = false := by
  have copies := DwordMixedSequence.registers mode (distributionLayouts mode layout) (distributionStart mode layout)
    (Listing8LiteralMaskTrace.chain mode layout) (Listing8LiteralMaskTrace.copies_valid mode layout capacity masks)
    (prefixState mode layout candidate ruleOld state)
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have nonempty : (distributionLayouts mode layout).length ≠ 0 := by
    cases mode <;> simp [distributionLayouts,Listing8MaskCopy.distributionLayouts]
  have accumulator : (distributedState mode layout candidate ruleOld state).accumulator =
      DwordCode.lift mode (DwordCode.low mode (prefixState mode layout candidate ruleOld state).accumulator) := by
    simpa only [distributedState,Listing8LiteralMaskTrace.finish,if_neg nonempty] using copies.2.2
  have stack : (distributedState mode layout candidate ruleOld state).stack =
      (prefixState mode layout candidate ruleOld state).stack := copies.1
  rw [effect mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor tape]
  simp only
  rw [accumulator,stack,prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [DwordCode.low_lift,and_self]

/-- Initialization by the complete literal byte image supplies the entire
trace, selected tape result and retained live update code. Node binding is
still explicit until the full interpreter initializer is constructed. -/
theorem original_correct (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (backing : ByteMemory.Memory)
    (initialized : state.memory = image mode layout candidate ruleOld targetOld fresh backing)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    MixedDword.Trace mode state (program mode layout candidate ruleOld fresh) (finish mode layout candidate ruleOld fresh state) ∧
    DwordCode.get (finish mode layout candidate ruleOld fresh state).memory (layout.head+6) =
      (if chosen candidate ruleOld then fresh else candidate) ∧
    InputUpdate.Intact mode (updateLayout mode layout) (CursorEffects.delta ruleOld fresh (chosen candidate ruleOld))
      fresh (chosen candidate ruleOld) (finish mode layout candidate ruleOld fresh state).memory := by
  have intact : Intact mode layout candidate ruleOld targetOld fresh state.memory := by
    rw [initialized]
    exact initial_intact mode layout candidate ruleOld targetOld fresh backing
  exact ⟨trace mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor,
    tape_value mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor tape,
    retained mode layout candidate ruleOld targetOld fresh capacity masks update outside state entry intact cursor tape⟩

end SmcTuring.Appendix.Listing8LiteralComposition
