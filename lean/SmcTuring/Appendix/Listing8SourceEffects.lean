module
public import SmcTuring.Appendix.Listing8LiteralComposition

public section
namespace SmcTuring.Appendix.Listing8SourceEffects
open Native Listing8LiteralInput Listing8LiteralComposition
abbrev Dword := BitVec 32

/- Printed MOVEMODEOFFS sends the current tape symbol to curinputval's SUB
immediate and the transition's current symbol to curtinputval's scalar.
The existing trace is mode- and value-general. These effects use that actual
binding and retain the earlier candidate/tape specialization unchanged. -/

theorem effect (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol) :
    finish mode layout ruleSymbol tapeSymbol fresh state =
      { distributedState mode layout ruleSymbol tapeSymbol state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put
          (DwordCode.put (distributedState mode layout ruleSymbol tapeSymbol state).memory (pendingField mode layout)
            (CursorEffects.delta tapeSymbol fresh (chosen ruleSymbol tapeSymbol)))
          (layout.head+6) (if chosen ruleSymbol tapeSymbol then fresh else tapeSymbol) } := by
  have result := InputUpdateTrace.effect_rule mode (updateLayout mode layout) update tapeSymbol tapeSymbol fresh
    (chosen ruleSymbol tapeSymbol) (distributedState mode layout ruleSymbol tapeSymbol state)
    (distribution_pc mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks state entry intact)
    (distribution_update_intact mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks state entry intact)
    ((distribution_cursor mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks outside state entry intact).trans cursor)
    ((distribution_tape mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks outside state entry intact).trans tape)
    (fun _ => rfl)
  rw [InputUpdate.endpoint] at result
  exact result


theorem retained (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol) :
    InputUpdate.Intact mode (updateLayout mode layout) (CursorEffects.delta tapeSymbol fresh (chosen ruleSymbol tapeSymbol))
      fresh (chosen ruleSymbol tapeSymbol) (finish mode layout ruleSymbol tapeSymbol fresh state).memory :=
  InputUpdateTrace.retained_image_rule mode (updateLayout mode layout) update tapeSymbol tapeSymbol fresh
    (chosen ruleSymbol tapeSymbol) (distributedState mode layout ruleSymbol tapeSymbol state)
    (distribution_pc mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks state entry intact)
    (distribution_update_intact mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks state entry intact)
    ((distribution_cursor mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks outside state entry intact).trans cursor)
    ((distribution_tape mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks outside state entry intact).trans tape)
    (fun _ => rfl)


theorem destination_values (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (separate : Listing8LiteralMaskTrace.Separate mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol)
    (reader : DwordLayout.Layout) (member : reader ∈ distributionLayouts mode layout) :
    DwordCode.get (finish mode layout ruleSymbol tapeSymbol fresh state).memory reader.destination =
      InputUpdate.mask (chosen ruleSymbol tapeSymbol) := by
  rw [effect mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks update outside state entry intact cursor tape]
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
    (prefix_pc mode layout ruleSymbol tapeSymbol targetOld fresh capacity state entry intact)
    (prefix_mask mode layout ruleSymbol tapeSymbol targetOld fresh capacity state entry intact) reader member


theorem tape_value (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol) :
    DwordCode.get (finish mode layout ruleSymbol tapeSymbol fresh state).memory (layout.head+6) =
      (if chosen ruleSymbol tapeSymbol then fresh else tapeSymbol) := by
  rw [effect mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks update outside state entry intact cursor tape,
    DwordCode.get_put]


theorem registers (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol) :
    (finish mode layout ruleSymbol tapeSymbol fresh state).accumulator = DwordCode.lift mode (DwordCode.low mode state.accumulator) ∧
    (finish mode layout ruleSymbol tapeSymbol fresh state).stack = state.stack ∧
    (finish mode layout ruleSymbol tapeSymbol fresh state).carry = false := by
  have copies := DwordMixedSequence.registers mode (distributionLayouts mode layout) (distributionStart mode layout)
    (Listing8LiteralMaskTrace.chain mode layout) (Listing8LiteralMaskTrace.copies_valid mode layout capacity masks)
    (prefixState mode layout ruleSymbol tapeSymbol state)
    (prefix_pc mode layout ruleSymbol tapeSymbol targetOld fresh capacity state entry intact)
  have nonempty : (distributionLayouts mode layout).length ≠ 0 := by
    cases mode <;> simp [distributionLayouts,Listing8MaskCopy.distributionLayouts]
  have accumulator : (distributedState mode layout ruleSymbol tapeSymbol state).accumulator =
      DwordCode.lift mode (DwordCode.low mode (prefixState mode layout ruleSymbol tapeSymbol state).accumulator) := by
    simpa only [distributedState,Listing8LiteralMaskTrace.finish,if_neg nonempty] using copies.2.2
  have stack : (distributedState mode layout ruleSymbol tapeSymbol state).stack =
      (prefixState mode layout ruleSymbol tapeSymbol state).stack := copies.1
  rw [effect mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks update outside state entry intact cursor tape]
  simp only
  rw [accumulator,stack,prefix_effect mode layout ruleSymbol tapeSymbol targetOld fresh capacity state entry intact]
  simp only [DwordCode.low_lift,and_self]


/-- The actual printed source binding has a complete current-byte trace and
selected tape effect from one initialized input-region image. The surrounding
copy/retargeting prologue must still derive this image and cursor binding. -/
theorem original_correct (mode : Mode) (layout : Layout) (ruleSymbol tapeSymbol targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (backing : ByteMemory.Memory)
    (initialized : state.memory = image mode layout ruleSymbol tapeSymbol targetOld fresh backing)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeSymbol) :
    MixedDword.Trace mode state (program mode layout ruleSymbol tapeSymbol fresh)
      (finish mode layout ruleSymbol tapeSymbol fresh state) ∧
    DwordCode.get (finish mode layout ruleSymbol tapeSymbol fresh state).memory (layout.head+6) =
      (if chosen ruleSymbol tapeSymbol then fresh else tapeSymbol) ∧
    InputUpdate.Intact mode (updateLayout mode layout) (CursorEffects.delta tapeSymbol fresh (chosen ruleSymbol tapeSymbol))
      fresh (chosen ruleSymbol tapeSymbol) (finish mode layout ruleSymbol tapeSymbol fresh state).memory := by
  have intact : Intact mode layout ruleSymbol tapeSymbol targetOld fresh state.memory := by
    rw [initialized]
    exact initial_intact mode layout ruleSymbol tapeSymbol targetOld fresh backing
  exact ⟨Listing8LiteralComposition.trace mode layout ruleSymbol tapeSymbol targetOld fresh
      capacity masks update outside state entry intact cursor,
    tape_value mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks update outside state entry intact cursor tape,
    retained mode layout ruleSymbol tapeSymbol targetOld fresh capacity masks update outside state entry intact cursor tape⟩

end SmcTuring.Appendix.Listing8SourceEffects
