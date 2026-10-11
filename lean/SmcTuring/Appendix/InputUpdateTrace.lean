module
public import SmcTuring.Appendix.InputUpdate

public section
namespace SmcTuring.Appendix.InputUpdateTrace
open Native InputUpdate

theorem first_current (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value fresh chosen memory) :
    ByteMemory.bytesAt memory layout.start (DwordArithmetic.encode (xorForm mode layout fresh)).length =
      DwordArithmetic.encode (xorForm mode layout fresh) := by
  have allBytes : ByteMemory.bytesAt memory layout.start (bytes mode layout value fresh chosen).length =
      bytes mode layout value fresh chosen := by simpa only [length,Intact] using intact
  exact ByteWindow.packet memory layout.start [] _ (DwordArithmetic.encode (andForm mode layout chosen) ++
    CursorImage.bytes mode (body layout) value) (by simpa [bytes,List.append_assoc] using allBytes)

theorem second_current (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value fresh chosen memory) :
    ByteMemory.bytesAt memory (layout.start+10) (DwordArithmetic.encode (andForm mode layout chosen)).length =
      DwordArithmetic.encode (andForm mode layout chosen) := by
  have allBytes : ByteMemory.bytesAt memory layout.start (bytes mode layout value fresh chosen).length =
      bytes mode layout value fresh chosen := by simpa only [length,Intact] using intact
  have found := ByteWindow.packet memory layout.start (DwordArithmetic.encode (xorForm mode layout fresh))
    (DwordArithmetic.encode (andForm mode layout chosen)) (CursorImage.bytes mode (body layout) value)
    (by simpa [bytes,List.append_assoc] using allBytes)
  simpa only [(prefix_lengths mode layout fresh chosen).1] using found

theorem prefix_trace (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory) :
    MixedDword.Trace mode state [.arithmetic (xorForm mode layout fresh),.arithmetic (andForm mode layout chosen)]
      (masked mode layout fresh chosen state) := by
  have startFits : layout.start < 2^(8*mode.wordBytes) := by
    have bounds := field_bounds mode layout
    have fits := field_fits mode layout valid
    omega
  have nextFits : layout.start+10 < 2^(8*mode.wordBytes) := by
    have bounds := field_bounds mode layout
    have fits := field_fits mode layout valid
    omega
  have firstPC : state.pc.toNat = layout.start := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ startFits]
  have secondPC : (xored mode layout fresh state).pc.toNat = layout.start+10 := by
    rw [xored_effect mode layout valid old fresh chosen state entry intact,Arithmetic.encode_nat_toNat mode _ nextFits]
  have firstFetch : MixedDword.fetch mode state.memory state.pc.toNat =
      some (.arithmetic (xorForm mode layout fresh)) := by
    rw [firstPC]
    exact MixedDword.current_encoding mode _ _ _ (first_current mode layout old fresh chosen state.memory intact)
  have secondFetch : MixedDword.fetch mode (xored mode layout fresh state).memory (xored mode layout fresh state).pc.toNat =
      some (.arithmetic (andForm mode layout chosen)) := by
    rw [secondPC]
    exact MixedDword.current_encoding mode _ _ _ (second_current mode layout (old ^^^ fresh) fresh chosen _
      (xored_intact mode layout valid old fresh chosen state entry intact))
  exact .step firstFetch (.step secondFetch (.nil _))

theorem cursor_frame (mode : Mode) (layout : Layout) (valid : Valid mode layout) (index : Fin mode.wordBytes) :
    ¬ByteMemory.Inside (field mode layout) 4 (layout.cursor+index.val) := by
  have bounds := field_bounds mode layout
  have within := index.isLt
  unfold ByteMemory.Inside
  rcases valid.cursorOutside with before | after <;> omega

theorem tape_frame (mode : Mode) (layout : Layout) (valid : Valid mode layout) (index : Fin 4) :
    ¬ByteMemory.Inside (field mode layout) 4 (layout.head+6+index.val) := by
  have bounds := field_bounds mode layout
  have within := index.isLt
  unfold ByteMemory.Inside
  rcases valid.tapeOutside with before | after <;> omega

theorem masked_cursor (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    MixedMemory.getWord mode (masked mode layout fresh chosen state).memory (body layout).cursor =
      Arithmetic.encodeNat mode (body layout).head := by
  rw [masked_effect mode layout valid old fresh chosen state entry intact]
  change MixedMemory.getWord mode (DwordCode.put state.memory (field mode layout) _) layout.cursor = _
  rw [MixedMemory.wide_after_dword mode state.memory _ _ _ (cursor_frame mode layout valid)]
  exact cursor

theorem masked_tape (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (tape : DwordCode.get state.memory (layout.head+6) = old) :
    DwordCode.get (masked mode layout fresh chosen state).memory ((body layout).head+6) = old := by
  rw [masked_effect mode layout valid old fresh chosen state entry intact]
  change DwordCode.get (DwordCode.put state.memory (field mode layout) _) (layout.head+6) = old
  rw [DwordCode.get_frame state.memory _ _ _ (tape_frame mode layout valid)]
  exact tape

theorem masked_tape_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleOld fresh chosen state.memory)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld) :
    DwordCode.get (masked mode layout fresh chosen state).memory ((body layout).head+6) = tapeOld := by
  rw [masked_effect mode layout valid ruleOld fresh chosen state entry intact]
  change DwordCode.get (DwordCode.put state.memory (field mode layout) _) (layout.head+6) = tapeOld
  rw [DwordCode.get_frame state.memory _ _ _ (tape_frame mode layout valid)]
  exact tape

theorem trace (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    MixedDword.Trace mode state (program mode layout old fresh chosen) (finish mode layout old fresh chosen state) := by
  have firstTrace := prefix_trace mode layout valid old fresh chosen state entry intact
  have maskedPC : (masked mode layout fresh chosen state).pc = Arithmetic.encodeNat mode (body layout).start := by
    rw [masked_effect mode layout valid old fresh chosen state entry intact]
  have cursorCode := body_current mode layout (CursorEffects.delta old fresh chosen) fresh chosen _
    (masked_intact mode layout valid old fresh chosen state entry intact)
  have rest := CursorImage.trace mode (body layout) valid.cursor (CursorEffects.delta old fresh chosen)
    (masked mode layout fresh chosen state) maskedPC
    (masked_cursor mode layout valid old fresh chosen state entry intact cursor) cursorCode
  exact MixedDword.trace_append mode firstTrace rest

theorem effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old) :
    finish mode layout old fresh chosen state =
      { state with
        pc := Arithmetic.encodeNat mode (CursorLayout.endPC mode (body layout))
        carry := false
        memory := DwordCode.put (DwordCode.put state.memory (field mode layout) (CursorEffects.delta old fresh chosen))
          (layout.head+6) (if chosen then fresh else old) } := by
  have maskedPC : (masked mode layout fresh chosen state).pc = Arithmetic.encodeNat mode (body layout).start := by
    rw [masked_effect mode layout valid old fresh chosen state entry intact]
  have result := CursorEffects.selected_effect mode (body layout) valid.cursor old fresh chosen
    (masked mode layout fresh chosen state) maskedPC
    (masked_cursor mode layout valid old fresh chosen state entry intact cursor)
    (masked_tape mode layout valid old fresh chosen state entry intact tape)
  change finish mode layout old fresh chosen state = _ at result
  rw [result,masked_effect mode layout valid old fresh chosen state entry intact]
  rfl

/-- The copied rule symbol and live tape symbol may differ on a failed
comparison; the match implication is the only equality needed for the update. -/
theorem effect_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleOld fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld)
    (matching : chosen = true → ruleOld = tapeOld) :
    finish mode layout ruleOld fresh chosen state =
      { state with
        pc := Arithmetic.encodeNat mode (CursorLayout.endPC mode (body layout))
        carry := false
        memory := DwordCode.put (DwordCode.put state.memory (field mode layout)
          (CursorEffects.delta ruleOld fresh chosen))
          (layout.head+6) (if chosen then fresh else tapeOld) } := by
  have maskedPC : (masked mode layout fresh chosen state).pc =
      Arithmetic.encodeNat mode (body layout).start := by
    rw [masked_effect mode layout valid ruleOld fresh chosen state entry intact]
  have result := CursorEffects.selected_effect_rule mode (body layout) valid.cursor
    ruleOld tapeOld fresh chosen (masked mode layout fresh chosen state) maskedPC
    (masked_cursor mode layout valid ruleOld fresh chosen state entry intact cursor)
    (masked_tape_rule mode layout valid ruleOld tapeOld fresh chosen state entry intact tape)
    matching
  change finish mode layout ruleOld fresh chosen state = _ at result
  rw [result,masked_effect mode layout valid ruleOld fresh chosen state entry intact]
  rfl

theorem exterior (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old) (position : Nat)
    (operandOutside : ¬ByteMemory.Inside (field mode layout) 4 position)
    (tapeOutside : ¬ByteMemory.Inside (layout.head+6) 4 position) :
    (finish mode layout old fresh chosen state).memory position = state.memory position := by
  rw [effect mode layout valid old fresh chosen state entry intact cursor tape]
  exact (ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using tapeOutside)).trans
    (ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using operandOutside))

theorem exterior_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleOld fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld)
    (matching : chosen = true → ruleOld = tapeOld) (position : Nat)
    (operandOutside : ¬ByteMemory.Inside (field mode layout) 4 position)
    (tapeOutside : ¬ByteMemory.Inside (layout.head+6) 4 position) :
    (finish mode layout ruleOld fresh chosen state).memory position = state.memory position := by
  rw [effect_rule mode layout valid ruleOld tapeOld fresh chosen state entry intact cursor tape matching]
  exact (ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using tapeOutside)).trans
    (ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using operandOutside))

theorem pure (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (owned : Nat → Nat → Prop) (operandOwned : owned (field mode layout) 4)
    (cursorOwned : owned layout.cursor mode.wordBytes) (tapeOwned : owned (layout.head+6) 4) :
    MixedDword.OwnedRun mode owned (program mode layout old fresh chosen) state := by
  have firstTarget := DwordArithmetic.located_address mode (.bitXor 0 fresh) layout.start (field mode layout) state
    rfl entry (xor_range mode layout)
  have firstPC : (xored mode layout fresh state).pc = Arithmetic.encodeNat mode (layout.start+10) := by
    rw [xored_effect mode layout valid old fresh chosen state entry intact]
  have secondTarget := DwordArithmetic.located_address mode (.bitAnd 0 (mask chosen)) (layout.start+10)
    (field mode layout) (xored mode layout fresh state) rfl firstPC (and_range mode layout)
  have maskedPC : (masked mode layout fresh chosen state).pc = Arithmetic.encodeNat mode (body layout).start := by
    rw [masked_effect mode layout valid old fresh chosen state entry intact]
  have rest := CursorImage.pure mode (body layout) valid.cursor (CursorEffects.delta old fresh chosen)
    (masked mode layout fresh chosen state) maskedPC
    (masked_cursor mode layout valid old fresh chosen state entry intact cursor) owned cursorOwned tapeOwned
  change owned (DwordArithmetic.address mode (xorForm mode layout fresh) state).toNat 4 ∧
    owned (DwordArithmetic.address mode (andForm mode layout chosen) (xored mode layout fresh state)).toNat 4 ∧
    MixedDword.OwnedRun mode owned (CursorLayout.program mode (body layout) (CursorEffects.delta old fresh chosen))
      (masked mode layout fresh chosen state)
  rw [xorForm,andForm,firstTarget,secondTarget,Arithmetic.encode_nat_toNat mode _ (field_fits mode layout valid)]
  exact ⟨operandOwned,operandOwned,rest⟩

theorem original_correct (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (backing : ByteMemory.Memory)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (initialized : state.memory = image mode layout old fresh chosen backing)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old) :
    MixedDword.Trace mode state (program mode layout old fresh chosen) (finish mode layout old fresh chosen state) ∧
    finish mode layout old fresh chosen state =
      { state with
        pc := Arithmetic.encodeNat mode (CursorLayout.endPC mode (body layout))
        carry := false
        memory := DwordCode.put (DwordCode.put state.memory (field mode layout) (CursorEffects.delta old fresh chosen))
          (layout.head+6) (if chosen then fresh else old) } := by
  have intact : Intact mode layout old fresh chosen state.memory := by
    rw [initialized]
    exact initial_intact mode layout old fresh chosen backing
  exact ⟨trace mode layout valid old fresh chosen state entry intact cursor,
    effect mode layout valid old fresh chosen state entry intact cursor tape⟩


theorem original_correct_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (backing : ByteMemory.Memory) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (initialized : state.memory = image mode layout ruleOld fresh chosen backing)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld)
    (matching : chosen = true → ruleOld = tapeOld) :
    MixedDword.Trace mode state (program mode layout ruleOld fresh chosen)
      (finish mode layout ruleOld fresh chosen state) ∧
    finish mode layout ruleOld fresh chosen state =
      { state with
        pc := Arithmetic.encodeNat mode (CursorLayout.endPC mode (body layout))
        carry := false
        memory := DwordCode.put (DwordCode.put state.memory (field mode layout)
          (CursorEffects.delta ruleOld fresh chosen))
          (layout.head+6) (if chosen then fresh else tapeOld) } := by
  have intact : Intact mode layout ruleOld fresh chosen state.memory := by
    rw [initialized]
    exact initial_intact mode layout ruleOld fresh chosen backing
  exact ⟨trace mode layout valid ruleOld fresh chosen state entry intact cursor,
    effect_rule mode layout valid ruleOld tapeOld fresh chosen state entry intact cursor tape matching⟩

theorem retained_image (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old) :
    Intact mode layout (CursorEffects.delta old fresh chosen) fresh chosen
      (finish mode layout old fresh chosen state).memory := by
  have ready := masked_intact mode layout valid old fresh chosen state entry intact
  rw [masked_effect mode layout valid old fresh chosen state entry intact] at ready
  rw [effect mode layout valid old fresh chosen state entry intact cursor tape]
  apply intact_external mode layout _ fresh chosen _ ready
  rcases valid.tapeOutside with before | after
  · left; omega
  · right; exact after

theorem retained_image_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout ruleOld fresh chosen state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld)
    (matching : chosen = true → ruleOld = tapeOld) :
    Intact mode layout (CursorEffects.delta ruleOld fresh chosen) fresh chosen
      (finish mode layout ruleOld fresh chosen state).memory := by
  have ready := masked_intact mode layout valid ruleOld fresh chosen state entry intact
  rw [masked_effect mode layout valid ruleOld fresh chosen state entry intact] at ready
  rw [effect_rule mode layout valid ruleOld tapeOld fresh chosen state entry intact cursor tape matching]
  apply intact_external mode layout _ fresh chosen _ ready
  rcases valid.tapeOutside with before | after
  · left; omega
  · right; exact after

end SmcTuring.Appendix.InputUpdateTrace
