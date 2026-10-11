module
public import SmcTuring.Appendix.Listing8SourceEffects

public section
namespace SmcTuring.Appendix.Listing8InputMask
open Native Listing8LiteralInput
abbrev Dword := BitVec 32

/-- The printed AND starts with CNSTFRC32; a subsequent invocation can start
with the previous live mask. Only that initial immediate varies here. -/
@[expose] def leading (mode : Mode) (layout : Layout) (rule tape fresh : Dword) :=
  prefixBytes mode layout rule tape ++ distributionBytes mode layout ++
    DwordArithmetic.encode (InputUpdate.xorForm mode (updateLayout mode layout) fresh) ++ [0x81,0x25] ++
    LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode layout+20) (pendingField mode layout))
@[expose] def trailing (mode : Mode) (layout : Layout) (pending : Dword) :=
  CursorImage.bytes mode (InputUpdate.body (updateLayout mode layout)) pending
@[expose] def bytes (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword) :=
  leading mode layout rule tape fresh ++ LittleEndian.wordEncode 4 oldMask ++ trailing mode layout pending
@[expose] def Intact (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start (bytes mode layout rule tape pending fresh oldMask).length =
    bytes mode layout rule tape pending fresh oldMask
@[expose] def image (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (backing : ByteMemory.Memory) := ByteMemory.putBytes backing layout.start (bytes mode layout rule tape pending fresh oldMask)
@[expose] def normalized (mode : Mode) (layout : Layout) (state : Execution.State mode) :=
  { state with memory := DwordCode.put state.memory (maskField mode layout) 0 }

theorem zero_bytes (mode : Mode) (layout : Layout) (rule tape pending fresh : Dword) :
    bytes mode layout rule tape pending fresh 0 = Listing8LiteralInput.bytes mode layout rule tape pending fresh := by
  have spelling := Listing8InputComposition.update_mask_spelling mode (updateLayout mode layout) pending fresh false
  simp only [InputUpdate.mask,Bool.false_eq_true,ite_false] at spelling
  rw [Listing8LiteralInput.bytes,spelling]
  simp only [bytes,leading,trailing,updateLayout,pendingField,List.append_assoc]

theorem mask_position (mode : Mode) (layout : Layout) (rule tape fresh : Dword) :
    layout.start+(leading mode layout rule tape fresh).length = maskField mode layout := by
  have prefixExtent := prefix_length mode layout rule tape
  have gapLength := distribution_length mode layout
  simp only [leading,List.length_append,DwordArithmetic.encode_length,InputUpdate.xorForm,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,List.length_cons,List.length_nil,
    LittleEndian.word_encode_length]
  unfold maskField updateStart
  omega

theorem bytes_length (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword) :
    layout.start+(bytes mode layout rule tape pending fresh oldMask).length = endPC mode layout := by
  have old := Listing8LiteralInput.bytes_length mode layout rule tape pending fresh
  rw [←zero_bytes] at old
  simpa only [bytes,List.length_append,LittleEndian.word_encode_length] using old

theorem initial_intact (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword) (backing : ByteMemory.Memory) :
    Intact mode layout rule tape pending fresh oldMask (image mode layout rule tape pending fresh oldMask backing) :=
  ByteMemory.bytes_at_put _ _ _

theorem zero_intact (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Intact mode layout rule tape pending fresh oldMask memory) :
    Listing8LiteralInput.Intact mode layout rule tape pending fresh (DwordCode.put memory (maskField mode layout) 0) := by
  have patched := BytePatch.current memory layout.start (leading mode layout rule tape fresh)
    (LittleEndian.wordEncode 4 oldMask) (LittleEndian.wordEncode 4 (0 : Dword)) (trailing mode layout pending)
    (by simp only [LittleEndian.word_encode_length]) current
  rw [mask_position,←bytes,zero_bytes] at patched
  exact patched

theorem reset_same (mode : Mode) (layout : Layout) (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    resetState mode layout state = resetState mode layout (normalized mode layout state) := by
  rw [reset_effect mode layout capacity state entry,reset_effect mode layout capacity (normalized mode layout state) entry]
  simp only [normalized,DwordCode.put_overwrite]

theorem finish_same (mode : Mode) (layout : Layout) (rule tape fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    Listing8LiteralComposition.finish mode layout rule tape fresh state =
      Listing8LiteralComposition.finish mode layout rule tape fresh (normalized mode layout state) := by
  unfold Listing8LiteralComposition.finish Listing8LiteralComposition.distributedState prefixState ownerState copiedState
  rw [reset_same mode layout capacity state entry]

theorem reset_current (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Intact mode layout rule tape pending fresh oldMask memory) :
    ByteMemory.bytesAt memory layout.start 10 = DwordArithmetic.encode (resetForm mode layout) := by
  have packet := ByteWindow.packet memory layout.start [] (DwordArithmetic.encode (resetForm mode layout))
    (DwordMixedImage.bytes mode (copyLayout mode layout) ++ DwordArithmetic.encode (ownerForm mode layout rule) ++
      DwordComparisonTail.bytes mode (tailLayout mode layout) tape ++ distributionBytes mode layout ++
      DwordArithmetic.encode (InputUpdate.xorForm mode (updateLayout mode layout) fresh) ++ [0x81,0x25] ++
      LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode layout+20) (pendingField mode layout)) ++
      LittleEndian.wordEncode 4 oldMask ++ trailing mode layout pending)
    (by simpa only [Intact,bytes,leading,prefixBytes,List.append_assoc,List.nil_append] using current)
  simpa only [List.length_nil,Nat.add_zero,DwordArithmetic.encode_length,resetForm,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length] using packet

theorem replace_head (mode : Mode) (first : MixedDword.Form mode) (rest : List (MixedDword.Form mode))
    (a b final : Execution.State mode) (trace : MixedDword.Trace mode b (first::rest) final)
    (fetched : MixedDword.fetch mode a.memory a.pc.toNat = some first)
    (same : MixedDword.execute mode first a = MixedDword.execute mode first b) :
    MixedDword.Trace mode a (first::rest) final := by
  cases trace with
  | step _ tail => exact .step fetched (same.symm ▸ tail)

/-- The actual first reset store removes every old mask, including the
printed CNSTFRC32. All following fetches come from the normalized image;
there is no host reinitialization step in the resulting trace. -/
theorem trace (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Intact mode layout rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    MixedDword.Trace mode state (Listing8LiteralComposition.program mode layout rule tape fresh)
      (Listing8LiteralComposition.finish mode layout rule tape fresh state) := by
  have zero := zero_intact mode layout rule tape pending fresh oldMask state.memory current
  have cursorFrame := Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  have fromZero := Listing8LiteralComposition.trace mode layout rule tape pending fresh capacity masks update outside
    (normalized mode layout state) entry zero (cursorFrame.trans cursor)
  have startFits : layout.start < 2^(8*mode.wordBytes) := by
    have ending := (positions mode layout).2.2.2.2.2.2.2
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at ending <;> omega
  have first : MixedDword.fetch mode state.memory state.pc.toNat = some (.arithmetic (resetForm mode layout)) := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ startFits]
    exact MixedDword.arithmetic_encoding mode _ _ _ (reset_current mode layout rule tape pending fresh oldMask _ current)
  rw [finish_same mode layout rule tape fresh capacity state entry]
  exact replace_head mode (.arithmetic (resetForm mode layout)) _ state (normalized mode layout state) _ fromZero first
    (reset_same mode layout capacity state entry)

theorem tape_value (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Intact mode layout rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (symbol : DwordCode.get state.memory (layout.head+6) = tape) :
    DwordCode.get (Listing8LiteralComposition.finish mode layout rule tape fresh state).memory (layout.head+6) =
      if chosen rule tape then fresh else tape := by
  have cursorFrame := Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  have tapeFrame := Listing8LiteralComposition.tape_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  rw [finish_same mode layout rule tape fresh capacity state entry]
  exact Listing8SourceEffects.tape_value mode layout rule tape pending fresh capacity masks update outside
    (normalized mode layout state) entry (zero_intact mode layout rule tape pending fresh oldMask _ current)
    (cursorFrame.trans cursor) (tapeFrame.trans symbol)

theorem retained (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Intact mode layout rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (symbol : DwordCode.get state.memory (layout.head+6) = tape) :
    InputUpdate.Intact mode (updateLayout mode layout) (CursorEffects.delta tape fresh (chosen rule tape))
      fresh (chosen rule tape) (Listing8LiteralComposition.finish mode layout rule tape fresh state).memory := by
  have cursorFrame := Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  have tapeFrame := Listing8LiteralComposition.tape_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  rw [finish_same mode layout rule tape fresh capacity state entry]
  exact Listing8SourceEffects.retained mode layout rule tape pending fresh capacity masks update outside
    (normalized mode layout state) entry (zero_intact mode layout rule tape pending fresh oldMask _ current)
    (cursorFrame.trans cursor) (tapeFrame.trans symbol)

end SmcTuring.Appendix.Listing8InputMask
