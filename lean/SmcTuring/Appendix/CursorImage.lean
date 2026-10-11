module
public import SmcTuring.Appendix.CursorEffects
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Appendix.CursorImage
open Native CursorLayout CursorEffects
@[expose] def span (mode : Mode) : Nat := 2*exchangeSize mode+7
@[expose] def bytes (mode : Mode) (layout : Layout) (value : BitVec 32) : List LittleEndian.Byte :=
  MixedDword.encode mode (first mode layout) ++ MixedDword.encode mode (middle mode value) ++
    MixedDword.encode mode (last mode layout)
@[expose] def image (mode : Mode) (layout : Layout) (value : BitVec 32) (backing : ByteMemory.Memory) :
    ByteMemory.Memory := ByteMemory.putBytes backing layout.start (bytes mode layout value)
@[expose] def Intact (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start (span mode) = bytes mode layout value

theorem length (mode : Mode) (layout : Layout) (value : BitVec 32) : (bytes mode layout value).length = span mode := by
  simp only [bytes,List.length_append,MixedDword.encode_length,(lengths mode layout value).1,
    (lengths mode layout value).2.1,(lengths mode layout value).2.2,span]
  omega

theorem initial_intact (mode : Mode) (layout : Layout) (value : BitVec 32) (backing : ByteMemory.Memory) :
    Intact mode layout value (image mode layout value backing) := by
  rw [Intact,←length mode layout value]
  exact ByteMemory.bytes_at_put _ _ _

theorem first_current (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value memory) :
    ByteMemory.bytesAt memory layout.start (MixedDword.encode mode (first mode layout)).length =
      MixedDword.encode mode (first mode layout) := by
  have current : ByteMemory.bytesAt memory layout.start (bytes mode layout value).length = bytes mode layout value :=
    by simpa only [length,Intact] using intact
  exact ByteWindow.packet memory layout.start [] _ (MixedDword.encode mode (middle mode value) ++
    MixedDword.encode mode (last mode layout)) (by simpa [bytes,List.append_assoc] using current)

theorem middle_current (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value memory) :
    ByteMemory.bytesAt memory (middlePC mode layout) (MixedDword.encode mode (middle mode value)).length =
      MixedDword.encode mode (middle mode value) := by
  have current : ByteMemory.bytesAt memory layout.start (bytes mode layout value).length = bytes mode layout value :=
    by simpa only [length,Intact] using intact
  have found := ByteWindow.packet memory layout.start (MixedDword.encode mode (first mode layout))
    (MixedDword.encode mode (middle mode value)) (MixedDword.encode mode (last mode layout))
    (by simpa [bytes] using current)
  simpa only [MixedDword.encode_length,(lengths mode layout value).1,middlePC] using found

theorem last_current (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value memory) :
    ByteMemory.bytesAt memory (lastPC mode layout) (MixedDword.encode mode (last mode layout)).length =
      MixedDword.encode mode (last mode layout) := by
  have current : ByteMemory.bytesAt memory layout.start (bytes mode layout value).length = bytes mode layout value :=
    by simpa only [length,Intact] using intact
  have found := ByteWindow.packet memory layout.start
    (MixedDword.encode mode (first mode layout) ++ MixedDword.encode mode (middle mode value))
    (MixedDword.encode mode (last mode layout)) [] (by simpa [bytes,List.append_assoc] using current)
  simpa only [List.length_append,MixedDword.encode_length,(lengths mode layout value).1,
    (lengths mode layout value).2.1,lastPC,middlePC,Nat.add_assoc] using found

theorem intact_wide (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value memory) (field : Nat) (word : Word mode)
    (outside : field+mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ field) :
    Intact mode layout value (ByteMemory.putWord mode memory field word) := by
  rw [Intact,ByteMemory.putWord,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index
    have bound := index.isLt
    have endPoint := endpoint mode layout
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    unfold span at bound
    rcases outside with before | after <;> omega

theorem intact_dword (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value memory) (field : Nat) (word : BitVec 32)
    (outside : field+4 ≤ layout.start ∨ endPC mode layout ≤ field) :
    Intact mode layout value (DwordCode.put memory field word) := by
  rw [Intact,DwordCode.put,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index
    have bound := index.isLt
    have endPoint := endpoint mode layout
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    unfold span at bound
    rcases outside with before | after <;> omega

theorem swapped_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout value state.memory) :
    Intact mode layout value (swapped mode layout state).memory := by
  rw [swapped_effect mode layout valid state entry]
  exact intact_wide mode layout value state.memory intact layout.cursor state.accumulator valid.cursorOutside

theorem updated_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (intact : Intact mode layout value state.memory) :
    Intact mode layout value (updated mode layout value state).memory := by
  rw [updated_effect mode layout valid value state entry cursor]
  have saved := intact_wide mode layout value state.memory intact layout.cursor state.accumulator valid.cursorOutside
  apply intact_dword mode layout value _ saved
  · rcases valid.tapeOutside with before | after
    · left; omega
    · right; exact after

theorem finish_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (intact : Intact mode layout value state.memory) :
    Intact mode layout value (finish mode layout value state).memory := by
  rw [finish_effect mode layout valid value state entry cursor]
  apply intact_dword mode layout value state.memory intact
  rcases valid.tapeOutside with before | after
  · left; omega
  · right; exact after

theorem trace (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (intact : Intact mode layout value state.memory) :
    MixedDword.Trace mode state (program mode layout value) (finish mode layout value state) := by
  have firstPC : state.pc.toNat = layout.start := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ (by
      have limit := valid.codeFits
      have bound := endpoint mode layout
      omega)]
  have middlePCeq : (swapped mode layout state).pc.toNat = middlePC mode layout := by
    rw [swapped_pc mode layout valid state entry,Arithmetic.encode_nat_toNat mode _ (by
      have limit := valid.codeFits
      unfold endPC lastPC at limit
      omega)]
  have lastPCeq : (updated mode layout value state).pc.toNat = lastPC mode layout := by
    rw [updated_pc mode layout valid value state entry cursor,Arithmetic.encode_nat_toNat mode _ (by
      have limit := valid.codeFits
      unfold endPC at limit
      omega)]
  have a : MixedDword.fetch mode state.memory state.pc.toNat = some (first mode layout) := by
    rw [firstPC]
    exact MixedDword.current_encoding mode _ _ _ (first_current mode layout value _ intact)
  have b : MixedDword.fetch mode (swapped mode layout state).memory (swapped mode layout state).pc.toNat =
      some (middle mode value) := by
    rw [middlePCeq]
    exact MixedDword.current_encoding mode _ _ _ (middle_current mode layout value _
      (swapped_intact mode layout valid value state entry intact))
  have c : MixedDword.fetch mode (updated mode layout value state).memory (updated mode layout value state).pc.toNat =
      some (last mode layout) := by
    rw [lastPCeq]
    exact MixedDword.current_encoding mode _ _ _ (last_current mode layout value _
      (updated_intact mode layout valid value state entry cursor intact))
  exact .step a (.step b (.step c (.nil _)))

theorem original_trace (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (backing : ByteMemory.Memory)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (initialized : state.memory = image mode layout value backing) :
    MixedDword.Trace mode state (program mode layout value) (finish mode layout value state) := by
  apply trace mode layout valid value state entry cursor
  rw [initialized]
  exact initial_intact mode layout value backing

theorem correct (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : BitVec 32)
    (chosen : Bool) (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old)
    (intact : Intact mode layout (delta old fresh chosen) state.memory) :
    MixedDword.Trace mode state (program mode layout (delta old fresh chosen)) (finish mode layout (delta old fresh chosen) state) ∧
    finish mode layout (delta old fresh chosen) state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put state.memory (layout.head+6) (if chosen then fresh else old) } ∧
    Intact mode layout (delta old fresh chosen) (finish mode layout (delta old fresh chosen) state).memory :=
  ⟨trace mode layout valid _ state entry cursor intact,selected_effect mode layout valid old fresh chosen state entry cursor tape,
    finish_intact mode layout valid _ state entry cursor intact⟩

theorem pure (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : BitVec 32)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (owned : Nat → Nat → Prop) (cursorOwned : owned layout.cursor mode.wordBytes) (tapeOwned : owned (layout.head+6) 4) :
    MixedDword.OwnedRun mode owned (program mode layout value) state := by
  have firstTarget : (MixedDword.address mode (first mode layout) state).toNat = layout.cursor := by
    rw [first,MixedDword.exchange_address,first_hits mode layout valid state entry,cursor_toNat mode layout valid]
  have middleTarget : (MixedDword.address mode (middle mode value) (swapped mode layout state)).toNat = layout.head+6 := by
    rw [swapped_effect mode layout valid state entry,cursor]
    change (Arithmetic.encodeNat mode layout.head+Arithmetic.encodeNat mode 6).toNat = layout.head+6
    rw [show Arithmetic.encodeNat mode layout.head+Arithmetic.encodeNat mode 6 =
      Arithmetic.encodeNat mode (layout.head+6) from BitVec.ofNat_add_ofNat _ _,head_toNat mode layout valid]
  have lastTarget : (MixedDword.address mode (last mode layout) (updated mode layout value state)).toNat = layout.cursor := by
    rw [last,MixedDword.exchange_address,last_hits mode layout valid _ (updated_pc mode layout valid value state entry cursor),
      cursor_toNat mode layout valid]
  change owned (MixedDword.address mode (first mode layout) state).toNat (MixedDword.width mode (first mode layout)) ∧
    owned (MixedDword.address mode (middle mode value) (swapped mode layout state)).toNat (MixedDword.width mode (middle mode value)) ∧
    owned (MixedDword.address mode (last mode layout) (updated mode layout value state)).toNat (MixedDword.width mode (last mode layout)) ∧ True
  have firstSize : MixedDword.width mode (first mode layout) = mode.wordBytes :=
    MixedDword.exchange_width mode (firstDisp mode layout)
  have lastSize : MixedDword.width mode (last mode layout) = mode.wordBytes :=
    MixedDword.exchange_width mode (lastDisp mode layout)
  rw [firstTarget,middleTarget,lastTarget,firstSize,lastSize]
  exact ⟨cursorOwned,tapeOwned,cursorOwned,True.intro⟩

end SmcTuring.Appendix.CursorImage
