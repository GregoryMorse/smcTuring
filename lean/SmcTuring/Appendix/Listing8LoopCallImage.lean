module
public import SmcTuring.Appendix.Listing8LoopFailure
public import SmcTuring.Appendix.Listing8CallSelection

public section
namespace SmcTuring.Appendix.Listing8LoopCallImage
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailure.Bounds
abbrev Current:=Listing8LoopFailure.Current

theorem entry_packet (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (callImage : ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin)))) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=
        Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin))) := by
  have coords:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l sentinel begin)
  rw [Listing8LoopFailurePrefix.window mode l t v old sentinel begin b state entry forward current _ _
    (by cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords ⊢ <;> omega) (Nat.le_refl _)]
  exact callImage

theorem entry_operand (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (callImage : ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin)))) :
    DwordCode.get (Listing8LoopState.finish mode l t v state).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+1)=
        Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin) := by
  let region:=Listing8FailureGeometry.region mode l sentinel begin
  let reached:=Listing8LoopState.finish mode l t v state
  have current:=entry_packet mode l t v sentinel begin old b state entry forward current callImage
  have packet:=ByteWindow.packet reached.principal.memory (Listing8FailureLayout.callPC mode region) [0xe8]
    (LittleEndian.wordEncode 4 (Listing8FailureLayout.original mode region)) []
    (by simpa only [region,reached,Native.encode,List.append_nil,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length] using current)
  change ByteMemory.bytesAt reached.principal.memory (Listing8FailureLayout.callPC mode region+1) 4=LittleEndian.wordEncode 4 _ at packet
  have decoded : ByteMemory.readWord .x86 reached.principal.memory (Listing8FailureLayout.callPC mode region+1)=some (Listing8FailureLayout.original mode region) := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt _ _ 4)=some _
    rw [packet,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem call_packet (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (callImage : ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin)))) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=
        Native.encode mode (.callRelative (if Listing8LoopFailure.failed mode l t v sentinel begin state then 0 else
          Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin))) := by
  let region:=Listing8FailureGeometry.region mode l sentinel begin
  rw [Listing8LoopFailure.memory_effect mode l t v sentinel begin old b state entry forward current,
    entry_operand mode l t v sentinel begin old b state entry forward current callImage,Listing8CallSelection.toggle_selection]
  apply Listing8CallSelection.operand_current
  have maskBefore : Listing8FailureLayout.mask mode region+4≤Listing8FailureLayout.callPC mode region := by
    cases mode <;> simp [Listing8FailureLayout.mask,Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan] <;> omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤Listing8FailureLayout.callPC mode region := by
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    omega
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl maskBefore),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by simpa only [Nat.add_assoc] using andBefore))]
  exact entry_packet mode l t v sentinel begin old b state entry forward current callImage

theorem call_fetch (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (callImage : ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)) 5=Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin)))) :
    StringControl.fetch mode (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin))=
        some (.previous (StringDwordCopy.native mode (.callRelative (if Listing8LoopFailure.failed mode l t v sentinel begin state then 0 else
          Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin))))) :=
  StringControl.previous_fetch mode _ _ _ (StringDwordCopy.native_encoding mode _ _ _
    (call_packet mode l t v sentinel begin old b state entry forward current callImage))

end SmcTuring.Appendix.Listing8LoopCallImage
