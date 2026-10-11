module
public import SmcTuring.Appendix.Listing8GlobalFailure
public import SmcTuring.Appendix.Listing8StateValues

public section
namespace SmcTuring.Appendix.Listing8FailureGlobalValues
open Native Listing8CopyImage Listing8FailureGeometry
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def failed (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailureValues.failed mode (region mode l sentinel begin)
    (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory

theorem failure_condition (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode l t v sentinel begin extra seed=
      decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel) := by
  unfold failed Listing8FailureValues.failed
  change decide (MixedMemory.getWord mode
    (Listing8GlobalState.finish mode l t v (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed).principal.memory
    (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode sentinel)= _
  rw [Listing8StateValues.transition mode l t v r owners copies bounds.state _ seed]

theorem call_original (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin)+1)=Listing8FailureLayout.original mode (region mode l sentinel begin) := by
  have current:=Listing8FailureGlobalImage.current_call mode l t v sentinel begin r owners copies bounds extra seed
  have packet:=ByteWindow.packet (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory
    (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) [0xe8]
    (LittleEndian.wordEncode 4 (Listing8FailureLayout.original mode (region mode l sentinel begin))) []
    (by simpa only [Listing8GlobalFailure.entryState,Listing8FailureGlobalImage.callBytes,Native.encode,List.append_nil,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length] using current)
  change ByteMemory.bytesAt (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory
    (Listing8FailureLayout.callPC mode (region mode l sentinel begin)+1) 4=LittleEndian.wordEncode 4 _ at packet
  have decoded : ByteMemory.readWord .x86 (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin)+1)=some (Listing8FailureLayout.original mode (region mode l sentinel begin)) := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt _ _ 4)=some _
    rw [packet,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem call_value (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin)+1)=
      if failed mode l t v sentinel begin extra seed then 0 else Listing8FailureLayout.original mode (region mode l sentinel begin) := by
  rw [Listing8GlobalFailure.finish,Listing8FailureValues.memory mode (region mode l sentinel begin)
    (local_bounds mode l t sentinel begin r bounds) _ (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed),DwordCode.get_put,
    call_original mode l t v sentinel begin r owners copies bounds extra seed,Listing8CallSelection.toggle_selection]
  rfl

theorem call_packet (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) 5=
      Native.encode mode (.callRelative (if failed mode l t v sentinel begin extra seed then 0 else Listing8FailureLayout.original mode (region mode l sentinel begin))) := by
  rw [Listing8GlobalFailure.finish,Listing8FailureValues.memory mode (region mode l sentinel begin)
    (local_bounds mode l t sentinel begin r bounds) _ (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed),
    call_original mode l t v sentinel begin r owners copies bounds extra seed,Listing8CallSelection.toggle_selection]
  apply Listing8CallSelection.operand_current
  have maskBefore : Listing8FailureLayout.mask mode (region mode l sentinel begin)+4 ≤ Listing8FailureLayout.callPC mode (region mode l sentinel begin) := by
    cases mode <;> simp [Listing8FailureLayout.mask,Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan] <;> omega
  have andBefore : Listing8FailureLayout.andPC mode (region mode l sentinel begin)+10 ≤ Listing8FailureLayout.callPC mode (region mode l sentinel begin) := by
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    omega
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl maskBefore),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by simpa only [Nat.add_assoc] using andBefore))]
  exact Listing8FailureGlobalImage.current_call mode l t v sentinel begin r owners copies bounds extra seed

/-- The selected CALL packet is present in the current post-mask memory.
The intervening printed stack prefix still needs its execution/frame proof. -/
theorem call_fetch (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringControl.fetch mode (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin))=
      some (.previous (StringDwordCopy.native mode (.callRelative
        (if failed mode l t v sentinel begin extra seed then 0 else Listing8FailureLayout.original mode (region mode l sentinel begin))))) :=
  StringControl.previous_fetch mode _ _ _ (StringDwordCopy.native_encoding mode _ _ _
    (call_packet mode l t v sentinel begin r owners copies bounds extra seed))

theorem before_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ (region mode l sentinel begin).start) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory observed count := by
  apply Listing8FailureValues.window mode (region mode l sentinel begin) (local_bounds mode l t sentinel begin r bounds) _
    (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
  all_goals right
  all_goals have coords:=Listing8FailureLayout.positions mode (region mode l sentinel begin)
  all_goals cases mode
  all_goals simp [Listing8FailureLayout.andPC,Listing8FailureLayout.storePC] at coords ⊢ <;> omega

theorem transition (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory
      (Listing8StateGeometry.region mode l).cursor=if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next := by
  have before:=(local_bounds mode l t sentinel begin r bounds).cursorBefore
  have frame:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (before_window mode l t v sentinel begin r owners copies bounds extra seed (region mode l sentinel begin).cursor mode.wordBytes before)
  change MixedMemory.getWord mode (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
    MixedMemory.getWord mode (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory (Listing8StateGeometry.region mode l).cursor at frame
  rw [frame]
  exact Listing8StateValues.transition mode l t v r owners copies bounds.state _ seed

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction=if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward) else Arithmetic.encodeNat mode l.sourceNode := by
  have first:=Listing8StateFields.first_cursor_before mode l t bounds.state
  have second:=(local_bounds mode l t sentinel begin r bounds).cursorBefore
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes ≤ (region mode l sentinel begin).start at second
  have before : l.input.cursor+mode.wordBytes ≤ (region mode l sentinel begin).start := by omega
  have frame:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (before_window mode l t v sentinel begin r owners copies bounds extra seed l.input.cursor mode.wordBytes before)
  change MixedMemory.getWord mode (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory _=
    MixedMemory.getWord mode (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory _ at frame
  rw [frame]
  exact Listing8StateValues.head mode l t v r owners copies bounds.state _ seed takeBack encoded

theorem tape (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  have frame : ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory (l.sourceNode+6) 4=
      ByteMemory.bytesAt (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory (l.sourceNode+6) 4 := by
    rcases bounds.nodeOutside with early | late
    · apply before_window mode l t v sentinel begin r owners copies bounds extra seed
      have coords:=positions mode l t sentinel begin bounds
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
    · apply Listing8FailureValues.window mode (region mode l sentinel begin) (local_bounds mode l t sentinel begin r bounds) _
        (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
        (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
      all_goals left
      all_goals cases mode
      all_goals simp [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan,
        Listing8FailureLayout.mask,Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC] at late ⊢ <;> omega
  have value:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory (l.sourceNode+6)=
    DwordCode.get (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed).principal.memory (l.sourceNode+6) at value
  rw [value]
  exact Listing8StateValues.tape mode l t v r owners copies bounds.state _ seed

end SmcTuring.Appendix.Listing8FailureGlobalValues
