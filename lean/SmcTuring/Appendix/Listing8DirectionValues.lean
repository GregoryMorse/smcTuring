module
public import SmcTuring.Appendix.Listing8DirectionFields

public section
namespace SmcTuring.Appendix.Listing8DirectionValues
open Native Listing8CopyImage Listing8DirectionGeometry Listing8DirectionFields
abbrev Targets := Listing8PointerCopies.Targets

theorem back_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.backPC mode (region mode l)+6) = low mode v.back := by
  rw [input_frame mode l t v r owners copies bounds extra seed _ (by simp [fields]),←bounds.back,
    Listing8PointerValues.memory_effect mode l t v r owners copies _ seed,
    pointer_frame mode _ t.forward v.forward (t.back+6) (Or.inr (by
      rw [bounds.back,bounds.forward]
      cases mode <;> simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
        Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega)),pointer_low]

theorem forward_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.forwardPC mode (region mode l)+6) = low mode v.forward := by
  rw [input_frame mode l t v r owners copies bounds extra seed _ (by simp [fields]),←bounds.forward,
    Listing8PointerValues.memory_effect mode l t v r owners copies _ seed,pointer_low]

theorem back_high (l : Layout) (t : Targets) (v : Values .x64) (r : Resources .x64 l)
    (owners : Listing8CopiedOwners.Bounds .x64 l v) (copies : Listing8PointerCopies.Bounds .x64 l t)
    (bounds : Bounds .x64 l t) (extra : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GlobalDirection.entryState .x64 l t v extra seed).principal.memory
      (Listing8DirectionLayout.backPC .x64 (region .x64 l)+16) = X64.HalfWords.high v.back := by
  rw [input_frame .x64 l t v r owners copies bounds extra seed _ (by simp [fields]),←bounds.back,
    Listing8PointerValues.memory_effect .x64 l t v r owners copies _ seed,
    pointer_frame .x64 _ t.forward v.forward (t.back+16) (Or.inr (by
      rw [bounds.back,bounds.forward]
      simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
        Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega)),pointer_high]

theorem forward_high (l : Layout) (t : Targets) (v : Values .x64) (r : Resources .x64 l)
    (owners : Listing8CopiedOwners.Bounds .x64 l v) (copies : Listing8PointerCopies.Bounds .x64 l t)
    (bounds : Bounds .x64 l t) (extra : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GlobalDirection.entryState .x64 l t v extra seed).principal.memory
      (Listing8DirectionLayout.forwardPC .x64 (region .x64 l)+16) = X64.HalfWords.high v.forward := by
  rw [input_frame .x64 l t v r owners copies bounds extra seed _ (by simp [fields]),←bounds.forward,
    Listing8PointerValues.memory_effect .x64 l t v r owners copies _ seed,pointer_high]

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC mode (region mode l)+6) = v.direction := by
  rw [input_frame mode l t v r owners copies bounds extra seed _ (by simp [fields]),←bounds.direction,
    Listing8PointerValues.memory_effect mode l t v r owners copies _ seed]
  have coordinates := Listing8DirectionLayout.positions mode (region mode l)
  have forwardFrame : t.forward+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [bounds.forward,bounds.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have backFrame : t.back+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [bounds.back,bounds.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have stateFrame : l.direction+6+4 ≤ t.state+6 := by
    have after := bounds.stateAfter
    rw [bounds.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  rw [pointer_frame mode _ t.forward v.forward (l.direction+6) (Or.inl forwardFrame),
    pointer_frame mode _ t.back v.back (l.direction+6) (Or.inl backFrame),
    pointer_frame mode _ t.state v.newState (l.direction+6) (Or.inr stateFrame)]
  have codeBefore := Listing8PointerCopies.cursor_before mode l
  have inputBefore := r.inputAfter
  have spans := positions mode l t bounds
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  have cursorBefore : StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ l.direction+6 := by
    change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ codeEnd mode l at codeBefore
    rw [bounds.direction]
    simp only [region] at coordinates ⊢
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input coordinates ⊢ <;> omega
  rw [DwordDataflow.word_frame mode _ _ (l.direction+6) v.next (Or.inl cursorBefore),
    Listing8PointerImage.ownerFinish,(Listing8CopiedOwners.result mode l v r owners _ seed).2.1,DwordCode.get_put]

end SmcTuring.Appendix.Listing8DirectionValues
