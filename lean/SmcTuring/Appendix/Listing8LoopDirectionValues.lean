module
public import SmcTuring.Appendix.Listing8LoopDirection
public import SmcTuring.Appendix.Listing8LoopPointerValues
public import SmcTuring.Appendix.Listing8DirectionFields

public section
namespace SmcTuring.Appendix.Listing8LoopDirectionValues
open Native Listing8CopyImage Listing8DirectionGeometry Listing8DirectionFields
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirection.Bounds
abbrev Current:=Listing8LoopDirection.Current

theorem input_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed : Nat) (member : observed∈fields mode l) :
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory observed=
      DwordCode.get (Listing8MainPrefix.finish mode l t v state).principal.memory observed := by
  have frame:=Listing8MainInputFrames.input_window mode l t v old b.input state entry forward current.input observed 4
    (input_outside mode l t b.direction observed member)
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame

theorem back_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory (Listing8DirectionLayout.backPC mode (Listing8DirectionGeometry.region mode l)+6)=low mode v.back := by
  rw [input_frame mode l t v old b state entry forward current _ (by simp [fields]),←b.direction.back,Listing8LoopPointerValues.memory_effect mode l t v b.input.input.prefixBounds state entry forward current.input.prefixCurrent]
  rw [pointer_frame mode _ t.forward v.forward (t.back+6) (Or.inr (by
    rw [b.direction.back,b.direction.forward]
    cases mode <;> simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount])),pointer_low]

theorem forward_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory (Listing8DirectionLayout.forwardPC mode (Listing8DirectionGeometry.region mode l)+6)=low mode v.forward := by
  rw [input_frame mode l t v old b state entry forward current _ (by simp [fields]),←b.direction.forward,Listing8LoopPointerValues.memory_effect mode l t v b.input.input.prefixBounds state entry forward current.input.prefixCurrent]
  exact pointer_low mode _ _ _

theorem back_high (l : Layout) (t : Targets) (v : Values .x64) (old : OldInput) (b : Bounds .x64 l t v)
    (state : StringExecution.State .x64) (entry : state.principal.pc=Arithmetic.encodeNat .x64 l.start)
    (forward : state.backwards=false) (current : Current .x64 l t v old state.principal.memory) :
    DwordCode.get (Listing8MainInput.finish .x64 l t v state).principal.memory (Listing8DirectionLayout.backPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=X64.HalfWords.high v.back := by
  rw [input_frame .x64 l t v old b state entry forward current _ (by simp [fields]),←b.direction.back,Listing8LoopPointerValues.memory_effect .x64 l t v b.input.input.prefixBounds state entry forward current.input.prefixCurrent]
  rw [pointer_frame .x64 _ t.forward v.forward (t.back+16) (Or.inr (by
    rw [b.direction.back,b.direction.forward]
    simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount])),pointer_high]

theorem forward_high (l : Layout) (t : Targets) (v : Values .x64) (old : OldInput) (b : Bounds .x64 l t v)
    (state : StringExecution.State .x64) (entry : state.principal.pc=Arithmetic.encodeNat .x64 l.start)
    (forward : state.backwards=false) (current : Current .x64 l t v old state.principal.memory) :
    DwordCode.get (Listing8MainInput.finish .x64 l t v state).principal.memory (Listing8DirectionLayout.forwardPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=X64.HalfWords.high v.forward := by
  rw [input_frame .x64 l t v old b state entry forward current _ (by simp [fields]),←b.direction.forward,Listing8LoopPointerValues.memory_effect .x64 l t v b.input.input.prefixBounds state entry forward current.input.prefixCurrent]
  exact pointer_high _ _ _

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)+6)=v.direction := by
  rw [input_frame mode l t v old b state entry forward current _ (by simp [fields]),←b.direction.direction,
    Listing8LoopPointerValues.memory_effect mode l t v b.input.input.prefixBounds state entry forward current.input.prefixCurrent]
  have coordinates := Listing8DirectionLayout.positions mode (region mode l)
  have forwardFrame : t.forward+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [b.direction.forward,b.direction.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have backFrame : t.back+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [b.direction.back,b.direction.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have stateFrame : l.direction+6+4 ≤ t.state+6 := by
    have after := b.direction.stateAfter
    rw [b.direction.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  rw [pointer_frame mode _ t.forward v.forward (l.direction+6) (Or.inl forwardFrame),
    pointer_frame mode _ t.back v.back (l.direction+6) (Or.inl backFrame),
    pointer_frame mode _ t.state v.newState (l.direction+6) (Or.inr stateFrame)]
  have codeBefore := Listing8PointerCopies.cursor_before mode l
  have inputBefore := b.input.input.prefixBounds.resources.inputAfter
  have spans := positions mode l t b.direction
  have input := Listing8InputBounds.positions mode l t b.direction.input.fields b.direction.input.joined
  have cursorBefore : StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ l.direction+6 := by
    change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ codeEnd mode l at codeBefore
    rw [b.direction.direction]
    simp only [region] at coordinates ⊢
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input coordinates ⊢ <;> omega
  rw [DwordDataflow.word_frame mode _ _ (l.direction+6) v.next (Or.inl cursorBefore),
    (Listing8MainLiveOwners.result mode l v b.input.input.prefixBounds.resources b.input.input.prefixBounds.owners b.input.input.prefixBounds.tapeReach state entry forward current.input.prefixCurrent.copying).2.1,DwordCode.get_put]

end SmcTuring.Appendix.Listing8LoopDirectionValues
