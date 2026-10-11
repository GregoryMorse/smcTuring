module
public import SmcTuring.Appendix.Listing8GraphNextHead

public section
namespace SmcTuring.Appendix.Listing8GraphNextDirectionValues
open Native Listing8CopyImage Listing8DirectionGeometry Listing8DirectionFields Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem input_frame (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed : Nat) (member : observed∈fields mode l) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed=
      DwordCode.get (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed := by
  have disjoint:=input_outside mode (nextLayout mode origin l g node rule target) t
    (Listing8GraphNextDirectionBounds.direction mode origin l t g node rule target ctx) observed member
  have frame:=Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) observed 4 disjoint
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame

theorem back_low (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.backPC mode (Listing8DirectionGeometry.region mode l)+6)=low mode (liveValues mode origin g node rule target).back := by
  rw [input_frame mode origin l t g node rule target ctx selected memory seed _ (by simp [fields]),←ctx.body.state.head.back,Listing8GraphNextPointerValues.memory_effect mode origin l t g node rule target ctx selected memory seed]
  rw [pointer_frame mode _ t.forward (liveValues mode origin g node rule target).forward (t.back+6) (Or.inr (by
    rw [ctx.body.state.head.back,ctx.body.state.head.forward]
    cases mode <;> simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega)),pointer_low]

theorem forward_low (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.forwardPC mode (Listing8DirectionGeometry.region mode l)+6)=low mode (liveValues mode origin g node rule target).forward := by
  rw [input_frame mode origin l t g node rule target ctx selected memory seed _ (by simp [fields]),←ctx.body.state.head.forward,Listing8GraphNextPointerValues.memory_effect mode origin l t g node rule target ctx selected memory seed]
  exact pointer_low mode _ _ _

theorem back_high (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context  .x64 origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GraphNextInput.finish .x64 origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.backPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=X64.HalfWords.high (liveValues .x64 origin g node rule target).back := by
  rw [input_frame .x64 origin l t g node rule target ctx selected memory seed _ (by simp [fields]),←ctx.body.state.head.back,Listing8GraphNextPointerValues.memory_effect .x64 origin l t g node rule target ctx selected memory seed]
  rw [pointer_frame .x64 _ t.forward (liveValues .x64 origin g node rule target).forward (t.back+16) (Or.inr (by
    rw [ctx.body.state.head.back,ctx.body.state.head.forward]
    simp [Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega)),pointer_high]

theorem forward_high (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context  .x64 origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GraphNextInput.finish .x64 origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.forwardPC .x64 (Listing8DirectionGeometry.region .x64 l)+16)=X64.HalfWords.high (liveValues .x64 origin g node rule target).forward := by
  rw [input_frame .x64 origin l t g node rule target ctx selected memory seed _ (by simp [fields]),←ctx.body.state.head.forward,Listing8GraphNextPointerValues.memory_effect .x64 origin l t g node rule target ctx selected memory seed]
  exact pointer_high _ _ _

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)+6)=(liveValues mode origin g node rule target).direction := by
  rw [input_frame mode origin l t g node rule target ctx selected memory seed _ (by simp [fields]),←ctx.body.state.head.direction,
    Listing8GraphNextPointerValues.memory_effect mode origin l t g node rule target ctx selected memory seed]
  have coordinates := Listing8DirectionLayout.positions mode (region mode l)
  have forwardFrame : t.forward+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [ctx.body.state.head.forward,ctx.body.state.head.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have backFrame : t.back+(if mode = .x86 then 10 else 20) ≤ l.direction+6 := by
    rw [ctx.body.state.head.back,ctx.body.state.head.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  have stateFrame : l.direction+6+4 ≤ t.state+6 := by
    have after := ctx.body.state.head.stateAfter
    rw [ctx.body.state.head.direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates ⊢ <;> omega
  rw [pointer_frame mode _ t.forward (liveValues mode origin g node rule target).forward (l.direction+6) (Or.inl forwardFrame),
    pointer_frame mode _ t.back (liveValues mode origin g node rule target).back (l.direction+6) (Or.inl backFrame),
    pointer_frame mode _ t.state (liveValues mode origin g node rule target).newState (l.direction+6) (Or.inr stateFrame)]
  have codeBefore := Listing8PointerCopies.cursor_before mode l
  have inputBefore := ctx.resources.inputAfter
  have spans := positions mode l t ctx.body.state.head
  have input := Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have cursorBefore : StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ l.direction+6 := by
    change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes ≤ codeEnd mode l at codeBefore
    rw [ctx.body.state.head.direction]
    simp only [region] at coordinates ⊢
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input coordinates ⊢ <;> omega
  rw [DwordDataflow.word_frame mode _ _ (l.direction+6) (liveValues mode origin g node rule target).next (Or.inl cursorBefore),
    (Listing8GraphNextOwners.result mode origin l t g node rule target ctx selected memory seed).2.1,DwordCode.get_put]

end SmcTuring.Appendix.Listing8GraphNextDirectionValues
