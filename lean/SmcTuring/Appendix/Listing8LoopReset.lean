module
public import SmcTuring.Appendix.Listing8LoopHaltImage
public import SmcTuring.Appendix.Listing8GraphNextReset

public section
namespace SmcTuring.Appendix.Listing8LoopReset
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Current:=Listing8LoopHaltImage.Current
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8ResetEffects.finish mode (Listing8LoopHaltImage.region mode origin l g) (Listing8LoopTable.finish mode origin l t g node rule state)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8LoopTable.program mode origin l t g node rule state++((Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map StringControl.Form.previous).map StringStack.Form.previous

theorem reset_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringDword.Trace mode (Listing8LoopTable.finish mode origin l t g node rule state) (Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)) (finish mode origin l t g node rule state) :=
  Listing8ResetTrace.trace mode (Listing8LoopHaltImage.region mode origin l g) (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset _
    (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (program mode origin l t g node rule state) (finish mode origin l t g node rule state) :=
  StringStack.trace_append mode (Listing8LoopTable.trace mode origin l t g node rule ctx old state image.control halted)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (reset_trace mode origin l t g node rule ctx old state image halted)))

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    finish mode origin l t g node rule state={Listing8LoopTable.finish mode origin l t g node rule state with principal:={(Listing8LoopTable.finish mode origin l t g node rule state).principal with
      pc:=Arithmetic.encodeNat mode (Listing8ResetLayout.endPC mode (Listing8LoopHaltImage.region mode origin l g))
      accumulator:=StringInit.accumulator mode (Listing8FullTableImage.start mode origin) (Listing8ResetEffects.afterInput mode (Listing8LoopHaltImage.region mode origin l g) (Listing8LoopTable.finish mode origin l t g node rule state))
      memory:=ByteMemory.putWord mode (ByteMemory.putWord mode (DwordCode.put (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory
        (Listing8JumpLayout.callPC mode origin+1) (Listing8ResetLayout.original (Listing8LoopHaltImage.region mode origin l g))) l.input.cursor (Arithmetic.encodeNat mode (nodePC mode origin g g.halt)))
        (Listing8StateGeometry.region mode l).cursor (Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin))}} := by
  rw [finish,Listing8ResetEffects.effect mode (Listing8LoopHaltImage.region mode origin l g) (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset _
    (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted),
    Listing8LoopHaltImage.after_table_source mode origin l t g node rule ctx old state image halted]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 148 else 194)+11*g.transitions := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8LoopTable.instruction_count,Listing8ResetLayout.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.pc.toNat=Listing8GraphLayout.input mode origin g.transitions := by
  rw [effect mode origin l t g node rule ctx old state image halted,Listing8LoopHaltImage.region,Arithmetic.encode_nat_toNat mode _ (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset.capacity,
    Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body,
    table_length,Listing8GraphReset.endpoint]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.stack=state.principal.stack ∧ (finish mode origin l t g node rule state).principal.carry=false ∧
    (finish mode origin l t g node rule state).sourceIndex=state.sourceIndex ∧ (finish mode origin l t g node rule state).destinationIndex=state.destinationIndex ∧ (finish mode origin l t g node rule state).backwards=false := by
  rw [effect mode origin l t g node rule ctx old state image halted]
  exact Listing8LoopTable.registers mode origin l t g node rule ctx old state image.control halted

theorem input_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [effect mode origin l t g node rule ctx old state image halted,MixedFrames.word_after_word mode _ _ _ _
    (Or.inr (Listing8StateFields.first_cursor_before mode l t ctx.body.state)),MixedMemory.get_put]

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [effect mode origin l t g node rule ctx old state image halted,MixedMemory.get_put]

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) (observed count : Nat) (after : Listing8JumpLayout.callPC mode origin+5≤observed) :
    ByteMemory.bytesAt (finish mode origin l t g node rule state).principal.memory observed count=ByteMemory.bytesAt (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory observed count := by
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  rw [effect mode origin l t g node rule ctx old state image halted,StackWindows.word_window _ _ _ _ _ _ (Or.inl (by omega)),StackWindows.word_window _ _ _ _ _ _ (Or.inl (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega))]

theorem reset_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8ResetPackets.Initial mode (Listing8LoopHaltImage.region mode origin l g) (finish mode origin l t g node rule state).principal.memory := by
  have after : Listing8JumpLayout.callPC mode origin+5≤(Listing8LoopHaltImage.region mode origin l g).start :=
    (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset.callBefore
  rw [Listing8ResetPackets.Initial,window mode origin l t g node rule ctx old state image halted _ _ after]
  exact Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted

end SmcTuring.Appendix.Listing8LoopReset
