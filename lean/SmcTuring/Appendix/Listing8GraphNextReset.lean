module
public import SmcTuring.Appendix.Listing8GraphNextResetImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextReset
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8ResetEffects.finish mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))
    (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextTable.program mode origin l t g node rule target memory seed++
    ((Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))).map StringControl.Form.previous).map StringStack.Form.previous

theorem reset_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringDword.Trace mode (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed)
      (Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8ResetTrace.trace mode _ (Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx) _
    (Listing8GraphNextTable.endpoint mode origin l t g node rule target ctx selected memory seed halted)
    (Listing8GraphNextResetImage.after_table mode origin l t g node rule target ctx selected memory seed halted)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextTable.trace mode origin l t g node rule target ctx selected memory seed halted)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (reset_trace mode origin l t g node rule target ctx selected memory seed halted)))

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let state:=Listing8GraphNextTable.finish mode origin l t g node rule target memory seed
    let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
    finish mode origin l t g node rule target memory seed={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (Listing8ResetLayout.endPC mode reset)
      accumulator:=StringInit.accumulator mode (Listing8FullTableImage.start mode origin) (Listing8ResetEffects.afterInput mode reset state)
      memory:=ByteMemory.putWord mode (ByteMemory.putWord mode (DwordCode.put state.principal.memory (Listing8JumpLayout.callPC mode origin+1)
        (Listing8ResetLayout.original reset)) l.input.cursor (Arithmetic.encodeNat mode (nodePC mode origin g g.halt)))
        (Listing8StateGeometry.region mode l).cursor (Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin))}} := by
  rw [finish,Listing8ResetEffects.effect mode _ (Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx) _
    (Listing8GraphNextTable.endpoint mode origin l t g node rule target ctx selected memory seed halted)
    (Listing8GraphNextResetImage.after_table mode origin l t g node rule target ctx selected memory seed halted),
    Listing8GraphNextResetImage.source_value mode origin l t g node rule target ctx selected memory seed halted]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 295 else 389)+11*g.transitions := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextTable.instruction_count,Listing8ResetLayout.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=Listing8GraphLayout.input mode origin g.transitions := by
  rw [effect mode origin l t g node rule target ctx selected memory seed halted,
    Arithmetic.encode_nat_toNat mode _ (Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx).capacity,
    Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body,
    table_length,Listing8GraphReset.endpoint]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false := by
  rw [effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GraphNextTable.registers mode origin l t g node rule target ctx selected memory seed halted

theorem cursors_before_call (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    l.input.cursor+mode.wordBytes≤Listing8JumpLayout.callPC mode origin ∧
    (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8JumpLayout.callPC mode origin := by
  have first:=Listing8StateFields.first_cursor_before mode l t ctx.body.state
  have second:=(Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body).cursorBefore
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤(Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start at second
  let fragment:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have coords:=Listing8FailureLayout.positions mode fragment
  have before : fragment.start≤Listing8FailureLayout.callPC mode fragment := by
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords ⊢ <;> omega
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode fragment=Listing8JumpLayout.callPC mode origin at position
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤fragment.start at second
  rw [position] at before
  exact ⟨by omega,Nat.le_trans second before⟩

theorem input_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [effect mode origin l t g node rule target ctx selected memory seed halted,
    MixedFrames.word_after_word mode _ _ _ _ (Or.inr (Listing8StateFields.first_cursor_before mode l t ctx.body.state)),MixedMemory.get_put]

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [effect mode origin l t g node rule target ctx selected memory seed halted,MixedMemory.get_put]

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
    (observed count : Nat) (after : Listing8JumpLayout.callPC mode origin+5≤observed) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have cursors:=cursors_before_call mode origin l t g node rule ctx
  rw [effect mode origin l t g node rule target ctx selected memory seed halted,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl (by omega)),StackWindows.word_window _ _ _ _ _ _ (Or.inl (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega))]

theorem reset_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [Listing8ResetPackets.Initial,window mode origin l t g node rule target ctx selected memory seed halted _ _
    (Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx).callBefore]
  exact Listing8GraphNextResetImage.after_table mode origin l t g node rule target ctx selected memory seed halted

end SmcTuring.Appendix.Listing8GraphNextReset
