module
public import SmcTuring.Appendix.Listing8LoopResetOutput

public section
namespace SmcTuring.Appendix.Listing8LoopTerminal
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8NodeTrace.finish mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (Listing8LoopReset.finish mode origin l t g node rule state)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8LoopReset.program mode origin l t g node rule state++((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map StringControl.Form.previous).map StringStack.Form.previous

theorem input_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (Listing8LoopReset.finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions) := by
  rw [Listing8LoopReset.effect mode origin l t g node rule ctx old state image halted,Listing8LoopHaltImage.region,
    Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body,
    table_length,Listing8GraphReset.endpoint]

theorem input_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringDword.Trace mode (Listing8LoopReset.finish mode origin l t g node rule state) (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))) (finish mode origin l t g node rule state) :=
  Listing8NodeTrace.trace mode _ _ (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)) _
    (input_entry mode origin l t g node rule ctx old state image halted) (Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted).1

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (program mode origin l t g node rule state) (finish mode origin l t g node rule state) :=
  StringStack.trace_append mode (Listing8LoopReset.trace mode origin l t g node rule ctx old state image halted)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (input_trace mode origin l t g node rule ctx old state image halted)))

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
    (finish mode origin l t g node rule state).principal.memory=(Listing8LoopReset.finish mode origin l t g node rule state).principal.memory ∧ (finish mode origin l t g node rule state).principal.stack=(Listing8LoopReset.finish mode origin l t g node rule state).principal.stack ∧
    (finish mode origin l t g node rule state).principal.carry=(Listing8LoopReset.finish mode origin l t g node rule state).principal.carry ∧ (finish mode origin l t g node rule state).sourceIndex=(Listing8LoopReset.finish mode origin l t g node rule state).sourceIndex ∧
    (finish mode origin l t g node rule state).destinationIndex=(Listing8LoopReset.finish mode origin l t g node rule state).destinationIndex ∧ (finish mode origin l t g node rule state).backwards=(Listing8LoopReset.finish mode origin l t g node rule state).backwards := by
  have actual:=Listing8NodeTrace.result mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
    (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)) _
    (input_entry mode origin l t g node rule ctx old state image halted) (Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted).1
  have ending : Listing8NodeTable.endPC mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))=Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
    rw [Listing8NodeTable.endPC,Listing8GraphNodeImage.length]
    rfl
  rw [ending] at actual
  exact actual

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 148 else 194)+11*g.transitions+9*g.nodes := by
  have length:=Listing8NodeTrace.instruction_count mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
  rw [Listing8GraphNodeImage.length] at length
  rw [program,List.length_append,List.length_map,List.length_map,Listing8LoopReset.instruction_count,length]
  rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.pc.toNat=Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  rw [(result mode origin l t g node rule ctx old state image halted).1,Arithmetic.encode_nat_toNat mode _ ctx.native.capacity]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.stack=state.principal.stack ∧ (finish mode origin l t g node rule state).principal.carry=false ∧
    (finish mode origin l t g node rule state).sourceIndex=state.sourceIndex ∧ (finish mode origin l t g node rule state).destinationIndex=state.destinationIndex ∧ (finish mode origin l t g node rule state).backwards=false := by
  have actual:=result mode origin l t g node rule ctx old state image halted
  have prior:=Listing8LoopReset.registers mode origin l t g node rule ctx old state image halted
  exact ⟨actual.2.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,
    actual.2.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.2⟩

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (finish mode origin l t g node rule state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (finish mode origin l t g node rule state).principal.memory := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted

theorem all_symbols (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    List.ofFn (fun index : Fin g.nodes => DwordCode.get (finish mode origin l t g node rule state).principal.memory (nodePC mode origin g index+6))=
      List.ofFn (fun index : Fin g.nodes => ((Listing8GraphStep.updated g node rule).tape index).symbol) := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopResetOutput.all_symbols mode origin l t g node rule ctx old state image halted

theorem logical_head_output (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    DwordCode.get (finish mode origin l t g node rule state).principal.memory (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6)=
      ((Listing8GraphStep.updated g node rule).tape (Listing8GraphStep.nextNode g node rule)).symbol := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopResetOutput.logical_head_output mode origin l t g node rule ctx old state image halted

theorem reset_cursors (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact ⟨Listing8LoopReset.input_cursor mode origin l t g node rule ctx old state image halted,Listing8LoopReset.transition_cursor mode origin l t g node rule ctx old state image halted⟩

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    ByteMemory.bytesAt (finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.callPC mode origin) 5=Native.encode mode (Listing8JumpLayout.call mode origin false) := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopResetOutput.call_packet mode origin l t g node rule ctx old state image halted

end SmcTuring.Appendix.Listing8LoopTerminal
