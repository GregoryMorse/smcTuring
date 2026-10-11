module
public import SmcTuring.Appendix.Listing8LoopControlCases
public import SmcTuring.Appendix.Listing8GraphNextTable

public section
namespace SmcTuring.Appendix.Listing8LoopTable
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8TableTrace.finish mode (Listing8FullTableImage.start mode origin) (table mode origin g) (Listing8LoopControl.finish mode origin l t g node rule state)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8LoopControl.program mode origin l t g node rule state++((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map StringControl.Form.previous).map StringStack.Form.previous

theorem table_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (Listing8LoopControl.finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [Listing8LoopControlCases.halt_effect mode origin l t g node rule ctx old state image halted]

theorem table_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringDword.Trace mode (Listing8LoopControl.finish mode origin l t g node rule state) (Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)) (finish mode origin l t g node rule state) :=
  Listing8TableTrace.trace mode _ _ (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native) _
    (table_entry mode origin l t g node rule ctx old state image halted) (Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state image).2

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (program mode origin l t g node rule state) (finish mode origin l t g node rule state) :=
  StringStack.trace_append mode (Listing8LoopControl.trace mode origin l t g node rule ctx old state image)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (table_trace mode origin l t g node rule ctx old state image halted)))

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)) ∧
    (finish mode origin l t g node rule state).principal.memory=(Listing8LoopControl.finish mode origin l t g node rule state).principal.memory ∧
    (finish mode origin l t g node rule state).principal.stack=(Listing8LoopControl.finish mode origin l t g node rule state).principal.stack ∧
    (finish mode origin l t g node rule state).principal.carry=(Listing8LoopControl.finish mode origin l t g node rule state).principal.carry ∧
    (finish mode origin l t g node rule state).sourceIndex=(Listing8LoopControl.finish mode origin l t g node rule state).sourceIndex ∧ (finish mode origin l t g node rule state).destinationIndex=(Listing8LoopControl.finish mode origin l t g node rule state).destinationIndex ∧
    (finish mode origin l t g node rule state).backwards=(Listing8LoopControl.finish mode origin l t g node rule state).backwards :=
  Listing8TableTrace.result mode _ _ (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native) _
    (table_entry mode origin l t g node rule ctx old state image halted) (Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state image).2

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 139 else 182)+11*g.transitions := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8LoopControl.instruction_count,
    Listing8TableTrace.instruction_count,table_length]

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start :=
  (result mode origin l t g node rule ctx old state image halted).1

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule state).principal.stack=state.principal.stack ∧ (finish mode origin l t g node rule state).principal.carry=false ∧
    (finish mode origin l t g node rule state).sourceIndex=state.sourceIndex ∧ (finish mode origin l t g node rule state).destinationIndex=state.destinationIndex ∧ (finish mode origin l t g node rule state).backwards=false := by
  have actual:=result mode origin l t g node rule ctx old state image halted
  have prior:=Listing8LoopControl.registers mode origin l t g node rule ctx old state image
  exact ⟨actual.2.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.2.2.2.1,
    actual.2.2.2.2.1.trans prior.2.1,actual.2.2.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.1⟩

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (finish mode origin l t g node rule state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (finish mode origin l t g node rule state).principal.memory := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state image

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopControlFrames.logical_head mode origin l t g node rule ctx old state image

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (finish mode origin l t g node rule state).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [(result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8LoopControlCases.halt_cursor mode origin l t g node rule ctx old state image halted

end SmcTuring.Appendix.Listing8LoopTable
