module
public import SmcTuring.Appendix.Listing8LoopGraphHead
public import SmcTuring.Appendix.Listing8LoopStateFrames

public section
namespace SmcTuring.Appendix.Listing8LoopGraphState
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode) : Prop where
  head : Listing8LoopGraphHead.Current mode origin l t g node rule old state
  fragments : Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l) state.principal.memory

theorem input_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (current : Current mode origin l t g node rule old state) :
    Listing8LoopState.Current mode l t (values mode origin g node rule) old state.principal.memory :=
  ⟨Listing8LoopGraphHead.input_current mode origin l t g node rule old state nodeLocated ruleLocated current.head,current.fragments⟩

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LoopState.Bounds mode l t (values mode origin g node rule) :=
  ⟨Listing8LoopGraphHead.bounds mode origin l t g node rule ctx,ctx.body.state⟩

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopState.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      (((Listing8LoopState.program mode l t (values mode origin g node rule) state).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) :=
  Listing8LoopState.stack_trace mode l t _ old b state current.head.graph.entry current.head.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopState.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule g node rule)) := by
  rw [Listing8LoopStateValues.transition mode l t _ old b state current.head.graph.entry current.head.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)]
  exact Listing8GraphStep.rule_pointer mode origin g node rule

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopState.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  rw [Listing8LoopStateFrames.head_frame mode l t _ old b state current.head.graph.entry current.head.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)]
  exact Listing8LoopGraphHead.logical_head mode origin l t g node rule old state nodeLocated ruleLocated b.head current.head

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state)
    (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory observed count :=
  Listing8LoopStateFrames.window mode l t _ old (bounds mode origin l t g node rule ctx) state current.head.graph.entry current.head.graph.forward
    (input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_helpers_before mode l _ _ writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_packets_before mode l t _ _ ctx.resources ctx.body writer member) after))

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have before:=Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule ctx old state current _ _ (Nat.le_trans before inputAfter)]
    exact (Listing8LoopGraphHead.source_graph mode origin l t g node rule ctx old state current.head).1
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule ctx old state current _ _ before]
    exact (Listing8LoopGraphHead.source_graph mode origin l t g node rule ctx old state current.head).2

end SmcTuring.Appendix.Listing8LoopGraphState
