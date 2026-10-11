module
public import SmcTuring.Appendix.Listing8LoopHeadValues
public import SmcTuring.Appendix.Listing8MainGraphInput
public import SmcTuring.Appendix.Listing8GraphNextDirectionBounds

public section
namespace SmcTuring.Appendix.Listing8LoopGraphHead
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- The complete graph and immutable direction/head fragments are observations
of the same present main-entry state. -/
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode) : Prop where
  graph : Listing8MainGraphImage.Current mode origin l t g node rule old state
  fragments : Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) state.principal.memory

theorem input_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (current : Current mode origin l t g node rule old state) :
    Listing8LoopHead.Current mode l t (values mode origin g node rule) old state.principal.memory :=
  ⟨Listing8MainGraphImage.input_current mode origin l t g node rule old state nodeLocated ruleLocated current.graph,current.fragments⟩

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LoopHead.Bounds mode l t (values mode origin g node rule) :=
  ⟨Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx,ctx.body.state.head⟩

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopHead.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      (((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) :=
  Listing8LoopHead.stack_trace mode l t _ old b state current.graph.entry current.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopHead.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  rw [Listing8LoopHeadValues.head_selection mode l t _ old b state current.graph.entry current.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current) (g.rules rule).takeBack rfl,
    b.input.input.prefixBounds.fields.headLabel,nodeLocated]
  exact Listing8GraphStep.head_pointer mode origin g node rule

theorem direction_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state)
    (observed count : Nat) (after : (Listing8StateGeometry.region mode l).start≤observed) :
    ByteMemory.bytesAt (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory observed count :=
  Listing8LoopDirection.window mode l t _ old (bounds mode origin l t g node rule ctx) state current.graph.entry current.graph.forward
    (input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_helpers mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_packets mode l writer member) after))

theorem head_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state)
    (observed count : Nat) (after : (Listing8StateGeometry.region mode l).start≤observed) :
    ByteMemory.bytesAt (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory observed count := by
  rw [Listing8LoopHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8LoopDirection.endpoint mode l t _ old (bounds mode origin l t g node rule ctx) state current.graph.entry current.graph.forward
      (input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current)) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_xors mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t ctx.body.state writer (List.mem_append_left _ member)) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t ctx.body.state writer (List.mem_append_right _ member)) after))]
  exact direction_window mode origin l t g node rule ctx old state current observed count after

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have before:=Listing8GraphNextDirectionBounds.direction_before_table mode origin l t g node rule ctx
  change (Listing8StateGeometry.region mode l).start≤Listing8FullTableImage.start mode origin at before
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,head_window mode origin l t g node rule ctx old state current _ _ (Nat.le_trans before inputAfter)]
    exact (Listing8MainGraphInputNodes.source_graph mode origin l t g node rule ctx old state current.graph).1
  · rw [Listing8TransitionTable.Initial,head_window mode origin l t g node rule ctx old state current _ _ before]
    exact (Listing8MainGraphInputNodes.source_graph mode origin l t g node rule ctx old state current.graph).2

/-- Combined actual graph-labelled prefix/input/direction/head result. -/
theorem correct (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      (((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) ∧
    (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)) ∧
    MixedMemory.getWord mode (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) ∧
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have b:=bounds mode origin l t g node rule ctx
  have image:=input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have graph:=source_graph mode origin l t g node rule ctx old state current
  exact ⟨trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current,
    Listing8LoopHead.endpoint mode l t _ old b state current.graph.entry current.graph.forward image,
    logical_head mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current,
    graph.1,graph.2,Listing8LoopHead.current_after mode l t _ old b state current.graph.entry current.graph.forward image⟩

end SmcTuring.Appendix.Listing8LoopGraphHead
