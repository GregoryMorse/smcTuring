module
public import SmcTuring.Appendix.Listing8LoopGraphState
public import SmcTuring.Appendix.Listing8LoopFailureFrames

public section
namespace SmcTuring.Appendix.Listing8LoopGraphFailure
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (machine : StringExecution.State mode) : Prop where
  state : Listing8LoopGraphState.Current mode origin l t g node rule old machine
  failure : Listing8FailureReuseImage.Current mode
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) machine.principal.memory

theorem input_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (current : Current mode origin l t g node rule old state) :
    Listing8LoopFailure.Current mode l t (values mode origin g node rule) old (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) state.principal.memory :=
  ⟨Listing8LoopGraphState.input_current mode origin l t g node rule old state nodeLocated ruleLocated current.state,current.failure⟩

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LoopFailure.Bounds mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) :=
  ⟨Listing8LoopGraphState.bounds mode origin l t g node rule ctx,ctx.body⟩

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopFailure.Bounds mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state) :=
  Listing8LoopFailure.stack_trace mode l t _ _ _ old b state current.state.head.graph.entry current.state.head.graph.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopFailure.Bounds mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (current : Current mode origin l t g node rule old state)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8LoopFailure.failed mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state=true ↔
      Listing8GraphRun.Halted g node rule := by
  unfold Listing8LoopFailure.failed Listing8FailureValues.failed
  change decide (MixedMemory.getWord mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory
    (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt))=true ↔ _
  rw [Listing8LoopGraphState.logical_transition mode origin l t g node rule old state nodeLocated ruleLocated b.state current.state]
  simp only [decide_eq_true_eq]
  exact (Listing8GraphLabels.state_halt_iff mode origin g _ native).trans (Listing8GraphStep.halted_iff g node rule)

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopFailure.Bounds mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (current : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule g node rule)) := by
  have image:=input_current mode origin l t g node rule old state nodeLocated ruleLocated current
  have second:=(Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure).cursorBefore
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (Listing8LoopFailureFrames.before_window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.state.head.graph.entry current.state.head.graph.forward image (Listing8StateGeometry.region mode l).cursor mode.wordBytes (by
      change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start at second
      exact second))
  change MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8StateGeometry.region mode l).cursor=
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory (Listing8StateGeometry.region mode l).cursor at kept
  rw [kept]
  exact Listing8LoopGraphState.logical_transition mode origin l t g node rule old state nodeLocated ruleLocated b.state current.state

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8LoopFailure.Bounds mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (current : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  have image:=input_current mode origin l t g node rule old state nodeLocated ruleLocated current
  have second:=(Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure).cursorBefore
  have first:=Listing8StateFields.first_cursor_before mode l t b.state.state
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (Listing8LoopFailureFrames.before_window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.state.head.graph.entry current.state.head.graph.forward image l.input.cursor mode.wordBytes (by
      change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start at second
      omega))
  change MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory l.input.cursor=
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory l.input.cursor at kept
  rw [kept]
  exact Listing8LoopGraphState.logical_head mode origin l t g node rule old state nodeLocated ruleLocated b.state current.state

theorem after_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory observed count := by
  have image:=input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have b:=bounds mode origin l t g node rule ctx
  have before:=Listing8GraphNextDirectionBounds.call_before_table mode origin l t g node rule ctx
  apply Listing8LoopFailure.window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.state.head.graph.entry current.state.head.graph.forward image observed count
  all_goals left
  all_goals cases mode
  all_goals simp [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan,
    Listing8FailureLayout.mask,Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC] at before ⊢ <;> omega

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory := by
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions) (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,after_table mode origin l t g node rule ctx old state current _ _ inputAfter]
    exact (Listing8LoopGraphState.source_graph mode origin l t g node rule ctx old state current.state).1
  · rw [Listing8TransitionTable.Initial,after_table mode origin l t g node rule ctx old state current _ _ (Nat.le_refl _)]
    exact (Listing8LoopGraphState.source_graph mode origin l t g node rule ctx old state current.state).2

/-- Combined actual graph-labelled body through failure selection. -/
theorem correct (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state) ∧
    (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) ∧
    (Listing8LoopFailure.failed mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state=true ↔ Listing8GraphRun.Halted g node rule) ∧
    MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) ∧
    MixedMemory.getWord mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule g node rule)) ∧
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory := by
  have b:=bounds mode origin l t g node rule ctx
  have image:=input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have graph:=source_graph mode origin l t g node rule ctx old state current
  exact ⟨trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current,
    Listing8LoopFailure.endpoint mode l t _ _ _ old b state current.state.head.graph.entry current.state.head.graph.forward image,
    failed_iff mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current ctx.native,
    logical_head mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current,
    logical_transition mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated b current,graph.1,graph.2⟩

end SmcTuring.Appendix.Listing8LoopGraphFailure
