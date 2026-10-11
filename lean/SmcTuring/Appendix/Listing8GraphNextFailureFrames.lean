module
public import SmcTuring.Appendix.Listing8GraphNextFailure

public section
namespace SmcTuring.Appendix.Listing8GraphNextFailureFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem before_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤(Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  apply Listing8FailureReuseEffects.prefix_window mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
  have later:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at later <;> omega

theorem after_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have before:=Listing8GraphNextDirectionBounds.call_before_table mode origin l t g node rule ctx
  apply Listing8FailureReuseEffects.window mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
  all_goals left
  all_goals cases mode
  all_goals simp [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan,
    Listing8FailureLayout.mask,Listing8FailureLayout.xorPC,Listing8FailureLayout.andPC] at before ⊢ <;> omega

theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  have before:=(Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body).cursorBefore
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (before_window mode origin l t g node rule target ctx selected memory seed _ _ before)
  rw [show MixedMemory.getWord mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=_ from kept]
  exact Listing8GraphNextStateValues.logical_transition mode origin l t g node rule target ctx selected memory seed

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  have first:=Listing8StateFields.first_cursor_before mode l t ctx.body.state
  have second:=(Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body).cursorBefore
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤(Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start at second
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (before_window mode origin l t g node rule target ctx selected memory seed l.input.cursor mode.wordBytes (by omega))
  rw [show MixedMemory.getWord mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=_ from kept]
  exact Listing8GraphNextStateFrames.head mode origin l t g node rule target ctx selected memory seed

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions) (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,after_table mode origin l t g node rule target ctx selected memory seed _ _ inputAfter]
    exact (Listing8GraphNextStateFrames.source_graph mode origin l t g node rule target ctx selected memory seed).1
  · rw [Listing8TransitionTable.Initial,after_table mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_refl _)]
    exact (Listing8GraphNextStateFrames.source_graph mode origin l t g node rule target ctx selected memory seed).2

end SmcTuring.Appendix.Listing8GraphNextFailureFrames
