module
public import SmcTuring.Appendix.Listing8GraphNextStateValues

public section
namespace SmcTuring.Appendix.Listing8GraphNextStateFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed count :=
  Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_helpers_before mode l _ _ writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_packets_before mode l t _ _ ctx.resources ctx.body writer member) after))

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory := by
  have before:=Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_trans before inputAfter)]
    exact (Listing8GraphNextHeadFrames.source_graph mode origin l t g node rule target ctx selected memory seed).1
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ before]
    exact (Listing8GraphNextHeadFrames.source_graph mode origin l t g node rule target ctx selected memory seed).2

theorem head_frame (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      MixedMemory.getWord mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor := by
  have before := (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state).cursorBefore
  have first := Listing8StateFields.first_cursor_before mode l t ctx.body.state
  have helpers : ∀ writer ∈ Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l),
      writer.destination+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.destination := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  have packets : ∀ writer ∈ Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l),
      writer.target+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.target := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  exact congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
      (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed) l.input.cursor mode.wordBytes helpers packets)

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [head_frame mode origin l t g node rule target ctx selected memory seed]
  exact Listing8GraphNextHeadValues.logical_head mode origin l t g node rule target ctx selected memory seed

end SmcTuring.Appendix.Listing8GraphNextStateFrames
