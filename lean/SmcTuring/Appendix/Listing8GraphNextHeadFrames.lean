module
public import SmcTuring.Appendix.Listing8GraphNextHeadValues

public section
namespace SmcTuring.Appendix.Listing8GraphNextHeadFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem direction_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (Listing8StateGeometry.region mode l).start≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count :=
  Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_helpers mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_packets mode l writer member) after))

theorem head_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (Listing8StateGeometry.region mode l).start≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  rw [Listing8GraphNextHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_xors mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t ctx.body.state writer (List.mem_append_left _ member)) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t ctx.body.state writer (List.mem_append_right _ member)) after))]
  exact direction_window mode origin l t g node rule target ctx selected memory seed observed count after

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory := by
  have before:=Listing8GraphNextDirectionBounds.direction_before_table mode origin l t g node rule ctx
  change (Listing8StateGeometry.region mode l).start≤Listing8FullTableImage.start mode origin at before
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,head_window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_trans before inputAfter)]
    exact (Listing8GraphNextInputNodes.source_graph mode origin l t g node rule target ctx selected memory seed).1
  · rw [Listing8TransitionTable.Initial,head_window mode origin l t g node rule target ctx selected memory seed _ _ before]
    exact (Listing8GraphNextInputNodes.source_graph mode origin l t g node rule target ctx selected memory seed).2

end SmcTuring.Appendix.Listing8GraphNextHeadFrames
