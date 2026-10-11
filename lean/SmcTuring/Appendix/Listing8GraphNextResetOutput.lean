module
public import SmcTuring.Appendix.Listing8GraphNextReset

public section
namespace SmcTuring.Appendix.Listing8GraphNextResetOutput
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory := by
  have tableAfter : Listing8JumpLayout.callPC mode origin+5≤Listing8FullTableImage.start mode origin := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC];omega
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions) (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,Listing8GraphNextReset.window mode origin l t g node rule target ctx selected memory seed halted _ _ (Nat.le_trans tableAfter inputAfter)]
    exact (Listing8GraphNextTable.source_graph mode origin l t g node rule target ctx selected memory seed halted).1
  · rw [Listing8TransitionTable.Initial,Listing8GraphNextReset.window mode origin l t g node rule target ctx selected memory seed halted _ _ tableAfter]
    exact (Listing8GraphNextTable.source_graph mode origin l t g node rule target ctx selected memory seed halted).2

theorem tape_symbol (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) (index : Fin g.nodes) :
    DwordCode.get (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (nodePC mode origin g index+6)=
      ((Listing8GraphNextInputNodes.graph g node rule target).tape index).symbol := by
  let graph:=Listing8GraphNextInputNodes.graph g node rule target
  have initial:=(source_graph mode origin l t g node rule target ctx selected memory seed halted).1
  have packet:=Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin graph) index.val (Listing8GraphNodeImage.value mode origin graph index)
    (Listing8GraphNodeImage.lookup mode origin graph index) _ initial
  exact (node_values mode (nodePC mode origin graph index) (graph.tape index).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back))
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward)) _ (by rw [node_length];exact packet)).1

theorem neighbors (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) (index : Fin g.nodes) :
    let graph:=Listing8GraphNextInputNodes.graph g node rule target
    MixedMemory.getWord mode (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (pointerField mode (backEntry mode (nodePC mode origin graph index)))=
      Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back) ∧
    MixedMemory.getWord mode (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (pointerField mode (forwardEntry mode (nodePC mode origin graph index)))=
      Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward) := by
  let graph:=Listing8GraphNextInputNodes.graph g node rule target
  have initial:=(source_graph mode origin l t g node rule target ctx selected memory seed halted).1
  have packet:=Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin graph) index.val (Listing8GraphNodeImage.value mode origin graph index)
    (Listing8GraphNodeImage.lookup mode origin graph index) _ initial
  exact (node_values mode (nodePC mode origin graph index) (graph.tape index).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back))
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward)) _ (by rw [node_length];exact packet)).2

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    ByteMemory.bytesAt (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (Listing8JumpLayout.call mode origin false) := by
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  rw [Listing8GraphNextReset.effect mode origin l t g node rule target ctx selected memory seed halted,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl cursors.2),StackWindows.word_window _ _ _ _ _ _ (Or.inl cursors.1)]
  apply Listing8CallSelection.operand_current
  rw [Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  have packet:=Listing8GraphNextJump.call_packet mode origin l t g node rule target ctx selected memory seed
  rw [Listing8GraphNextFailReturn.failure mode origin l t g node rule target ctx selected memory seed halted] at packet
  exact packet

theorem call_fetch (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringStack.fetch mode (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory (Listing8JumpLayout.callPC mode origin)=
      some (StringStack.native mode (Listing8JumpLayout.call mode origin false)) :=
  StringStack.native_encoding mode _ _ _ (by
    simpa only [Listing8JumpLayout.call,Bool.false_eq_true,ite_false,Native.encode,List.length_cons,List.length_nil,List.length_append,LittleEndian.word_encode_length] using
      call_packet mode origin l t g node rule target ctx selected memory seed halted)

theorem marker_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    ByteMemory.bytesAt (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8ResetLayout.markerPC mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))) 10=
        TerminalMarker.bytes mode (Listing8ResetLayout.markerPC mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))) :=
  Listing8ResetPackets.marker_current mode _ _ (Listing8GraphNextReset.reset_current mode origin l t g node rule target ctx selected memory seed halted)

theorem bootstrap_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    ByteMemory.bytesAt (Listing8GraphNextReset.finish mode origin l t g node rule target memory seed).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  have first:=Listing8EarlyGeometry.first_cursor mode l t ctx.body.state.head
  change l.start≤l.input.cursor at first
  have second:=Listing8EarlyGeometry.second_cursor mode l
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  have ending : origin+Listing4EntryLayout.size mode=l.start := ctx.boot.packed.symm
  rw [Listing8GraphNextReset.effect mode origin l t g node rule target ctx selected memory seed halted,
    StackWindows.word_window _ _ _ _ _ _ (Or.inr (by omega)),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),
    Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GraphNextStackImage.code_current mode origin l t g node rule target ctx selected memory seed

end SmcTuring.Appendix.Listing8GraphNextResetOutput
