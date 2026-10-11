module
public import SmcTuring.Appendix.Listing8LoopReset
public import SmcTuring.Appendix.Listing8GraphNextResetOutput

public section
namespace SmcTuring.Appendix.Listing8LoopResetOutput
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory := by
  have tableAfter : Listing8JumpLayout.callPC mode origin+5≤Listing8FullTableImage.start mode origin := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC];omega
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions) (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,Listing8LoopReset.window mode origin l t g node rule ctx old state image halted _ _ (Nat.le_trans tableAfter inputAfter)]
    exact (Listing8LoopTable.source_graph mode origin l t g node rule ctx old state image.control halted).1
  · rw [Listing8TransitionTable.Initial,Listing8LoopReset.window mode origin l t g node rule ctx old state image halted _ _ tableAfter]
    exact (Listing8LoopTable.source_graph mode origin l t g node rule ctx old state image.control halted).2

theorem tape_symbol (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) (index : Fin g.nodes) :
    DwordCode.get (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (nodePC mode origin g index+6)=((Listing8GraphStep.updated g node rule).tape index).symbol := by
  let graph:=Listing8GraphStep.updated g node rule
  have initial:=(source_graph mode origin l t g node rule ctx old state image halted).1
  have packet:=Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin graph) index.val (Listing8GraphNodeImage.value mode origin graph index)
    (Listing8GraphNodeImage.lookup mode origin graph index) _ initial
  exact (node_values mode (nodePC mode origin graph index) (graph.tape index).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back))
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward)) _ (by rw [node_length];exact packet)).1

theorem neighbors (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) (index : Fin g.nodes) :
    let graph:=Listing8GraphStep.updated g node rule
    MixedMemory.getWord mode (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (pointerField mode (backEntry mode (nodePC mode origin graph index)))=Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back) ∧
    MixedMemory.getWord mode (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (pointerField mode (forwardEntry mode (nodePC mode origin graph index)))=Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward) := by
  let graph:=Listing8GraphStep.updated g node rule
  have initial:=(source_graph mode origin l t g node rule ctx old state image halted).1
  have packet:=Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin graph) index.val (Listing8GraphNodeImage.value mode origin graph index)
    (Listing8GraphNodeImage.lookup mode origin graph index) _ initial
  exact (node_values mode (nodePC mode origin graph index) (graph.tape index).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).back))
    (Arithmetic.encodeNat mode (nodePC mode origin graph (graph.tape index).forward)) _ (by rw [node_length];exact packet)).2

/-- Every final tape symbol, with the logical terminal head observed separately
from the cursors deliberately reset by the printed cleanup. -/
theorem all_symbols (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    List.ofFn (fun index : Fin g.nodes => DwordCode.get (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (nodePC mode origin g index+6))=
      List.ofFn (fun index : Fin g.nodes => ((Listing8GraphStep.updated g node rule).tape index).symbol) := by
  apply congrArg List.ofFn
  funext index
  exact tape_symbol mode origin l t g node rule ctx old state image halted index

theorem logical_head_output (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    DwordCode.get (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6)=
      ((Listing8GraphStep.updated g node rule).tape (Listing8GraphStep.nextNode g node rule)).symbol :=
  tape_symbol mode origin l t g node rule ctx old state image halted (Listing8GraphStep.nextNode g node rule)

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    ByteMemory.bytesAt (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.callPC mode origin) 5=Native.encode mode (Listing8JumpLayout.call mode origin false) := by
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  rw [Listing8LoopReset.effect mode origin l t g node rule ctx old state image halted,StackWindows.word_window _ _ _ _ _ _ (Or.inl cursors.2),StackWindows.word_window _ _ _ _ _ _ (Or.inl cursors.1)]
  apply Listing8CallSelection.operand_current
  rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
  have packet:=Listing8LoopControlFrames.call_packet mode origin l t g node rule ctx old state image.control
  rw [Listing8LoopControlCases.failure mode origin l t g node rule ctx old state image.control halted] at packet
  exact packet

theorem call_fetch (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.fetch mode (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.callPC mode origin)=some (StringStack.native mode (Listing8JumpLayout.call mode origin false)) :=
  StringStack.native_encoding mode _ _ _ (by
    simpa only [Listing8JumpLayout.call,Bool.false_eq_true,ite_false,Native.encode,List.length_cons,List.length_nil,List.length_append,LittleEndian.word_encode_length] using call_packet mode origin l t g node rule ctx old state image halted)

theorem marker_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    ByteMemory.bytesAt (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory (Listing8ResetLayout.markerPC mode (Listing8LoopHaltImage.region mode origin l g)) 10=
      TerminalMarker.bytes mode (Listing8ResetLayout.markerPC mode (Listing8LoopHaltImage.region mode origin l g)) :=
  Listing8ResetPackets.marker_current mode _ _ (Listing8LoopReset.reset_current mode origin l t g node rule ctx old state image halted)

theorem bootstrap_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    ByteMemory.bytesAt (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  have first:=Listing8EarlyGeometry.first_cursor mode l t ctx.body.state.head
  change l.start≤l.input.cursor at first
  have second:=Listing8EarlyGeometry.second_cursor mode l
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  have ending : origin+Listing4EntryLayout.size mode=l.start := ctx.boot.packed.symm
  rw [Listing8LoopReset.effect mode origin l t g node rule ctx old state image halted,StackWindows.word_window _ _ _ _ _ _ (Or.inr (by omega)),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
  exact Listing8LoopControlFrames.entry_packet mode origin l t g node rule ctx old state image.control

end SmcTuring.Appendix.Listing8LoopResetOutput
