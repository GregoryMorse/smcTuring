module
public import SmcTuring.Appendix.Listing8GraphReturnFetch
public import SmcTuring.Appendix.Listing8LoopTerminalFetch
public import SmcTuring.Appendix.Listing8GraphHaltTerminalReads

public section
namespace SmcTuring.Appendix.Listing8GraphHaltTerminalFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphHaltTerminalWrites
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringFetchWindows.Run StringWrites.OwnedRun StringReadRuns.Run

theorem table_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (tableForms mode origin g) (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed) := by
  apply StringFetchWindows.of_pc_run mode _ (table_trace mode origin l t g node rule ctx memory seed)
  apply Listing8DeclarationPC.transitions_windows mode _ _ _ _ ?_
    (Listing8LoopTerminalFetch.table_placement mode origin g).1 (Listing8LoopTerminalFetch.table_placement mode origin g).2 ctx.native.capacity
  rw [Listing8GraphHaltReturnWrites.finish,Listing8FailReturn.effect mode origin l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body]
  rfl

theorem reset_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (resetForms mode origin l g) (afterTable mode origin l t g node rule memory seed) :=
  StringFetchWindows.of_pc_run mode _ (reset_trace mode origin l t g node rule ctx memory seed)
    (Listing8ResetPC.windows mode _ _ _ (reset_entry mode origin l t g node rule ctx memory seed)
      (Listing8LoopTerminalFetch.reset_placement mode origin l t g node rule ctx).1
      (Listing8LoopTerminalFetch.reset_placement mode origin l t g node rule ctx).2 ctx.native.capacity)

theorem nodes_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (nodeForms mode origin g node rule) (beforeNodes mode origin l t g node rule memory seed) := by
  have placed:=Listing8LoopTerminalFetch.node_placement mode origin (Listing8GraphStep.updated g node rule)
  exact StringFetchWindows.of_pc_run mode _ (nodes_trace mode origin l t g node rule ctx memory seed halted)
    (Listing8DeclarationPC.nodes_windows mode _ _ _ _ (Listing8LoopFirstHalt.input_entry mode origin l t g node rule ctx memory seed halted)
      placed.1 (Nat.le_of_eq placed.2) ctx.native.capacity)

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  unfold program
  apply StringFetchWindows.append_trace mode _ _ _ _ (beforeNodes mode origin l t g node rule memory seed)
    (StringStack.trace_append mode
      (StringStack.trace_append mode (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
        (table_trace mode origin l t g node rule ctx memory seed)) (reset_trace mode origin l t g node rule ctx memory seed))
  · apply StringFetchWindows.append_trace mode _ _ _ _ (afterTable mode origin l t g node rule memory seed)
      (StringStack.trace_append mode (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
        (table_trace mode origin l t g node rule ctx memory seed))
    · exact StringFetchWindows.append_trace mode _ _ _ _ (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed)
        (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
        (Listing8GraphReturnFetch.halted mode origin l t g node rule ctx memory seed halted)
        (table_contained mode origin l t g node rule ctx memory seed)
    · exact reset_contained mode origin l t g node rule ctx memory seed
  · exact nodes_contained mode origin l t g node rule ctx memory seed halted

theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  ⟨(execute mode origin l t g node rule ctx memory seed halted).1,
    contained mode origin l t g node rule ctx memory seed halted,
    (execute mode origin l t g node rule ctx memory seed halted).2,
    Listing8GraphHaltTerminalReads.contained mode origin l t g node rule ctx memory seed halted⟩

end SmcTuring.Appendix.Listing8GraphHaltTerminalFetch
