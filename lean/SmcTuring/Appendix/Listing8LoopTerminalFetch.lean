module
public import SmcTuring.Appendix.Listing8ResetPC
public import SmcTuring.Appendix.Listing8LoopControlFetch
public import SmcTuring.Appendix.Listing8LoopTerminalReads

public section
namespace SmcTuring.Appendix.Listing8LoopTerminalFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Current:=Listing8LoopHaltImage.Current
attribute [local irreducible] StringFetchWindows.Run StringWrites.OwnedRun StringReadRuns.Run

theorem table_placement (mode : Mode) (origin : Nat) (g : Graph) :
    origin≤Listing8FullTableImage.start mode origin ∧
    Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  constructor
  · rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  · have upper:=Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions)
      (Listing8LoopTailGeometry.input_before_end mode origin g)
    simpa only [Listing8TransitionTable.endPC,table_length,Listing8GraphLayout.reset,Listing8GraphLayout.transition] using upper

theorem reset_placement (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤(Listing8GraphHaltTerminalWrites.resetRegion mode origin l g).start ∧
    Listing8ResetLayout.endPC mode (Listing8GraphHaltTerminalWrites.resetRegion mode origin l g)≤
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  unfold Listing8GraphHaltTerminalWrites.resetRegion
  rw [Listing8GraphReset.actual_region mode origin l t _ _ ctx.boot ctx.body,table_length]
  constructor
  · exact Nat.le_trans (table_placement mode origin g).1 (Listing8GraphLayout.transition_lower mode origin g.transitions)
  · rw [Listing8GraphReset.endpoint]
    exact Listing8LoopTailGeometry.input_before_end mode origin g

theorem node_placement (mode : Mode) (origin : Nat) (g : Graph) :
    origin≤Listing8GraphLayout.input mode origin g.transitions ∧
    Listing8NodeTable.endPC mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g)=Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  exact ⟨Listing9EarlyImage.input_after_origin mode origin g.transitions,
    by simp only [Listing8NodeTable.endPC,Listing8GraphNodeImage.length,Listing8GraphLayout.endPC,Listing8GraphLayout.node]⟩

theorem table_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltTerminalWrites.tableForms mode origin g) (Listing8LoopControl.finish mode origin l t g node rule state) :=
  StringFetchWindows.of_pc_run mode _
    (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted))
    (Listing8DeclarationPC.transitions_windows mode _ _ _ _
      (Listing8LoopTable.table_entry mode origin l t g node rule ctx old state image.control halted)
      (table_placement mode origin g).1 (table_placement mode origin g).2 ctx.native.capacity)

theorem reset_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltTerminalWrites.resetForms mode origin l g) (Listing8LoopTable.finish mode origin l t g node rule state) :=
  StringFetchWindows.of_pc_run mode _
    (StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted))
    (Listing8ResetPC.windows mode _ _ _
      (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
      (reset_placement mode origin l t g node rule ctx).1 (reset_placement mode origin l t g node rule ctx).2 ctx.native.capacity)

theorem nodes_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltTerminalWrites.nodeForms mode origin g node rule) (Listing8LoopReset.finish mode origin l t g node rule state) := by
  have placed:=node_placement mode origin (Listing8GraphStep.updated g node rule)
  exact StringFetchWindows.of_pc_run mode _
    (StringDwordWritesBridge.trace mode (Listing8LoopTerminal.input_trace mode origin l t g node rule ctx old state image halted))
    (Listing8DeclarationPC.nodes_windows mode _ _ _ _
      (Listing8LoopTerminal.input_entry mode origin l t g node rule ctx old state image halted) placed.1 (Nat.le_of_eq placed.2) ctx.native.capacity)

/-- CALL effects, original declarations, reset and updated node declarations
are composed at their positively derived actual boundary states. -/
theorem tail_contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8LoopTerminalWrites.program mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  unfold Listing8LoopTerminalWrites.program
  apply StringFetchWindows.append_trace mode _ _ _ _ (Listing8LoopReset.finish mode origin l t g node rule state)
    (StringStack.trace_append mode
      (StringStack.trace_append mode (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
        (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)))
      (StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)))
  · apply StringFetchWindows.append_trace mode _ _ _ _ (Listing8LoopTable.finish mode origin l t g node rule state)
      (StringStack.trace_append mode (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
        (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)))
    · exact StringFetchWindows.append_trace mode _ _ _ _ (Listing8LoopControl.finish mode origin l t g node rule state)
        (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
        (Listing8LoopReturnFetch.contained mode origin l t g node rule ctx old state image.control)
        (table_contained mode origin l t g node rule ctx old state image halted)
    · exact reset_contained mode origin l t g node rule ctx old state image halted
  · exact nodes_contained mode origin l t g node rule ctx old state image halted

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8LoopTerminal.program mode origin l t g node rule state) state := by
  rw [Listing8LoopTerminalBodyWrites.program_split]
  exact StringFetchWindows.append_trace mode _ _ _ state (Listing8LoopControl.failureEnd mode origin l t g node rule state)
    (Listing8BodyFetch.complete mode origin l t g node rule ctx old state image.control.body).1
    (Listing8BodyFetch.contained mode origin l t g node rule ctx old state image.control.body)
    (tail_contained mode origin l t g node rule ctx old state image halted)

theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (Listing8LoopTerminal.program mode origin l t g node rule state) (Listing8LoopTerminal.finish mode origin l t g node rule state) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (Listing8LoopTerminal.program mode origin l t g node rule state) state ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (Listing8LoopTerminal.program mode origin l t g node rule state) state ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (Listing8LoopTerminal.program mode origin l t g node rule state) state :=
  ⟨Listing8LoopTerminal.trace mode origin l t g node rule ctx old state image halted,
    contained mode origin l t g node rule ctx old state image halted,
    Listing8LoopTerminalBodyWrites.owned mode origin l t g node rule ctx old state image halted,
    Listing8LoopTerminalReads.contained mode origin l t g node rule ctx old state image halted⟩

end SmcTuring.Appendix.Listing8LoopTerminalFetch
