module
public import SmcTuring.Appendix.Listing8LoopReturnWrites
public import SmcTuring.Appendix.Listing8GraphHaltTerminalWrites
public import SmcTuring.Appendix.Listing8LoopTerminal

public section
namespace SmcTuring.Appendix.Listing8LoopTerminalWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)++
    Listing8GraphHaltTerminalWrites.tableForms mode origin g++Listing8GraphHaltTerminalWrites.resetForms mode origin l g++
      Listing8GraphHaltTerminalWrites.nodeForms mode origin g node rule

theorem table_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphHaltTerminalWrites.tableForms mode origin g) (Listing8LoopControl.finish mode origin l t g node rule state) :=
  Listing8DeclarationWrites.transitions_owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing8FullTableImage.start mode origin) (table mode origin g) (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native)
    (Listing8GraphDeclarationWriteBounds.transitions mode origin g ctx.native) (Listing8LoopControl.finish mode origin l t g node rule state)
    (Listing8LoopTable.table_entry mode origin l t g node rule ctx old state image halted)
    (Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state image).2

theorem reset_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphHaltTerminalWrites.resetForms mode origin l g) (Listing8LoopTable.finish mode origin l t g node rule state) :=
  Listing8ResetWrites.owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (Listing8LoopHaltImage.region mode origin l g)
    (reset_bounds mode origin l t g node rule ctx).reset (Listing8GraphResetWriteBounds.placement mode origin l t g node rule ctx)
    (Listing8LoopTable.finish mode origin l t g node rule state) (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted)

theorem nodes_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphHaltTerminalWrites.nodeForms mode origin g node rule) (Listing8LoopReset.finish mode origin l t g node rule state) :=
  Listing8DeclarationWrites.nodes_owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
    (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native))
    (Listing8GraphDeclarationWriteBounds.nodes mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native))
    (Listing8LoopReset.finish mode origin l t g node rule state) (Listing8LoopTerminal.input_entry mode origin l t g node rule ctx old state image halted)
    (Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted).1

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state) (program mode origin l t g node rule state)
      (Listing8LoopTerminal.finish mode origin l t g node rule state) :=
  StringStack.trace_append mode (StringStack.trace_append mode (StringStack.trace_append mode
    (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
    (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)))
    (StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)))
    (StringDwordWritesBridge.trace mode (Listing8LoopTerminal.input_trace mode origin l t g node rule ctx old state image halted))

theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  unfold program
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ _ (Listing8LoopReset.finish mode origin l t g node rule state)
    (StringStack.trace_append mode (StringStack.trace_append mode (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
      (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)))
        (StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)))
  · apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      _ _ _ (Listing8LoopTable.finish mode origin l t g node rule state)
      (StringStack.trace_append mode (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
        (StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)))
    · exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
        _ _ _ (Listing8LoopControl.finish mode origin l t g node rule state)
        (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control)
        (Listing8LoopReturnWrites.owned mode origin l t g node rule ctx old state image.control)
        (table_owned mode origin l t g node rule ctx old state image.control halted)
    · exact reset_owned mode origin l t g node rule ctx old state image halted
  · exact nodes_owned mode origin l t g node rule ctx old state image halted

/-- The complete reached terminal suffix owns every store: actual CALL return,
all transition declarations, reset/DOHALT, input and node declarations. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopReset.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state) (program mode origin l t g node rule state)
      (Listing8LoopTerminal.finish mode origin l t g node rule state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  ⟨trace mode origin l t g node rule ctx old state image halted,owned mode origin l t g node rule ctx old state image halted⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 16 else 21)+11*g.transitions+9*g.nodes := by
  rw [program,List.length_append,List.length_append,List.length_append,Listing8JumpReturn.instruction_count,
    Listing8GraphHaltTerminalWrites.tableForms,Listing8GraphHaltTerminalWrites.resetForms,Listing8GraphHaltTerminalWrites.nodeForms,
    List.length_map,List.length_map,List.length_map,Listing8TableTrace.instruction_count,Listing8ResetLayout.instruction_count,
    Listing8NodeTrace.instruction_count,table_length,Listing8GraphNodeImage.length]
  rw [show (Listing8GraphStep.updated g node rule).nodes=g.nodes from rfl]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

end SmcTuring.Appendix.Listing8LoopTerminalWrites
