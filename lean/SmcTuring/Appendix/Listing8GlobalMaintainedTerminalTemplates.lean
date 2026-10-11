module
public import SmcTuring.Appendix.Listing8GlobalControlProperties
public import SmcTuring.Appendix.Listing8GlobalMainControlTemplates
public import SmcTuring.Appendix.Listing8LoopTerminal

public section
namespace SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringTemplateStates.Run StringStoreRegions.Run
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem reset_property (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8GlobalControlTemplates.Property mode origin
      (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory := by
  have initial : Listing8GlobalControlTemplates.Property mode origin
      (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory := by
    rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1,
      Listing8LoopControl.memory mode origin l t g node rule ctx old state image.control]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image.control)
  have bounds:=(reset_bounds mode origin l t g node rule ctx).reset
  have entry:=Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted
  have current:=Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted
  have actual:=StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)
  have identity:=Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body
  rw [table_length] at identity
  change Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)=_ at identity
  change _=Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start at entry
  change Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) _ at current
  change StringStack.Trace mode (Listing8LoopTable.finish mode origin l t g node rule state)
    ((Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))).map (StringStoreWrites.liftDword mode))
    (Listing8LoopReset.finish mode origin l t g node rule state) at actual
  rw [identity] at bounds entry current actual
  exact Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial
    (Listing8GlobalControlRegions.reset mode origin g.transitions bounds _ entry current) actual

/-- All final updated node declarations share the global control certificate
and their precise single-word active owner certificate at the same prefixes. -/
theorem nodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8LoopReset.finish mode origin l t g node rule state) :=
  StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
    (Listing8GlobalDeclarationBindings.nodes mode origin (Listing8GraphStep.updated g node rule)
      (Listing8GraphStep.native_bounds mode origin g node rule ctx.native) _
      (Listing8LoopTerminal.input_entry mode origin l t g node rule ctx old state image halted)
      (Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted).1
      (reset_property mode origin l t g node rule ctx old state image halted))

theorem property (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8GlobalControlTemplates.Property mode origin
      (Listing8LoopTerminal.finish mode origin l t g node rule state).principal.memory := by
  rw [(Listing8LoopTerminal.result mode origin l t g node rule ctx old state image halted).2.1]
  exact reset_property mode origin l t g node rule ctx old state image halted

/-- The complete maintained terminal iteration includes main, failure/CALL,
both possible target descriptors, every transition, reset and every node. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (Listing8LoopTerminal.program mode origin l t g node rule state)
      (Listing8LoopTerminal.finish mode origin l t g node rule state) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8LoopTerminal.program mode origin l t g node rule state) state := by
  have before:=Listing8GlobalMainControlTemplates.terminal mode origin l t g node rule ctx old state image halted
  refine ⟨Listing8LoopTerminal.trace mode origin l t g node rule ctx old state image halted,?_⟩
  rw [Listing8LoopTerminal.program,Listing8GlobalLoopMainRegions.lift_dword,StringTemplateStates.append,
    StringWrites.trace_run_eq mode before.1]
  exact ⟨before.2,nodes mode origin l t g node rule ctx old state image halted⟩

end SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates
