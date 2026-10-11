module
public import SmcTuring.Appendix.Listing8GlobalFailureBindings
public import SmcTuring.Appendix.Listing8GlobalDeclarationBindings
public import SmcTuring.Appendix.Listing8GlobalResetBindings

public section
namespace SmcTuring.Appendix.Listing8TerminalControlTemplates
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual terminal suffix starts at failure entry and includes its
CALL, selected target, every transition declaration and the complete reset. -/
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  ((Listing8FailureTrace.program mode
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous)++
    (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)++
    (((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode))++
    ((Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map (StringStoreWrites.liftDword mode))))

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (program mode origin l t g node rule state).length=(if mode=.x86 then 29 else 37)+11*g.transitions := by
  simp only [program,List.length_append,List.length_map,Listing8FailureTrace.instruction_count,
    Listing8JumpReturn.instruction_count,Listing8TableTrace.instruction_count,Listing8ResetLayout.instruction_count,table_length]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

/-- Every global descriptor decodes at every reached prefix of this complete
emitted suffix. All reached states and images are constructed from the
present main-entry invariant and the actual source-graph halt predicate. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8LoopState.finish mode l t (values mode origin g node rule) state)
      (program mode origin l t g node rule state) (Listing8LoopReset.finish mode origin l t g node rule state) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (program mode origin l t g node rule state) (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.control.body
  have f:=StringStack.previous_trace mode (Listing8LoopFailure.failure_trace mode l t _ _ _ old b state
    image.control.body.state.head.graph.entry image.control.body.state.head.graph.forward current)
  have c:=Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image.control
  change StringStack.Trace mode (Listing8LoopFailure.finish mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state) _ _ at c
  have d:=StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)
  have r:=StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)
  refine ⟨StringStack.trace_append mode f (StringStack.trace_append mode c (StringStack.trace_append mode d r)),?_⟩
  rw [program,StringTemplateStates.append]
  constructor
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
      (Listing8GlobalFailureBindings.maintained mode origin l t g node rule ctx old state image.control)
  · rw [StringWrites.trace_run_eq mode f,StringTemplateStates.append]
    constructor
    · exact Listing8GlobalControlBindings.maintained_jump mode origin l t g node rule ctx old state image.control
    · rw [StringWrites.trace_run_eq mode c,StringTemplateStates.append]
      constructor
      · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
          (Listing8GlobalDeclarationBindings.maintained mode origin l t g node rule ctx old state image.control halted)
      · rw [StringWrites.trace_run_eq mode d]
        exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
          (Listing8GlobalResetBindings.maintained mode origin l t g node rule ctx old state image halted)

theorem at_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule)
    (before after : List (StringStack.Form mode)) (cut : program mode origin l t g node rule state=before++after) :
    Listing8GlobalControlTemplates.Decodes mode origin
      (StringWrites.run mode before (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).principal.memory := by
  have kept:=(execute mode origin l t g node rule ctx old state image halted).2
  rw [cut] at kept
  exact StringTemplateStates.at_prefix mode _ before after _ kept

end SmcTuring.Appendix.Listing8TerminalControlTemplates
