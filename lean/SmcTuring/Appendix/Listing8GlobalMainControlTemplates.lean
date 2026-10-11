module
public import SmcTuring.Appendix.Listing8GlobalLoopMainRegions
public import SmcTuring.Appendix.Listing8GlobalControlReconstruction
public import SmcTuring.Appendix.Listing8GlobalControlBindings
public import SmcTuring.Appendix.Listing8GlobalDeclarationBindings
public import SmcTuring.Appendix.Listing8GlobalResetBindings

public section
set_option maxHeartbeats 3000000
namespace SmcTuring.Appendix.Listing8GlobalMainControlTemplates
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have trace:=Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated bounds image.body
  change StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
    (((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)++
      Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)) state
  apply (StringStoreRegions.append mode (Listing8GlobalControlLayout.Allowed mode origin) _ _ state).mpr
  refine ⟨Listing8GlobalLoopMainRegions.failure mode origin l t g node rule ctx old state image.body,?_⟩
  have endpoint : StringWrites.run mode
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous) state=
      Listing8LoopControl.failureEnd mode origin l t g node rule state := StringWrites.trace_run_eq mode trace
  rw [endpoint]
  exact Listing8GlobalControlRegions.jump mode origin _ _ (Listing8LoopControl.entry mode origin l t g node rule ctx old state image)
    (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body) (Listing8LoopControl.current mode origin l t g node rule ctx old state image)

/-- Abstract trace transfer keeps kernel reduction independent of the size of
the concrete emitted main body. The concrete wrapper derives every input. -/
theorem reconstruct (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode))
    (state final : StringExecution.State mode) (memory : ByteMemory.Memory)
    (trace : StringStack.Trace mode state forms final)
    (owned : StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin) forms state)
    (same : final.principal.memory=memory)
    (ending : Listing8GlobalControlTemplates.Property mode origin memory) :
    StringStack.Trace mode state forms final ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      forms state := by
  have kept:=Listing8GlobalControlReconstruction.all_states mode origin forms state owned (by
    rw [StringWrites.trace_run_eq mode trace,same]
    exact ending)
  exact ⟨trace,StringTemplateStates.monotone mode _ _ forms state
    (fun reached intact => Listing8GlobalControlTemplates.decodes mode origin _ intact) kept⟩

/-- All global control templates decode at the same every reached prefix of
the complete actual main iteration, including both copies, retargeting,
every copied owner, pointer/input/head/state/failure and CALL/target store. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode state (Listing8LoopControl.program mode origin l t g node rule state)
      (Listing8LoopControl.finish mode origin l t g node rule state) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8LoopControl.program mode origin l t g node rule state) state :=
  reconstruct mode origin (Listing8LoopControl.program mode origin l t g node rule state) state
    (Listing8LoopControl.finish mode origin l t g node rule state)
    (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory
    (Listing8LoopControl.trace mode origin l t g node rule ctx old state image)
    (regions mode origin l t g node rule ctx old state image)
    (Listing8LoopControl.memory mode origin l t g node rule ctx old state image)
    (Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image))

/-- The terminal case carries the same global catalog from actual main entry
through every transition declaration and complete reset, with all future
states, images, packets, traces and store regions concluded. -/
theorem terminal (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode state (Listing8LoopReset.program mode origin l t g node rule state)
      (Listing8LoopReset.finish mode origin l t g node rule state) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8LoopReset.program mode origin l t g node rule state) state := by
  have main:=execute mode origin l t g node rule ctx old state image.control
  have table:=StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)
  refine ⟨Listing8LoopReset.trace mode origin l t g node rule ctx old state image halted,?_⟩
  simp only [Listing8LoopReset.program,Listing8LoopTable.program,Listing8GlobalLoopMainRegions.lift_dword]
  rw [StringTemplateStates.append,StringTemplateStates.append]
  simp only [StringWrites.run_append,StringWrites.trace_run_eq mode main.1,StringWrites.trace_run_eq mode table]
  refine ⟨⟨main.2,?_⟩,?_⟩
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
      (Listing8GlobalDeclarationBindings.maintained mode origin l t g node rule ctx old state image.control halted)
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
      (Listing8GlobalResetBindings.maintained mode origin l t g node rule ctx old state image halted)

theorem at_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (before after : List (StringStack.Form mode)) (cut : Listing8LoopControl.program mode origin l t g node rule state=before++after) :
    Listing8GlobalControlTemplates.Decodes mode origin (StringWrites.run mode before state).principal.memory := by
  exact StringTemplateStates.at_prefix mode _ before after state
    (cut ▸ (execute mode origin l t g node rule ctx old state image).2)

end SmcTuring.Appendix.Listing8GlobalMainControlTemplates
