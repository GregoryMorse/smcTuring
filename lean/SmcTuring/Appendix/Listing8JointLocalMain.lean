module
public import SmcTuring.Appendix.Listing8JointLocalPrefixRun

public section
namespace SmcTuring.Appendix.Listing8JointLocalMain
open Native Listing8CopyImage Listing8SourceGraph Listing8JointLocalCatalog
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (state : StringExecution.State mode) : Prop :=
  Listing8JointOriginalGraphMain.Property mode origin l v g state ∧
  Listing8JointLocalCatalog.Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state.principal.memory ∧
  Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state.principal.memory ∧
  Listing8JointInputCatalog.Local mode l v state.principal.memory

theorem forms_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    Listing8LoopControl.program mode origin l t g node rule state=
      (Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++
      Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state := by
  simp only [Listing8LoopControl.program,Listing8LoopFailure.program,List.map_append,Listing8GlobalLoopMainRegions.lift_dword,
    Listing8JointOriginalGraphFailure.forms,Listing8JointOriginalGraphFailure.failureForms,Listing8JointOriginalGraphState.forms,
    Listing8LoopState.program,Listing8LoopHead.program,Listing8LoopDirection.program,Listing8MainInput.program,
    Listing8JointInputCatalog.forms,Listing8JointHeadCatalog.forms,Listing8WholeHeadTemplates.program,
    Listing8JointStateCatalog.forms,Listing8JointFailureCatalog.forms,Listing8LoopDirection.finish,List.append_assoc]
  rfl

theorem local_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointLocalCatalog.Property mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _ bounds state graph.entry graph.forward image.prefixCurrent)
  rw [forms_shape,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨Listing8JointLocalPrefixRun.all_states mode origin l t g node rule ctx old state current,
    Listing8JointLocalContinuation.through_control mode origin l t g node rule ctx old state current⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Property mode origin l (values mode origin g node rule) g)
      (Listing8LoopControl.program mode origin l t g node rule state) state :=
  JointTemplateStates.join mode _ _ _ _
    (Listing8JointOriginalGraphMain.maintained mode origin l t g node rule ctx old state current)
    (StringTemplateStates.monotone mode _ _ _ _
      (fun reached all => ⟨all,decodes mode l _ _ reached.principal.memory all,
        input_windows mode l (values mode origin g node rule) _ _ reached.principal.memory all⟩)
      (local_states mode origin l t g node rule ctx old state current))

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Property mode origin l (values mode origin g node rule) g (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have all:=maintained mode origin l t g node rule ctx old state current
  have actual:=Listing8LoopControl.trace mode origin l t g node rule ctx old state current
  have result:=StringTemplateStates.at_prefix mode _ _ [] state (by simpa only [List.append_nil] using all)
  rw [StringWrites.trace_run_eq mode actual] at result
  exact result

theorem at_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule state=before++after) :
    Property mode origin l (values mode origin g node rule) g (StringWrites.run mode before state) := by
  have all:=maintained mode origin l t g node rule ctx old state current
  rw [cut] at all
  exact StringTemplateStates.at_prefix mode _ before after state all

end SmcTuring.Appendix.Listing8JointLocalMain
