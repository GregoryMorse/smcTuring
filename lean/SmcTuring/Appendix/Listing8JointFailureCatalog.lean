module
public import SmcTuring.Appendix.Listing8FailureCrossCatalogFields
public import SmcTuring.Appendix.Listing8JointStateCatalog

public section
namespace SmcTuring.Appendix.Listing8JointFailureCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (state : StringExecution.State mode) :=
  (Listing8FailureTrace.program mode (Listing8FailureCrossCatalogFields.region mode origin l g) state).map StringStack.Form.previous
@[expose] def earlier (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8JointStateCatalog.earlier mode l t v state++Listing8JointStateCatalog.forms mode l (Listing8LoopHead.finish mode l t v state)

theorem prefix_forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    (Listing8LoopState.program mode l t v state).map (StringStoreWrites.liftDword mode)=
      (Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode)++earlier mode l t v state := by
  simp only [Listing8LoopState.program,List.map_append,Listing8JointStateCatalog.prefix_forms,
    earlier,Listing8JointStateCatalog.forms,List.append_assoc]

theorem prefix_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainRetarget.finish mode l (values mode origin g node rule) state)
      (earlier mode l t (values mode origin g node rule) state) (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have whole:=StringDwordWritesBridge.trace mode (Listing8LoopState.trace mode l t _ old b state current.head.graph.entry current.head.graph.forward image)
  rw [prefix_forms] at whole
  exact StringTracePrefixes.tail mode _ _ _ _ _ whole
    (StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state current.head.graph.entry current.head.graph.forward image.head.input.prefixCurrent.copying))

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have b:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8LoopHead.endpoint mode l t _ old b.head state current.head.graph.entry current.head.graph.forward image.head
  have core:=StringStoreTemplateRuns.preserve mode (Listing8MainCatalogTransport.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8JointStateCatalog.initial mode origin l t g node rule ctx old state current.head)
    (Listing8MainCatalogTransport.store mode origin l t g node rule ctx)
    (Listing8StateStoreFields.regions mode origin l t g node rule ctx _ entry)
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _ core
    (StringDwordWritesBridge.trace mode (Listing8LoopState.state_trace mode l t _ old b state current.head.graph.entry current.head.graph.forward image))

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureCrossCatalogFields.region mode origin l g) reached.principal.memory)
      (forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state))
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have entry:=current.body.state.head.graph.entry
  have forward:=current.body.state.head.graph.forward
  have position:=Listing8LoopState.endpoint mode l t _ old b.state state entry forward image.state
  have ready:=Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ b state entry forward image
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalLoopMainRegions.state mode origin l t g node rule ctx old state current.body.state)
    (Listing8LoopStateWrites.execute mode origin l t g node rule ctx old state current.body.state).1
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalFailureRegions.regions mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
      (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _ position ready)
  have core:=StringStoreTemplateRuns.preserve mode (Listing8FailureCrossCatalogFields.Allowed mode origin l g)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (initial mode origin l t g node rule ctx old state current.body.state)
    (Listing8FailureCrossCatalogFields.store mode origin l t g node rule ctx)
    (Listing8FailureCrossCatalogFields.regions mode origin l t g node rule ctx _ position ready)
  have joined:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨⟨all.1,(fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all.2.1 template member)),
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits all.2.2.1.1,
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits all.2.2.1.2⟩,
        Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all.2.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalRun core)
  exact JointTemplateStates.join mode _ _ _ _ joined
    (Listing8FailureTemplateBindings.maintained mode origin l t g node rule ctx old state current)

theorem through_failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (earlier mode l t (values mode origin g node rule) state++forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode (prefix_trace mode origin l t g node rule ctx old state current.body.state)]
  exact ⟨Listing8JointStateCatalog.through_state mode origin l t g node rule ctx old state current.body.state global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1) (main mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (earlier mode l t (values mode origin g node rule) state++forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact through_failure mode origin l t g node rule ctx old state image initialGlobal

end SmcTuring.Appendix.Listing8JointFailureCatalog
