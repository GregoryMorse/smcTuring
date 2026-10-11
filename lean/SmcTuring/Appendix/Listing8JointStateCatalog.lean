module
public import SmcTuring.Appendix.Listing8StateStoreFields
public import SmcTuring.Appendix.Listing8JointHeadCatalog
public import SmcTuring.Native.StringTracePrefixes

public section
namespace SmcTuring.Appendix.Listing8JointStateCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)
@[expose] def earlier (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  (Listing8JointOwnerPointerCatalog.forms mode l t v++Listing8JointInputCatalog.forms mode l v)++
    Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t v state)
@[expose] def Local (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  (∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (Listing8StateGeometry.region mode l),DwordTemplateCollection.Decodes mode descriptor memory) ∧
    (∀ descriptor∈Listing8StateTemplateFields.fixed mode (Listing8StateGeometry.region mode l),MixedFixedTemplates.Decodes mode descriptor memory)

theorem prefix_forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    (Listing8LoopHead.program mode l t v state).map (StringStoreWrites.liftDword mode)=
      (Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode)++earlier mode l t v state := by
  simp only [Listing8LoopHead.program,Listing8LoopDirection.program,Listing8MainInput.program,
    Listing8MainPrefix.program,Listing8MainLiveOwners.program,earlier,Listing8JointOwnerPointerCatalog.forms,
    Listing8JointInputCatalog.forms,Listing8JointHeadCatalog.forms,Listing8WholeHeadTemplates.program,
    Listing8LoopDirection.finish,List.map_append,List.append_assoc]

theorem prefix_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainRetarget.finish mode l (values mode origin g node rule) state)
      (earlier mode l t (values mode origin g node rule) state) (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have whole:=StringDwordWritesBridge.trace mode (Listing8LoopHead.trace mode l t _ old b state current.graph.entry current.graph.forward image)
  rw [prefix_forms] at whole
  exact StringTracePrefixes.tail mode _ _ _ _ _ whole
    (StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state current.graph.entry current.graph.forward image.input.prefixCurrent.copying))

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8MainInput.endpoint mode l t _ old b.input state current.graph.entry current.graph.forward image.input
  have core:=StringStoreTemplateRuns.preserve mode (Listing8HeadStoreFields.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8JointHeadCatalog.initial mode origin l t g node rule ctx old state current.graph)
    (Listing8HeadCrossCatalogFields.store mode origin l t g node rule ctx)
    (Listing8HeadStoreFields.complete mode origin l t g node rule ctx _ entry)
  have actual:=StringStack.trace_append mode
    (StringDwordWritesBridge.trace mode (Listing8LoopDirection.direction_trace mode l t _ old b state current.graph.entry current.graph.forward image))
    (StringDwordWritesBridge.trace mode (Listing8LoopHead.head_trace mode l t _ old b state current.graph.entry current.graph.forward image))
  rw [←List.map_append] at actual
  change StringStack.Trace mode _ (Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state)) _ at actual
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _ core actual

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧ Local mode l reached.principal.memory)
      (forms mode l (Listing8LoopHead.finish mode l t (values mode origin g node rule) state))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8LoopHead.endpoint mode l t _ old b.head state current.head.graph.entry current.head.graph.forward image.head
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalLoopMainRegions.head mode origin l t g node rule ctx old state current.head)
    (Listing8LoopHeadWrites.execute mode origin l t g node rule ctx old state current.head).1
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalSelectionRegions.state mode origin l t g node rule ctx _ entry)
  have core:=StringStoreTemplateRuns.preserve mode (Listing8MainCatalogTransport.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (initial mode origin l t g node rule ctx old state current.head)
    (Listing8MainCatalogTransport.store mode origin l t g node rule ctx)
    (Listing8StateStoreFields.regions mode origin l t g node rule ctx _ entry)
  have joined:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨⟨all.1,(fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all.2.1 template member)),
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits all.2.2.1.1,
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits all.2.2.1.2⟩,
        Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all.2.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalRun core)
  exact JointTemplateStates.join mode _ _ _ _ joined
    (Listing8StateTemplateBindings.maintained mode l t _ old b state current.head.graph.entry current.head.graph.forward image)

theorem through_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (earlier mode l t (values mode origin g node rule) state++forms mode l (Listing8LoopHead.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode (prefix_trace mode origin l t g node rule ctx old state current.head)]
  exact ⟨Listing8JointHeadCatalog.owner_pointer_input_head mode origin l t g node rule ctx old state current.head global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1) (main mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (earlier mode l t (values mode origin g node rule) state++forms mode l (Listing8LoopHead.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact through_state mode origin l t g node rule ctx old state image.body.state initialGlobal

end SmcTuring.Appendix.Listing8JointStateCatalog
