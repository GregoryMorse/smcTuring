module
public import SmcTuring.Appendix.Listing8HeadCrossCatalogFields
public import SmcTuring.Appendix.Listing8JointInputCatalog

public section
namespace SmcTuring.Appendix.Listing8JointHeadCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  (Listing8WholeHeadTemplates.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)
@[expose] def Local (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  (∀ descriptor∈Listing8DirectionTemplateFields.templates mode (Listing8DirectionGeometry.region mode l),DwordTemplateCollection.Decodes mode descriptor memory) ∧
    (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode (Listing8DirectionGeometry.region mode l),MixedFixedTemplates.Decodes mode descriptor memory) ∧
    (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l),DwordXorTemplates.Decodes mode helper memory)

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have b:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  have core:=StringStoreTemplateRuns.preserve mode (Listing8InputStoreFields.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8InputCatalogInitial.initial mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent)
    (Listing8JointInputCatalog.store mode origin l t g node rule ctx) (Listing8InputStoreFields.regions mode origin l t g node rule ctx old state current)
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _ core
    (StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old b state current.entry current.forward image))

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧ Local mode l reached.principal.memory)
      (forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8MainInput.endpoint mode l t _ old b.input state current.graph.entry current.graph.forward image.input
  have actual:=StringDwordWritesBridge.trace mode (Listing8LoopDirection.direction_trace mode l t _ old b state current.graph.entry current.graph.forward image)
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalLoopMainRegions.input mode origin l t g node rule ctx old state current.graph)
    (Listing8MainInputWrites.execute mode origin l t g node rule ctx old state current.graph).1
  have regions : StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) := by
    rw [forms,Listing8WholeHeadTemplates.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode actual]
    exact ⟨Listing8GlobalSelectionRegions.direction mode origin l t g node rule ctx _ entry,
      Listing8GlobalSelectionRegions.head mode origin l t g node rule ctx _
        (Listing8LoopDirection.endpoint mode l t _ old b state current.graph.entry current.graph.forward image)⟩
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt regions
  have core:=StringStoreTemplateRuns.preserve mode (Listing8HeadStoreFields.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (initial mode origin l t g node rule ctx old state current.graph)
    (Listing8HeadCrossCatalogFields.store mode origin l t g node rule ctx)
    (Listing8HeadStoreFields.complete mode origin l t g node rule ctx _ entry)
  have joined:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨⟨all.1,(fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all.2.1 template member)),
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits all.2.2.1.1,
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits all.2.2.1.2⟩,
        Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all.2.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalRun core)
  have localImage:=Listing8LoopDirectionPrefix.current_after_input mode l t _ old b state current.graph.entry current.graph.forward image
  have headers : DwordPackets.Intact mode (Listing8DirectionTemplateFields.sites mode (Listing8DirectionGeometry.region mode l))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
    intro site member
    simp only [Listing8DirectionTemplateFields.sites,List.mem_append] at member
    rcases member with (arithmetic | mask) | head
    · exact localImage.arithmetic site arithmetic
    · exact localImage.tailHeaders site (List.mem_append_left _ mask)
    · exact localImage.tailHeaders site (List.mem_append_right _ head)
  exact JointTemplateStates.join mode _ _ _ _ joined
    (Listing8WholeHeadTemplates.all_decodes mode _ (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head)
      _ entry localImage.helpers headers localImage.xorImage)

theorem owner_pointer_input_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      ((Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++Listing8JointInputCatalog.forms mode l (values mode origin g node rule))++
        forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.graph
  have b:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  have earlier:=StringStack.trace_append mode
    (StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state current.graph.entry current.graph.forward image.prefixCurrent.copying))
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _ b.input.prefixBounds state current.graph.entry current.graph.forward image.prefixCurrent))
  have actual:=StringStack.trace_append mode earlier
    (StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old b state current.graph.entry current.graph.forward image))
  change StringStack.Trace mode _ (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++Listing8JointInputCatalog.forms mode l (values mode origin g node rule)) _ at actual
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨Listing8JointInputCatalog.owner_pointer_input mode origin l t g node rule ctx old state current.graph global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1) (main mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory)
      ((Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++Listing8JointInputCatalog.forms mode l (values mode origin g node rule))++
        forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact owner_pointer_input_head mode origin l t g node rule ctx old state image.body.state.head initialGlobal

end SmcTuring.Appendix.Listing8JointHeadCatalog
