module
public import SmcTuring.Appendix.Listing8InputCatalogInitial
public import SmcTuring.Appendix.Listing8JointOwnerPointerPurity
public import SmcTuring.Appendix.Listing8MaintainedJointPhases

public section
namespace SmcTuring.Appendix.Listing8JointInputCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (v : Values mode) :=
  ((Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)
@[expose] def Local (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) : Prop :=
  ∀ window∈MixedTemplateGeometry.windows mode l.input.start (Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh),
    Listing8InputJointTemplates.ValidWindow mode window memory

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) memory)
    (allowed : Listing8InputStoreFields.Allowed mode origin l address packet.length) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) (ByteMemory.putBytes memory address packet) :=
  ⟨DwordTemplateCollection.store_all _ memory address packet initial.1
      (Listing8InputCrossCatalogFields.retarget mode origin l t g node rule ctx address packet.length allowed),
    Listing8InputCrossCatalogFields.macros_store mode origin l t g node rule ctx memory address packet initial.2.1 allowed,
    Listing8OwnerPointerFrames.store mode _ memory address packet initial.2.2
      (Listing8InputCrossCatalogFields.owners mode origin l t g node rule ctx address packet.length allowed)⟩

/-- Inactive catalogs and the executing SUB/XOR/AND input catalog share
EVERY native prefix. All owner headers remain valid with an empty region. -/
theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Local mode l (values mode origin g node rule) reached.principal.memory)
      (forms mode l (values mode origin g node rule)) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalMainPrefixRegions.regions mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent)
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _ bounds state current.entry current.forward image.prefixCurrent))
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalInputRegions.regions mode origin l t g node rule ctx old state current)
  have core:=StringStoreTemplateRuns.preserve mode (Listing8InputStoreFields.Allowed mode origin l)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8InputCatalogInitial.initial mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent)
    (store mode origin l t g node rule ctx) (Listing8InputStoreFields.regions mode origin l t g node rule ctx old state current)
  have joined:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨⟨all.1,(fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all.2.1 template member)),
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits all.2.2.1.1,
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits all.2.2.1.2⟩,
        Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all.2.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalRun core)
  exact JointTemplateStates.join mode _ _ _ _ joined
    (Listing8JointTemplateBindings.graph_input mode origin l t g node rule ctx old state current)

/-- The SAME invariant now appends the complete input phase to the actual
owner/pointer prefix; no later catalog or memory image is a premise. -/
theorem owner_pointer_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l
      (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++forms mode l (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have actual:=StringStack.trace_append mode
    (StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying))
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _ bounds state current.entry current.forward image.prefixCurrent))
  change StringStack.Trace mode _ (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)) _ at actual
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨Listing8JointOwnerPointerPurity.main mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1) (main mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l
      (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++forms mode l (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initial:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact owner_pointer_input mode origin l t g node rule ctx old state image.body.state.head.graph initial

end SmcTuring.Appendix.Listing8JointInputCatalog
