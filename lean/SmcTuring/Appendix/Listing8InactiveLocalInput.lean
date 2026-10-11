module
public import SmcTuring.Appendix.Listing8InactiveLocalCatalog

public section
namespace SmcTuring.Appendix.Listing8InactiveLocalInput
open Native Listing8CopyImage Listing8SourceGraph Listing8InactiveLocalCatalog
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Property (mode : Mode) (l : Layout) (sentinel begin : Nat) (state : StringExecution.State mode) : Prop :=
  Listing8WholeHeadTemplates.Property mode (Listing8DirectionGeometry.region mode l) state ∧
  Listing8StateExecutableTemplates.Property mode (Listing8StateGeometry.region mode l) state ∧
  Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureGeometry.region mode l sentinel begin) state.principal.memory

@[expose] def Decodes (mode : Mode) (l : Layout) (sentinel begin : Nat) (memory : ByteMemory.Memory) : Prop :=
  (∀ descriptor∈Listing8DirectionTemplateFields.templates mode (Listing8DirectionGeometry.region mode l),
    DwordTemplateCollection.Decodes mode descriptor memory) ∧
  (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode (Listing8DirectionGeometry.region mode l),
    MixedFixedTemplates.Decodes mode descriptor memory) ∧
  (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l),
    DwordXorTemplates.Decodes mode helper memory) ∧
  (∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (Listing8StateGeometry.region mode l),
    DwordTemplateCollection.Decodes mode descriptor memory) ∧
  (∀ descriptor∈Listing8StateTemplateFields.fixed mode (Listing8StateGeometry.region mode l),
    MixedFixedTemplates.Decodes mode descriptor memory) ∧
  Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureGeometry.region mode l sentinel begin) memory

theorem decodes (mode : Mode) (l : Layout) (sentinel begin : Nat) (state : StringExecution.State mode)
    (current : Property mode l sentinel begin state) : Decodes mode l sentinel begin state.principal.memory :=
  ⟨fun descriptor member => DwordTemplateCollection.decodes mode descriptor _ (current.1.1 descriptor member),
    fun descriptor member => MixedFixedTemplates.decodes mode descriptor _ (current.1.2.1 descriptor member),
    fun helper member => DwordXorTemplates.decodes mode helper _ (current.1.2.2 helper member),
    fun descriptor member => DwordTemplateCollection.decodes mode descriptor _ (current.2.1.1 descriptor member),
    fun descriptor member => MixedFixedTemplates.decodes mode descriptor _ (current.2.1.2 descriptor member),current.2.2⟩

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Snapshot mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state.principal.memory
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  intro w member
  rcases member with head | middle | failure
  · exact Listing8LoopDirectionPrefix.prefix_window mode l t _ old bounds.state.head state
      current.body.state.head.graph.entry current.body.state.head.graph.forward image.state.head w head
  · exact Listing8LoopStatePrefix.prefix_window mode l t _ old bounds.state state
      current.body.state.head.graph.entry current.body.state.head.graph.forward image.state w middle
  · exact Listing8LoopFailurePrefix.prefix_window mode l t _ old _ _ bounds state
      current.body.state.head.graph.entry current.body.state.head.graph.forward image w.1 w.2 failure.1

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Outside mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  apply StringStoreRegions.mixed mode _ _ _
  exact Listing8InputTemplateRegions.mask_complete mode l.input _ _ old.pending _ old.mask ctx.resources.inputFits
    (Listing8InputBounds.masks mode l bounds.input.prefixBounds.fields)
    (Listing8InputBounds.update mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources)
    (Listing8InputBounds.outside mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources) _
    (Listing8MainPrefix.entry mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    (Listing8MainInputImage.current mode l t _ old bounds.input state current.entry current.forward image)
    (Listing8MainPrefixFrames.head_cursor mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    _ (fields mode origin l t g node rule ctx)

theorem snapshots (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Snapshot mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) state.principal.memory reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  StringStoreTemplateRuns.preserve mode _ _ _ _ (initial mode origin l t g node rule ctx old state current)
    (store mode l _ _ state.principal.memory)
    (regions mode origin l t g node rule ctx old state current.body.state.head.graph)

theorem from_snapshot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state reached : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (snapshot : Snapshot mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      state.principal.memory reached.principal.memory) :
    Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached := by
  have head:=Listing8LoopDirectionImage.transport mode (Listing8DirectionGeometry.region mode l)
    state.principal.memory reached.principal.memory current.body.state.head.fragments
    (fun w member => snapshot w (Or.inl member))
  have middle:=Listing8LoopStateImage.transport mode (Listing8StateGeometry.region mode l)
    state.principal.memory reached.principal.memory current.body.state.fragments
    (fun w member => snapshot w (Or.inr (Or.inl member)))
  let layout:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have failure:=Listing8FailureReuseTransport.current mode layout state.principal.memory reached.principal.memory current.body.failure
    (fun observed count lower upper => snapshot (observed,count) (Or.inr (Or.inr ⟨lower,by
      have after : Listing8FailureLayout.endPC mode layout≤Listing8FailureLayout.callPC mode layout+5 := by
        unfold Listing8FailureLayout.callPC;omega
      exact upper.trans after⟩)))
  have callAt:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode layout=Listing8JumpLayout.callPC mode origin at callAt
  have callImage : ByteMemory.bytesAt reached.principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (Listing8JumpLayout.call mode origin false) := by
    have lower : layout.start≤Listing8FailureLayout.callPC mode layout := by
      unfold Listing8FailureLayout.callPC Listing8FailureLayout.endPC Listing8FailureLayout.xorPC Listing8FailureLayout.andPC Listing8FailureLayout.storePC Listing8FailureLayout.notPC Listing8FailureLayout.comparisonPC Listing8FailureLayout.ownerPC
      omega
    have kept:=snapshot (Listing8FailureLayout.callPC mode layout,5) (Or.inr (Or.inr ⟨lower,Nat.le_refl _⟩))
    change ByteMemory.bytesAt reached.principal.memory (Listing8FailureLayout.callPC mode layout) 5=
      ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode layout) 5 at kept
    rw [←callAt,kept,callAt]
    exact current.callImage
  have callHeader:=RelativeCallTemplate.initial mode (Listing8JumpLayout.callPC mode origin) _ reached.principal.memory callImage
  rw [←callAt] at callHeader
  refine ⟨Listing8WholeHeadTemplates.initial mode _ reached head.helpers ?_ head.xorImage,
    Listing8StateExecutableTemplates.initial mode _ reached middle.helpers middle.headers,
    Listing8FailureExecutableTemplates.decodes mode layout reached.principal.memory
      (Listing8FailureExecutableTemplates.initial mode layout reached.principal.memory failure callHeader)⟩
  intro site member
  simp only [Listing8DirectionTemplateFields.sites,List.mem_append] at member
  rcases member with (first | mask) | last
  · exact head.arithmetic site first
  · exact head.tailHeaders site (List.mem_append_left _ mask)
  · exact head.tailHeaders site (List.mem_append_right _ last)

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  StringTemplateStates.monotone mode _ _ _ _
    (fun reached snapshot => from_snapshot mode origin l t g node rule ctx old state reached current snapshot)
    (snapshots mode origin l t g node rule ctx old state current)

theorem all_decodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) reached ∧ Decodes mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  StringTemplateStates.monotone mode _ _ _ _ (fun reached intact => ⟨intact,decodes mode l _ _ reached intact⟩)
    (all_states mode origin l t g node rule ctx old state current)

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      ((Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointInputCatalog.Local mode l (values mode origin g node rule) reached.principal.memory) ∧
        Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory) ∧
      (Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached ∧
        Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory))
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  JointTemplateStates.join mode _ _ _ _
    (Listing8JointOriginalGraphInput.main mode origin l t g node rule ctx old state current.body.state.head.graph global)
    (all_decodes mode origin l t g node rule ctx old state current)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      ((Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointInputCatalog.Local mode l (values mode origin g node rule) reached.principal.memory) ∧
        Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory) ∧
      (Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached ∧
        Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory))
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact main mode origin l t g node rule ctx old state current initialGlobal

end SmcTuring.Appendix.Listing8InactiveLocalInput
