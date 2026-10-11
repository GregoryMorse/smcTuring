module
public import SmcTuring.Appendix.Listing8OriginalGraphOwnerRun

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphOwner
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem forms_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    Listing8JointControlCatalog.suffix mode origin l t g node rule state=
      Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)++
        Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state := by
  simp only [Listing8JointControlCatalog.suffix,Listing8JointControlCatalog.earlier,
    Listing8JointFailureCatalog.earlier,Listing8JointStateCatalog.earlier,
    Listing8JointOriginalGraphFailure.forms,Listing8JointOriginalGraphFailure.failureForms,
    Listing8JointOriginalGraphState.forms,List.append_assoc]

theorem owner_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have safe : ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),
      Listing8OriginalGraphOwnerRun.ScalarSafe mode origin owner := by
    intro owner member
    cases owner with
    | pointer source copied value => trivial
    | scalar pc target value => exact Listing8OriginalGraphOwnerInitial.scalar_targets mode origin l t g node rule ctx pc target value member
  have observers:=Listing8OriginalGraphOwnerRun.run mode origin g _ _
    (Listing8CopiedOwners.chain mode l _) (Listing8CopiedOwners.valid mode l _ ctx.resources bounds)
    (Listing8CopiedOwners.outside mode l _ ctx.resources bounds) safe _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying)
    (Listing8OriginalGraphOwnerInitial.initial mode origin l t g node rule ctx old state current)
  have catalogs:=Listing8OwnerPhaseJointCatalog.main mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying global
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached all => by
    refine ⟨⟨all.1.1,all.1.2.2.1,all.1.2.2.2.1,all.1.2.2.2.2⟩,?_⟩
    obtain ⟨packet,allowed,headers⟩:=all.2
    exact ⟨packet,Or.inl allowed,headers⟩)
    (JointTemplateStates.join mode _ _ _ _ catalogs observers)

theorem owner_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  rw [(Listing8MainLiveOwners.result mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
    ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying).2.1]
  have keep (pc target : Nat) (value : BitVec 32)
      (member : Listing8OwnerSequence.Owner.scalar pc target value∈Listing8OwnerImage.owners mode l (values mode origin g node rule))
      (memory : ByteMemory.Memory) (headers : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) :
      Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (DwordCode.put memory target value) := by
    exact Listing8OriginalGraphFailureRun.store mode origin g memory target _ headers (by
      rw [LittleEndian.word_encode_length]
      exact Listing8OriginalGraphOwnerInitial.scalar_targets mode origin l t g node rule ctx pc target value member)
  apply keep (directionEntry mode (transitionParams mode l).destination) (l.direction+6) _ (by simp [Listing8OwnerImage.owners])
  apply keep (newEntry mode (transitionParams mode l).destination) (Listing8LiteralInput.updateStart mode l.input+6) _ (by simp [Listing8OwnerImage.owners])
  apply keep (currentEntry mode (transitionParams mode l).destination) (Listing8LiteralInput.scalarField mode l.input) _ (by simp [Listing8OwnerImage.owners])
  exact Listing8OriginalGraphOwnerInitial.initial mode origin l t g node rule ctx old state current

theorem pointer_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode))
      (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have position:=(Listing8MainLiveOwners.registers mode l _ ctx.resources bounds ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying).1
  have copied:=Listing8OwnerPointerFrames.all_states mode origin l t g node rule ctx _ position
    (Listing8CopiedOwnerCatalog.all_current mode _ _ (Listing8MainLiveOwners.retained_image mode l _ ctx.resources bounds
      ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying))
  have originals:=StringStoreTemplateRuns.preserve mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
    (Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _
    (owner_endpoint mode origin l t g node rule ctx old state current)
    (Listing8OriginalGraphFailureRun.store mode origin g)
    (Listing8OriginalGraphOwnerInitial.pointer_regions mode origin l t g node rule ctx _ position)
  have catalogs:=Listing8JointOwnerPointerCatalog.main mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying global
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached all => by
    refine ⟨all.1,?_⟩
    obtain ⟨packet,allowed,headers⟩:=Listing8OriginalGraphOwnerRun.empty mode origin g _ reached.principal.memory all.2.1 all.2.2
    exact ⟨packet,Or.inl allowed,headers⟩)
    (JointTemplateStates.join mode _ _ _ _ catalogs (JointTemplateStates.join mode _ _ _ _ copied originals))

theorem owner_pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state current.entry current.forward image.prefixCurrent.copying)
  rw [Listing8JointOwnerPointerCatalog.forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨owner_main mode origin l t g node rule ctx old state current global,pointer_main mode origin l t g node rule ctx old state current global⟩

theorem through_control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointControlCatalog.suffix mode origin l t g node rule state)
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have ownerTrace:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state graph.entry graph.forward image.prefixCurrent.copying)
  have pointerTrace:=StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds state graph.entry graph.forward image.prefixCurrent)
  have actual:=StringStack.trace_append mode ownerTrace pointerTrace
  change StringStack.Trace mode _ (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule)) _ at actual
  rw [forms_shape,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨owner_pointer mode origin l t g node rule ctx old state graph global,
    Listing8JointOriginalGraphFailure.through_control mode origin l t g node rule ctx old state current global⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointControlCatalog.suffix mode origin l t g node rule state)
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact through_control mode origin l t g node rule ctx old state current initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphOwner
