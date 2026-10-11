module
public import SmcTuring.Appendix.Listing8MacroPointerFrames
public import SmcTuring.Appendix.Listing8OwnerPhaseJointCatalog
public import SmcTuring.Appendix.Listing8GlobalPointerRegions

public section
namespace SmcTuring.Appendix.Listing8JointOwnerPointerCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  Listing8GlobalControlTemplates.Decodes mode origin memory ∧
    (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template memory) ∧
    StringEncodedTemplates.Decodes mode (nodeParams mode l) memory ∧
    StringEncodedTemplates.Decodes mode (transitionParams mode l) memory
@[expose] def forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  (Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l v)).map (StringStoreWrites.liftDword mode) ++
    (Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l reached.principal.memory)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode))
      (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state) := by
  have ownerBounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have ownerTrace:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
    ownerBounds ctx.fields.tapeReach state entry forward current)
  have location:=(Listing8MainLiveOwners.registers mode l _ ctx.resources ownerBounds ctx.fields.tapeReach state entry forward current).1
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalMainOwnerRegions.regions mode origin l t g node rule ctx state entry forward current)
    (StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources ownerBounds
      ctx.fields.tapeReach state entry forward current))
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalPointerRegions.regions mode origin l t g node rule ctx _ location)
  have retargetRun:=StringStoreRegions.arithmetic_states mode _ _ _
    (Listing8RetargetOwnerCatalog.initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)
    (Listing8RetargetOwnerCatalog.regions mode origin l t g node rule ctx state entry forward current)
  have retargetAt:=StringTemplateStates.at_prefix mode _ _ [] (Listing8MainRetarget.finish mode l _ state)
    (by simpa only [List.append_nil] using retargetRun)
  rw [StringWrites.trace_run_eq mode ownerTrace] at retargetAt
  have retargetLater:=StringStoreRegions.arithmetic_states mode _ _ _ retargetAt
    (Listing8RetargetPointerFields.regions mode l t ctx.copies _ location)
  have retargetDecoded:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all template member)) retargetLater
  have macroRun:=StringStoreTemplateRuns.preserve mode (fun address _ => patchStart mode l≤address)
    (Listing8MacroPointerFrames.Property mode l) _ _
    (Listing8MacroOwnerFrames.initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)
    (fun memory address packet both after => Listing8MacroPointerFrames.store mode l memory address packet both (Or.inl after))
    (Listing8MacroOwnerFrames.regions mode origin l t g node rule ctx state entry forward current)
  have macroAt:=StringTemplateStates.at_prefix mode _ _ [] (Listing8MainRetarget.finish mode l _ state)
    (by simpa only [List.append_nil] using macroRun)
  rw [StringWrites.trace_run_eq mode ownerTrace] at macroAt
  have macroLater:=Listing8MacroPointerFrames.all_decodes mode l t ctx.copies ctx.resources _ location macroAt
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun _ all => ⟨all.1.1,all.1.2,all.2.1,all.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ (JointTemplateStates.join mode _ _ _ _ globalRun retargetDecoded) macroLater)

/-- One identical invariant spans the entire owner phase and subsequent
word/DWORD transfers. All intermediate catalog states are derived. -/
theorem owner_pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l reached.principal.memory)
      (forms mode l t (values mode origin g node rule)) (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have owners:=Listing8OwnerPhaseJointCatalog.main mode origin l t g node rule ctx state entry forward current global
  have first:=StringTemplateStates.monotone mode _ _ _ _
    (fun _ all => show Property mode origin l _ from ⟨all.1,all.2.2.1,all.2.2.2.1,all.2.2.2.2⟩) owners
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current)
  rw [forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨first,main mode origin l t g node rule ctx state entry forward current global⟩

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    (forms mode l t v).length=if mode=.x86 then 31 else 40 := by
  rw [forms,List.length_append,Listing8OwnerPhaseJointCatalog.instruction_count,List.length_map,
    (Listing8PointerCopies.sizes mode l t).2.2]
  cases mode <;> rfl

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l reached.principal.memory)
      (forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initial:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  exact owner_pointer mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
    current.state.head.input.prefixCurrent.copying initial

/-- One original emitted image and actual bootstrap supply both joint macro
certificates, without a future packet, image, readiness or trace premise. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l reached.principal.memory)
      (forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) := by
  have initial:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed)
  have actual:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  change StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) at actual
  have regions:=BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Listing8GlobalControlLayout.Allowed mode origin)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (fun _ _ slots => Or.inl slots)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  have readyGlobal:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial regions actual
  apply owner_pointer mode origin l t g node rule ctx _ _ _
    (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed) readyGlobal
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

end SmcTuring.Appendix.Listing8JointOwnerPointerCatalog
