module
public import SmcTuring.Appendix.Listing8OwnerPointerFrames
public import SmcTuring.Appendix.Listing8JointOwnerPointerCatalog

public section
namespace SmcTuring.Appendix.Listing8JointOwnerPointerPurity
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) : Prop :=
  Listing8JointOwnerPointerCatalog.Property mode origin l memory ∧
    Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l v) memory

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have owners:=Listing8JointCopiedOwnerTemplates.main mode origin l t g node rule ctx state entry forward current global
  have first:=StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.2) owners
  have present:=Listing8CopiedOwnerCatalog.all_current mode _ _
    (Listing8MainLiveOwners.retained_image mode l _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current)
  have location:=(Listing8MainLiveOwners.registers mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current).1
  have allPointers:=Listing8OwnerPointerFrames.all_states mode origin l t g node rule ctx _ location present
  have second:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all) allPointers
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current)
  have ownerRun : StringTemplateStates.Run mode (fun reached =>
      Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
    rw [Listing8JointOwnerPointerCatalog.forms,StringTemplateStates.append,StringWrites.trace_run_eq mode trace]
    exact ⟨first,second⟩
  exact JointTemplateStates.join mode _ _ _ _
    (Listing8JointOwnerPointerCatalog.owner_pointer mode origin l t g node rule ctx state entry forward current global) ownerRun

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initial:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  exact main mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
    current.state.head.input.prefixCurrent.copying initial

/-- One original emitted image and actual bootstrap supply both joint macro
certificates, without a future packet, image, readiness or trace premise. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
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
  apply main mode origin l t g node rule ctx _ _ _
    (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed) readyGlobal
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

end SmcTuring.Appendix.Listing8JointOwnerPointerPurity
