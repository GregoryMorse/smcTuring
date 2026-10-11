module
public import SmcTuring.Appendix.Listing8CopiedOwnerActiveRun
public import SmcTuring.Appendix.Listing8GlobalMainOwnerRegions
public import SmcTuring.Appendix.Listing8GlobalControlProperties
public import SmcTuring.Appendix.Listing8JointMacroControl
public import SmcTuring.Appendix.Listing8GlobalRetargetRegions

public section
namespace SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerSequence
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- Global control and all original-source/copied owner descriptors refer to
the SAME every native prefix, outside the one exact active reader word. -/
theorem execute (mode : Mode) (origin : Nat) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (placed : ∀ owner∈owners,Listing8GlobalCopiedOwnerRegions.Placement mode origin owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode owners state.principal.memory)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8CopiedOwnerActiveRun.Certificate mode owners reached.principal.memory)
      ((program mode owners).map (StringStoreWrites.liftDword mode)) state :=
  JointTemplateStates.join mode _ _ _ state
    (Listing8GlobalControlTemplates.all_decodes mode origin _ state initial
      (Listing8GlobalCopiedOwnerRegions.regions mode origin owners start chain valid outside placed state entry present))
    (Listing8CopiedOwnerActiveRun.run mode owners start chain valid outside state entry present)

/-- Every observer packet is positively restored/preserved at the complete
owner-sequence endpoint, so the exact active exception can be empty there. -/
theorem endpoint (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode owners state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode owners)
      (finish mode owners state).principal.memory := by
  apply Listing8CopiedOwnerCatalog.all_current
  intro observer member
  exact retained_observer mode owners start chain valid outside state entry present observer (present observer member)
    (fun writer written => outside writer written observer member)

/-- Complete copy/retarget execution constructs every owner packet, entry,
word referent and exact global placement; only present bytes are supplied. -/
theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory)
      ((program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward current)
  have readyGlobal:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial
    (Listing8GlobalRetargetRegions.regions mode origin l t g node rule ctx state entry forward current) actual
  exact execute mode origin _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8GlobalMainOwnerRegions.placements mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current) readyGlobal

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory)
      ((program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
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
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory)
      ((program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
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

end SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates
