module
public import SmcTuring.Appendix.Listing8PhaseOwnerCatalog

public section
namespace SmcTuring.Appendix.Listing8JointRetargetOwnerPhase
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) : Prop :=
  Listing8JointOwnerPointerCatalog.Property mode origin l memory ∧
    Listing8PhaseOwnerCatalog.Certificate mode (Listing8OwnerImage.owners mode l v) memory
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  (Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++
    Listing8JointControlCatalog.suffix mode origin l t g node rule state

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l state) := by
  have pointers:=Listing8RetargetPointerOwners.all_states mode origin l t g node rule ctx state entry forward current
  have scalars:=Listing8RetargetTapeTemplates.all_states mode l _ ctx.resources ctx.fields.tapeReach _
    (Listing8MainCopies.registers mode l _ ctx.resources state entry forward current).1
    (Listing8MainCopies.retarget_current mode l _ ctx.resources state entry forward current)
  have owned:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached both => Listing8PhaseOwnerCatalog.empty mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory
      (Listing8PhaseOwnerCatalog.from_catalogs mode l (values mode origin g node rule) reached.principal.memory both.1 both.2))
    (JointTemplateStates.join mode _ _ _ _ pointers scalars)
  exact JointTemplateStates.join mode _ _ _ _
    (Listing8JointMainMacroCatalog.retarget mode origin l t g node rule ctx state entry forward current global) owned

theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state) := by
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.retarget_trace mode l _ ctx.resources state
    image.body.state.head.graph.entry image.body.state.head.graph.forward current.state.head.input.prefixCurrent.copying)
  rw [forms,StringTemplateStates.append,StringWrites.trace_run_eq mode trace]
  exact ⟨retarget mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
      current.state.head.input.prefixCurrent.copying global,
    StringTemplateStates.monotone mode _ _ _ _ (fun reached both =>
      show Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨both.1,Listing8PhaseOwnerCatalog.from_fixed_certificate mode _ reached.principal.memory both.2⟩)
      (Listing8JointControlCatalog.through_control mode origin l t g node rule ctx old state image global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      (forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact after_copies mode origin l t g node rule ctx old state image initialGlobal

theorem fixed_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
 :
    Listing8OwnerTemplateCollection.All mode
      (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state).principal.memory :=
  Listing8CopiedOwnerCatalog.all_current mode _ _
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (forms mode origin l t g node rule state).length=if mode=.x86 then 94 else 135 := by
  rw [forms,List.length_append,List.length_map,Listing8LiveRetarget.instruction_count,Listing8JointControlCatalog.instruction_count]
  cases mode <;> rfl

theorem original_retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) := by
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
  apply retarget mode origin l t g node rule ctx _ _ _
    (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed)
    (Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial regions actual)
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

end SmcTuring.Appendix.Listing8JointRetargetOwnerPhase
