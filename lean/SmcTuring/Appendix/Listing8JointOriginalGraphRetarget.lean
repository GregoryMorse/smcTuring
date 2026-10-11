module
public import SmcTuring.Appendix.Listing8OriginalGraphRetarget
public import SmcTuring.Appendix.Listing8JointRetargetOwnerPhase

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphRetarget
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (Listing8CopiedOwnerActiveRun.Allowed mode (Listing8OwnerImage.owners mode l v) packet ∨
      packet.address=nodePC mode origin g g.halt ∧ packet.bytes.length=mode.wordBytes) ∧
    (∀ template∈Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v),Outside mode template packet →
      Intact mode (Listing8PhaseOwnerCatalog.live mode template memory) memory ∧ Decodes mode (Listing8PhaseOwnerCatalog.live mode template memory) memory) ∧
    (∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Outside mode template packet →
      Intact mode template memory ∧ Decodes mode template memory)
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8JointOwnerPointerCatalog.Property mode origin l memory ∧ Certificate mode origin l v g memory

theorem from_phase (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (owners : Listing8PhaseOwnerCatalog.Certificate mode (Listing8OwnerImage.owners mode l v) memory)
    (originals : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,headers⟩:=owners
  exact ⟨packet,Or.inl allowed,headers,fun template member _ => ⟨originals template member,Listing8OwnerTemplateCollection.decodes mode template memory (originals template member)⟩⟩

theorem from_fixed (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (current : Listing8JointOriginalGraphFailure.Certificate mode origin l v g memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,headers⟩:=current
  refine ⟨packet,allowed,?_,?_⟩
  · intro template member outside
    exact Listing8PhaseOwnerCatalog.from_fixed mode template memory (headers template (List.mem_append_left _ member) outside).1
  · intro template member outside
    exact headers template (List.mem_append_right _ member) outside

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) (Listing8MainCopies.finish mode l state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
    show Property mode origin l (values mode origin g node rule) g reached.principal.memory from
    ⟨all.1.1,from_phase mode origin l _ g reached.principal.memory all.1.2 all.2⟩)
    (JointTemplateStates.join mode _ _ _ _
      (Listing8JointRetargetOwnerPhase.retarget mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying global)
      (Listing8OriginalGraphRetarget.all_states mode origin l t g node rule ctx old state current))

theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state) := by
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.retarget_trace mode l _ ctx.resources state graph.entry graph.forward image.prefixCurrent.copying)
  rw [Listing8JointRetargetOwnerPhase.forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨retarget mode origin l t g node rule ctx old state graph global,
    StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
      show Property mode origin l (values mode origin g node rule) g reached.principal.memory from
      ⟨all.1,from_fixed mode origin l _ g reached.principal.memory all.2⟩)
      (Listing8JointOriginalGraphOwner.through_control mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule state) (Listing8MainCopies.finish mode l state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact after_copies mode origin l t g node rule ctx old state current initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphRetarget
