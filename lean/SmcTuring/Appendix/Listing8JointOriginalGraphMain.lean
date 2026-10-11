module
public import SmcTuring.Appendix.Listing8JointOriginalGraphRetarget

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphMain
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (Listing8CopiedOwnerActiveRun.Allowed mode (Listing8OwnerImage.owners mode l v) packet ∨
      ((packet.address=l.sourceNode ∨ packet.address=l.sourceTransition) ∧ packet.bytes.length=mode.wordBytes) ∨
      packet.address=nodePC mode origin g g.halt ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Outside mode template packet →
      Intact mode template memory ∧ Decodes mode template memory
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (state : StringExecution.State mode) :=
  Listing8JointCopyOwnerPrefixes.Catalog mode origin l state ∧ Certificate mode origin l v g state.principal.memory

theorem from_copy (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (current : Listing8JointOriginalGraphCopies.Certificate mode origin l g memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,headers⟩:=current
  refine ⟨packet,?_,headers⟩
  rcases allowed with restored | source
  · exact Or.inl (Or.inl restored)
  · exact Or.inr (Or.inl source)

theorem from_phase (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (current : Listing8JointOriginalGraphRetarget.Certificate mode origin l v g memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,_,headers⟩:=current
  refine ⟨packet,?_,headers⟩
  rcases allowed with owner | sentinel
  · exact Or.inl owner
  · exact Or.inr (Or.inr sentinel)

theorem forms_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    Listing8LoopControl.program mode origin l t g node rule state=
      (Listing8MainCopies.program mode l).map (StringWrites.liftString mode)++
        Listing8JointRetargetOwnerPhase.forms mode origin l t g node rule state := by
  simp only [Listing8LoopControl.program,Listing8JointRetargetOwnerPhase.forms,Listing8JointControlCatalog.suffix,
    Listing8JointControlCatalog.prefix_forms,Listing8JointRetargetControl.shape,List.append_assoc]

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (Property mode origin l (values mode origin g node rule) g)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have actual:=(Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state graph.entry graph.forward image.prefixCurrent.copying).1
  rw [forms_shape,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
      show Property mode origin l (values mode origin g node rule) g reached from
      ⟨all.1,from_copy mode origin l _ g reached.principal.memory all.2⟩)
      (Listing8JointOriginalGraphCopies.pair mode origin l t g node rule ctx old state graph global),
    StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
      show Property mode origin l (values mode origin g node rule) g reached from
      ⟨⟨all.1.1,all.1.2.2.1,all.1.2.2.2⟩,from_phase mode origin l _ g reached.principal.memory all.2⟩)
      (Listing8JointOriginalGraphRetarget.after_copies mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Property mode origin l (values mode origin g node rule) g)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact main mode origin l t g node rule ctx old state current initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphMain
