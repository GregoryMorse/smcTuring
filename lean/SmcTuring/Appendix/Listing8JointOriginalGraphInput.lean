module
public import SmcTuring.Appendix.Listing8OriginalGraphInputFields

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphInput
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringTemplateStates.Run
set_option maxHeartbeats 2000000
@[expose] def Property (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory ∧
    ∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Listing8OwnerTemplateCollection.Decodes mode template memory

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have packets:=Listing8MainGraphPrefix.source_graph mode origin l t g node rule ctx old state current
  exact Listing8OriginalGraphCatalog.from_initial mode origin g _ packets.1 packets.2

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin g reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have kept:=StringStoreTemplateRuns.preserve mode (Listing8InputStoreFields.Allowed mode origin l)
    (Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _
    (initial mode origin l t g node rule ctx old state current)
    (Listing8OriginalGraphInputFields.store mode origin l t g node rule ctx)
    (Listing8InputStoreFields.regions mode origin l t g node rule ctx old state current)
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached headers => ⟨headers,fun template member => Listing8OwnerTemplateCollection.decodes mode template reached.principal.memory (headers template member)⟩) kept

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointInputCatalog.Local mode l (values mode origin g node rule) reached.principal.memory) ∧
      Property mode origin g reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  JointTemplateStates.join mode _ _ _ _
    (Listing8JointInputCatalog.main mode origin l t g node rule ctx old state current global)
    (all_states mode origin l t g node rule ctx old state current)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      (Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointInputCatalog.Local mode l (values mode origin g node rule) reached.principal.memory) ∧
      Property mode origin g reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact main mode origin l t g node rule ctx old state image.body.state.head.graph initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphInput
