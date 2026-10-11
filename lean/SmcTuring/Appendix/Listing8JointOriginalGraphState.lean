module
public import SmcTuring.Appendix.Listing8OriginalGraphTransport

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphState
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  Listing8JointOwnerPointerPurity.Property mode origin l v memory ∧ Listing8JointOriginalGraphInput.Property mode origin g memory
@[expose] def forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  (Listing8JointInputCatalog.forms mode l v++Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t v state))++
    Listing8JointStateCatalog.forms mode l (Listing8LoopHead.finish mode l t v state)

theorem input_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have b:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _
    (StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1)
      (Listing8JointOriginalGraphInput.all_states mode origin l t g node rule ctx old state current))
    (StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old b state current.entry current.forward image))

theorem head_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainInput.finish mode l t (values mode origin g node rule) state)
      (Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have actual:=StringStack.trace_append mode
    (StringDwordWritesBridge.trace mode (Listing8LoopDirection.direction_trace mode l t _ old b state current.graph.entry current.graph.forward image))
    (StringDwordWritesBridge.trace mode (Listing8LoopHead.head_trace mode l t _ old b state current.graph.entry current.graph.forward image))
  rw [←List.map_append] at actual
  exact actual

theorem head_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointHeadCatalog.Local mode l reached.principal.memory) ∧
      Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory)
      (Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8MainInput.endpoint mode l t _ old b.input state current.graph.entry current.graph.forward image.input
  have regions:=BoundedStoreRegions.monotone mode (Listing8HeadStoreFields.Allowed mode origin l)
    (Listing8MainCatalogTransport.Allowed mode origin l) _ _ (Listing8OriginalGraphTransport.head_allowed mode origin l)
    (Listing8HeadStoreFields.complete mode origin l t g node rule ctx _ entry)
  have kept:=StringStoreTemplateRuns.preserve mode (Listing8MainCatalogTransport.Allowed mode origin l)
    (Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _
    (input_endpoint mode origin l t g node rule ctx old state current.graph)
    (Listing8OriginalGraphTransport.store mode origin l t g node rule ctx) regions
  have decoded:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached headers => show Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory from
      ⟨headers,fun template member => Listing8OwnerTemplateCollection.decodes mode template reached.principal.memory (headers template member)⟩) kept
  exact JointTemplateStates.join mode _ _ _ _
    (Listing8JointHeadCatalog.main mode origin l t g node rule ctx old state current global) decoded

theorem head_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state).principal.memory :=
  Listing8InputCatalogInitial.endpoint mode _ _ _ _
    (StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.2.1)
      (head_main mode origin l t g node rule ctx old state current global))
    (head_trace mode origin l t g node rule ctx old state current)

theorem state_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory ∧
        Listing8JointStateCatalog.Local mode l reached.principal.memory) ∧
      Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory)
      (Listing8JointStateCatalog.forms mode l (Listing8LoopHead.finish mode l t (values mode origin g node rule) state))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have entry:=Listing8LoopHead.endpoint mode l t _ old b.head state current.head.graph.entry current.head.graph.forward image.head
  have kept:=StringStoreTemplateRuns.preserve mode (Listing8MainCatalogTransport.Allowed mode origin l)
    (Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _
    (head_endpoint mode origin l t g node rule ctx old state current.head global)
    (Listing8OriginalGraphTransport.store mode origin l t g node rule ctx)
    (Listing8StateStoreFields.regions mode origin l t g node rule ctx _ entry)
  have decoded:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached headers => show Listing8JointOriginalGraphInput.Property mode origin g reached.principal.memory from
      ⟨headers,fun template member => Listing8OwnerTemplateCollection.decodes mode template reached.principal.memory (headers template member)⟩) kept
  exact JointTemplateStates.join mode _ _ _ _
    (Listing8JointStateCatalog.main mode origin l t g node rule ctx old state current global) decoded

theorem through_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (forms mode l t (values mode origin g node rule) state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.head.graph
  have b:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  have inputTrace:=StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old b state current.head.graph.entry current.head.graph.forward image)
  change StringStack.Trace mode (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
    (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
    (Listing8MainInput.finish mode l t (values mode origin g node rule) state) at inputTrace
  have headTrace:=head_trace mode origin l t g node rule ctx old state current.head
  have whole:=StringStack.trace_append mode inputTrace headTrace
  rw [forms,StringTemplateStates.append,StringWrites.trace_run_eq mode whole,
    StringTemplateStates.append,StringWrites.trace_run_eq mode inputTrace]
  exact ⟨⟨StringTemplateStates.monotone mode _ _ _ _ (fun _ all => ⟨all.1.1,all.2⟩)
      (Listing8JointOriginalGraphInput.main mode origin l t g node rule ctx old state current.head.graph global),
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => ⟨all.1.1,all.2⟩)
      (head_main mode origin l t g node rule ctx old state current.head global)⟩,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => ⟨all.1.1,all.2⟩)
      (state_main mode origin l t g node rule ctx old state current global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (forms mode l t (values mode origin g node rule) state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact through_state mode origin l t g node rule ctx old state image.body.state initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphState
