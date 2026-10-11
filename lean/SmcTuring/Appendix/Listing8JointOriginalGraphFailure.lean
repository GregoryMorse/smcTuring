module
public import SmcTuring.Appendix.Listing8OriginalGraphFailureRun

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphFailure
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (Listing8CopiedOwnerActiveRun.Allowed mode (Listing8OwnerImage.owners mode l v) packet ∨
      packet.address=nodePC mode origin g g.halt ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v)++Listing8OriginalGraphCatalog.catalog mode origin g,
      Outside mode template packet → Intact mode template memory ∧ Decodes mode template memory
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8JointOwnerPointerCatalog.Property mode origin l memory ∧ Certificate mode origin l v g memory
@[expose] def failureForms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8JointOriginalGraphState.forms mode l t (values mode origin g node rule) state++
    Listing8JointFailureCatalog.forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state)
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  failureForms mode origin l t g node rule state++Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)

theorem from_owner (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (owners : Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l v) memory)
    (originals : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,headers⟩:=owners
  refine ⟨packet,Or.inl allowed,?_⟩
  intro template member outside
  rcases List.mem_append.mp member with copied | original
  · exact headers template copied outside
  · exact ⟨originals template original,Listing8OwnerTemplateCollection.decodes mode template memory (originals template original)⟩

theorem from_sentinel (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (owners : All mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v)) memory)
    (originals : Listing8OriginalGraphSentinel.Certificate mode origin g memory) : Certificate mode origin l v g memory := by
  obtain ⟨packet,allowed,headers⟩:=originals
  refine ⟨packet,?_,?_⟩
  · rcases allowed with empty | sentinel
    · exact Or.inl (Or.inl empty)
    · exact Or.inr sentinel
  · intro template member outside
    rcases List.mem_append.mp member with copied | original
    · exact ⟨owners template copied,Listing8OwnerTemplateCollection.decodes mode template memory (owners template copied)⟩
    · exact headers template original outside

theorem limit (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
 :
    Listing8FailureLayout.callPC mode (Listing8FailureCrossCatalogFields.region mode origin l g)+5≤Listing8FullTableImage.start mode origin := by
  have geometry:=Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx
  have atCall : Listing8FailureLayout.callPC mode (Listing8FailureCrossCatalogFields.region mode origin l g)=Listing8JumpLayout.callPC mode origin := geometry.callAt
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  rw [atCall];omega

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have bounds:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body.state
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _
    (StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.2.1)
      (Listing8JointOriginalGraphState.state_main mode origin l t g node rule ctx old state current.body.state global))
    (StringDwordWritesBridge.trace mode (Listing8LoopState.state_trace mode l t _ old bounds state
      current.body.state.head.graph.entry current.body.state.head.graph.forward image))

theorem prefix_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
      (Listing8JointOriginalGraphState.forms mode l t (values mode origin g node rule) state)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have bounds:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  have inputTrace:=StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old bounds state graph.entry graph.forward image)
  have headTrace:=Listing8JointOriginalGraphState.head_trace mode origin l t g node rule ctx old state current.body.state.head
  have stateImage:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body.state
  have stateTrace:=StringDwordWritesBridge.trace mode (Listing8LoopState.state_trace mode l t _ old
    (Listing8LoopGraphState.bounds mode origin l t g node rule ctx) state graph.entry graph.forward stateImage)
  exact StringStack.trace_append mode (StringStack.trace_append mode inputTrace headTrace) stateTrace

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Property mode origin l (values mode origin g node rule) g reached.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureCrossCatalogFields.region mode origin l g) reached.principal.memory)
      (Listing8JointFailureCatalog.forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state))
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have entry:=current.body.state.head.graph.entry
  have forward:=current.body.state.head.graph.forward
  have position:=Listing8LoopState.endpoint mode l t _ old bounds.state state entry forward image.state
  have ready:=Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ bounds state entry forward image
  have originals:=Listing8OriginalGraphFailureRun.whole mode origin g (Listing8FailureCrossCatalogFields.region mode origin l g)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) (limit mode origin l t g node rule ctx) rfl
    _ position ready (initial mode origin l t g node rule ctx old state current global)
  have owners:=StringStoreTemplateRuns.preserve mode (Listing8FailureCrossCatalogFields.Allowed mode origin l g)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8JointFailureCatalog.initial mode origin l t g node rule ctx old state current.body.state)
    (Listing8FailureCrossCatalogFields.store mode origin l t g node rule ctx)
    (Listing8FailureCrossCatalogFields.regions mode origin l t g node rule ctx _ position ready)
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Property mode origin l (values mode origin g node rule) g reached.principal.memory ∧
        Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureCrossCatalogFields.region mode origin l g) reached.principal.memory from
      ⟨⟨all.1.1.1.1,from_sentinel mode origin l _ g reached.principal.memory all.1.2.2.2 all.2⟩,all.1.1.2⟩)
    (JointTemplateStates.join mode _ _ _ _
      (JointTemplateStates.join mode _ _ _ _ (Listing8JointFailureCatalog.main mode origin l t g node rule ctx old state current global) owners) originals)

theorem through_failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (failureForms mode origin l t g node rule state) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  rw [failureForms,StringTemplateStates.append,StringWrites.trace_run_eq mode (prefix_trace mode origin l t g node rule ctx old state current)]
  exact ⟨StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
      show Property mode origin l (values mode origin g node rule) g reached.principal.memory from
      ⟨all.1.1,from_owner mode origin l _ g reached.principal.memory all.1.2 all.2.1⟩)
      (Listing8JointOriginalGraphState.through_state mode origin l t g node rule ctx old state current.body.state global),
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1) (main mode origin l t g node rule ctx old state current global)⟩

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have position:=Listing8LoopState.endpoint mode l t _ old bounds.state state current.body.state.head.graph.entry current.body.state.head.graph.forward image.state
  have ready:=Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ bounds state current.body.state.head.graph.entry current.body.state.head.graph.forward image
  exact Listing8OriginalGraphFailureRun.endpoint mode origin g (Listing8FailureCrossCatalogFields.region mode origin l g)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) (limit mode origin l t g node rule ctx)
    _ position ready (initial mode origin l t g node rule ctx old state current global)

theorem control_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  have position:=Listing8LoopControl.entry mode origin l t g node rule ctx old state current
  have capacity:=Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  have ready:=Listing8LoopControl.current mode origin l t g node rule ctx old state current
  have originals:=StringStoreTemplateRuns.preserve mode (Listing8MainCatalogTransport.Allowed mode origin l)
    (All mode (Listing8OriginalGraphCatalog.catalog mode origin g)) _ _
    (endpoint mode origin l t g node rule ctx old state current global)
    (Listing8OriginalGraphTransport.store mode origin l t g node rule ctx)
    (Listing8ControlStoreFields.regions mode origin l t g node rule ctx _ _ position capacity ready)
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Property mode origin l (values mode origin g node rule) g reached.principal.memory from
      ⟨all.1.1,from_owner mode origin l _ g reached.principal.memory all.1.2 all.2⟩)
    (JointTemplateStates.join mode _ _ _ _ (Listing8JointControlCatalog.main mode origin l t g node rule ctx old state current global) originals)

theorem through_control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (forms mode origin l t g node rule state) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have failureTrace:=StringStack.previous_trace mode (Listing8LoopFailure.failure_trace mode l t _ _ _ old bounds state
    current.body.state.head.graph.entry current.body.state.head.graph.forward image)
  have actual:=StringStack.trace_append mode (prefix_trace mode origin l t g node rule ctx old state current) failureTrace
  change StringStack.Trace mode _ (failureForms mode origin l t g node rule state) _ at actual
  rw [forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨through_failure mode origin l t g node rule ctx old state current global,control_main mode origin l t g node rule ctx old state current global⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (forms mode origin l t g node rule state) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact through_control mode origin l t g node rule ctx old state current initialGlobal

end SmcTuring.Appendix.Listing8JointOriginalGraphFailure
