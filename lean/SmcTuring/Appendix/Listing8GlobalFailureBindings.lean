module
public import SmcTuring.Appendix.Listing8GlobalFailureRegions
public import SmcTuring.Appendix.Listing8GlobalControlReconstruction
public import SmcTuring.Appendix.Listing8GlobalControlBindings

public section
namespace SmcTuring.Appendix.Listing8GlobalFailureBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The helper reconstructs earlier protected bytes from an independently
proved endpoint. The graph wrappers below construct that endpoint catalog. -/
theorem catalog (mode : Mode) (origin : Nat) (l : Listing8FailureLayout.Layout)
    (geometry : Listing8GlobalFailureRegions.Geometry mode origin l) (bounds : Listing8FailureBounds.Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory)
    (ending : Listing8GlobalControlLayout.Current mode origin (Listing8FailureImage.finish mode l state).principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode l reached.principal.memory)
      ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state := by
  have regions:=Listing8GlobalFailureRegions.regions mode origin l geometry bounds state entry current
  have kept:=Listing8GlobalControlReconstruction.all_states mode origin _ state regions (by
    rw [StringWrites.trace_run_eq mode (StringStack.previous_trace mode (Listing8FailureReuseEffects.trace mode l bounds state entry current))]
    exact Listing8GlobalControlTemplates.initial mode origin _ ending)
  have initial:=StringTemplateStates.at_prefix mode _ [] ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state
    (by simpa only [List.nil_append] using kept)
  have after : Listing8FailureLayout.callPC mode l+5≤l.sentinel := by
    have ordering:=Listing8GlobalControlLayout.ordered mode origin
    have later:=geometry.sentinelLater
    rw [geometry.callAt]
    omega
  exact JointTemplateStates.join mode _ _ _ state
    (StringTemplateStates.monotone mode _ _ _ state (fun reached intact => Listing8GlobalControlTemplates.decodes mode origin _ intact) kept)
    (Listing8FailureExecutableTemplates.all_decodes mode l bounds (Or.inr after) state entry current
      (by rw [geometry.callAt];exact initial.2.1))

theorem original_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (limit : Nat)
    (tail : Listing8FailLayout.Bounds mode origin l limit) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    let extra:=Listing8GlobalBoot.extra mode origin (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory))
    let reached:=Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) extra (Listing8GlobalBoot.bodySeed mode origin seed)
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode region state.principal.memory)
      ((Listing8FailureTrace.program mode region reached).map StringStack.Form.previous) reached := by
  dsimp only
  apply catalog mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
    _ (Listing8GlobalFailure.entry mode l t _ _ _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
      ctx.copies ctx.body _ _)
    (Listing8FailureReuseImage.from_initial mode _ _ (Listing8FailureGlobalImage.current_region mode l t _ _ _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.body _ _))
  exact Listing8GlobalControlBindings.original_current mode origin l t _ _ limit ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body tail memory seed

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    let reached:=Listing8GraphNextState.finish mode origin l t g node rule target memory seed
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode region state.principal.memory)
      ((Listing8FailureTrace.program mode region reached).map StringStack.Form.previous) reached := by
  dsimp only
  exact catalog mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GlobalControlBindings.selected_current mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    let reached:=Listing8LoopState.finish mode l t (values mode origin g node rule) state
    StringTemplateStates.Run mode (fun machine => Listing8GlobalControlTemplates.Decodes mode origin machine.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode region machine.principal.memory)
      ((Listing8FailureTrace.program mode region reached).map StringStack.Form.previous) reached := by
  dsimp only
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  exact catalog mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8LoopState.endpoint mode l t _ old b.state state entry forward current.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ b state entry forward current)
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)

end SmcTuring.Appendix.Listing8GlobalFailureBindings
