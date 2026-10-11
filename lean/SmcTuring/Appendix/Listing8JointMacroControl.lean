module
public import SmcTuring.Appendix.Listing8MacroTemplateTransfers
public import SmcTuring.Appendix.Listing8GlobalMainControlTemplates
public import SmcTuring.Appendix.Listing8GlobalOriginalPrefix
public import SmcTuring.Appendix.Listing8GlobalInitialControl
public import SmcTuring.Appendix.Listing8GlobalControlProperties
public import SmcTuring.Appendix.Listing4EntrySlotRegions

public section
namespace SmcTuring.Appendix.Listing8JointMacroControl
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- Exact reversible frames recover the catalog at the actual entry. -/
theorem initial_property (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode)
    (regions : StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin) forms state)
    (ending : Listing8GlobalControlTemplates.Property mode origin (StringWrites.run mode forms state).principal.memory) :
    Listing8GlobalControlTemplates.Property mode origin state.principal.memory :=
  StringTemplateStates.at_prefix mode _ [] forms state
    (Listing8GlobalControlReconstruction.all_states mode origin forms state regions ending)

@[expose] def Joint (mode : Mode) (origin : Nat) (p : StringMacroLayout.Params) (state : StringExecution.State mode) : Prop :=
  StringTemplateStates.Run mode (fun reached =>
    Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
    StringEncodedTemplates.Decodes mode p reached.principal.memory)
    ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state

/-- Both macro certificates include all initializer/save/MOVS/cursor-restore
boundaries and share the actual first macro's restored continuation state. -/
theorem pair (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    Joint mode origin (nodeParams mode l) state ∧
    Joint mode origin (transitionParams mode l) (Listing8CopyTrace.first mode l state) := by
  have localBoth:=Listing8MacroTemplateTransfers.live mode l _ ctx.resources state entry forward current
  have globalBoth:=Listing8GlobalControlTemplates.all_decodes mode origin _ state initial
    (Listing8GlobalCopyRegions.regions mode origin l t g node rule ctx state entry forward current)
  change StringTemplateStates.Run mode _
    (((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state at globalBoth
  rw [List.map_append,StringTemplateStates.append] at globalBoth
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current)
  have firstRun : StringWrites.run mode
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
        (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
    rw [StringWrites.run_lift_string]
    exact (StringExecution.trace_run mode (StringMacroTrace.trace mode _ state ready)).symm
  rw [firstRun] at globalBoth
  exact ⟨JointTemplateStates.join mode _ _ _ _ globalBoth.1 localBoth.1.2.2,
    JointTemplateStates.join mode _ _ _ _ globalBoth.2 localBoth.2.2.2⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Joint mode origin (nodeParams mode l) state ∧
    Joint mode origin (transitionParams mode l) (Listing8CopyTrace.first mode l state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initial:=initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  exact pair mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
    current.state.head.input.prefixCurrent.copying initial

/-- One original emitted image and actual bootstrap supply both joint macro
certificates, without a future packet, image, readiness or trace premise. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Joint mode origin (nodeParams mode l) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) ∧
    Joint mode origin (transitionParams mode l)
      (Listing8CopyTrace.first mode l (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) := by
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
  apply pair mode origin l t g node rule ctx _ _ _
    (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed) readyGlobal
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

end SmcTuring.Appendix.Listing8JointMacroControl
