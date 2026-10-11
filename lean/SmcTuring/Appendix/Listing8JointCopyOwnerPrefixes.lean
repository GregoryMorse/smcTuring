module
public import SmcTuring.Appendix.Listing8CrossMacroCatalog

public section
namespace SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def Catalog (mode : Mode) (origin : Nat) (l : Layout) (state : StringExecution.State mode) : Prop :=
  Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
  StringEncodedTemplates.Decodes mode (nodeParams mode l) state.principal.memory ∧
  StringEncodedTemplates.Decodes mode (transitionParams mode l) state.principal.memory

theorem macro_prefix (mode : Mode) (p : StringMacroLayout.Params)
    (property : StringExecution.State mode → Prop) (state : StringExecution.State mode)
    (before after : List (StringStack.Form mode))
    (cut : (StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode)=before++after)
    (kept : StringTemplateStates.Run mode property
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state) :
    property (StringWrites.run mode
      ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)++before) state) := by
  have arranged : (StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)=
      ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)++before)++
      (after++(StringRestore.forms mode false (StringCodec.bodyEnd mode p.start p.size) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode)++
        (StringRestore.forms mode true (StringRestore.endpoint mode (StringCodec.bodyEnd mode p.start p.size) p.size) (StringCodec.destinationField mode p.start) p.size).map (StringWrites.liftString mode)) := by
    simp only [StringProgram.forms,List.map_append,cut,List.append_assoc]
  exact StringTemplateStates.at_prefix mode _ _ _ state (arranged ▸ kept)

@[expose] def Bound (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (state : StringExecution.State mode) : Prop :=
  (∀ before after : List (StringStack.Form mode),
    (StringMoves.forms mode (StringPlan.widths mode (nodeParams mode l).size)).map (StringWrites.liftString mode)=before++after →
    Listing8CopyOwnerPrefixes.Certificate mode (nodeParams mode l) state (Listing8CopyOwnerPrefixes.nodeTemplates mode l v) before ∧
    Catalog mode origin l (StringWrites.run mode
      ((StringSetup.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination).map (StringWrites.liftString mode)++before) state)) ∧
  (∀ before after : List (StringStack.Form mode),
    (StringMoves.forms mode (StringPlan.widths mode (transitionParams mode l).size)).map (StringWrites.liftString mode)=before++after →
    Listing8CopyOwnerPrefixes.Certificate mode (transitionParams mode l) (Listing8CopyTrace.first mode l state)
      (Listing8CopyOwnerPrefixes.transitionTemplates mode l v) before ∧
    Catalog mode origin l (StringWrites.run mode
      ((StringSetup.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination).map (StringWrites.liftString mode)++before)
      (Listing8CopyTrace.first mode l state)))

/-- Original and completed copied owner headers, exact copied byte counts,
both macro catalogs and global control describe the SAME actual MOVS prefix. -/
theorem pair (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    Bound mode origin l (values mode origin g node rule) state := by
  have owners:=Listing8CopyOwnerPrefixes.pair mode l _ ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current) (Listing8MainCopyImage.rule_current mode l _ _ current) current.node current.rule
  have kept:=Listing8CrossMacroCatalog.pair mode origin l t g node rule ctx state entry forward current initial
  change StringTemplateStates.Run mode (Catalog mode origin l)
    (((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state at kept
  rw [List.map_append,StringTemplateStates.append] at kept
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current)
  have firstRun : StringWrites.run mode
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
        (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
    rw [StringWrites.run_lift_string]
    exact (StringExecution.trace_run mode (StringMacroTrace.trace mode _ state ready)).symm
  rw [firstRun] at kept
  exact ⟨fun before after cut => ⟨owners.1 before after cut,macro_prefix mode _ _ state before after cut kept.1⟩,
    fun before after cut => ⟨owners.2 before after cut,macro_prefix mode _ _ _ before after cut kept.2⟩⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Bound mode origin l (values mode origin g node rule) state := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initial:=Listing8JointMacroControl.initial_property mode origin _ state
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
    Bound mode origin l (values mode origin g node rule) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
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

end SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes
