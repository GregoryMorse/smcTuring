module
public import SmcTuring.Native.StringMacroCrossTemplates
public import SmcTuring.Appendix.Listing8JointMacroControl

public section
namespace SmcTuring.Appendix.Listing8CrossMacroCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- Both code intervals and every complete original-source/copied-buffer
envelope are separate from the other macro's executable interval. -/
theorem separation (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    StringMacroCrossTemplates.Separate mode (nodeParams mode l) (transitionParams mode l) ∧
    StringMacroCrossTemplates.Separate mode (transitionParams mode l) (nodeParams mode l) := by
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have coords:=coordinates mode l
  have first:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  have second:=endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change l.start≤secondStart mode l at first
  change secondStart mode l≤patchStart mode l at second
  have nodeAfter : patchStart mode l≤(nodeParams mode l).destination := by
    dsimp [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout];omega
  have ruleAfter : patchStart mode l≤(transitionParams mode l).destination := by
    dsimp [transitionParams,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,patchLayout];omega
  constructor
  · refine ⟨Or.inl (Nat.le_refl _),Or.inr ?_,Or.inr nodeAfter⟩
    change patchStart mode l≤l.sourceNode
    omega
  · refine ⟨Or.inr (Nat.le_refl _),Or.inr ?_,Or.inr ?_⟩
    · change secondStart mode l≤l.sourceTransition;omega
    · change secondStart mode l≤(transitionParams mode l).destination;omega

/-- Throughout both complete actual copies, BOTH macro catalogs and global
control decode at each same reached prefix, including all restore stores. -/
theorem pair (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have separated:=separation mode origin l t g node rule ctx
  have localBoth:=Listing8MacroTemplateTransfers.live mode l _ ctx.resources state entry forward current
  have joint:=Listing8JointMacroControl.pair mode origin l t g node rule ctx state entry forward current initial
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current)
  have firstRun : StringWrites.run mode
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
        (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
    rw [StringWrites.run_lift_string]
    exact (StringExecution.trace_run mode (StringMacroTrace.trace mode _ state ready)).symm
  have secondThroughout:=StringMacroCrossTemplates.all_decodes mode _ _ separated.1 ctx.resources.transition.sizeFits _ state
    (StringMacroTemplates.initial mode _ _ (Listing8MainCopyImage.rule_current mode l _ _ current)) localBoth.1.1
  have firstEnding:=StringTemplateStates.at_prefix mode _ _ [] state
    (by simpa only [List.append_nil] using localBoth.1.2.1)
  rw [firstRun] at firstEnding
  have firstThroughout:=StringMacroCrossTemplates.all_decodes mode _ _ separated.2 ctx.resources.node.sizeFits _ _ firstEnding localBoth.2.1
  change StringTemplateStates.Run mode _
    (((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state
  rw [List.map_append,StringTemplateStates.append,firstRun]
  constructor
  · exact StringTemplateStates.monotone mode _ _ _ state (fun _ kept => ⟨kept.1.1,kept.1.2,kept.2⟩)
      (JointTemplateStates.join mode _ _ _ state joint.1 secondThroughout)
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => ⟨kept.1.1,kept.2,kept.1.2⟩)
      (JointTemplateStates.join mode _ _ _ _ joint.2 firstThroughout)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
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
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
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

end SmcTuring.Appendix.Listing8CrossMacroCatalog
