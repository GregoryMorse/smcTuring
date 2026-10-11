module
public import SmcTuring.Appendix.Listing8OriginalGraphMacroRun
public import SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes

public section
namespace SmcTuring.Appendix.Listing8JointOriginalGraphCopies
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
@[expose] def Certificate (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,
    (packet.bytes=[] ∨ (packet.address=l.sourceNode ∨ packet.address=l.sourceTransition) ∧ packet.bytes.length=mode.wordBytes) ∧
    ∀ template∈Listing8OriginalGraphCatalog.catalog mode origin g,Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory ∧ Listing8OwnerTemplateCollection.Decodes mode template memory
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (state : StringExecution.State mode) :=
  Listing8JointCopyOwnerPrefixes.Catalog mode origin l state ∧ Certificate mode origin l g state.principal.memory

theorem from_macro (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (p : StringMacroLayout.Params) (memory : ByteMemory.Memory)
    (source : p.source=l.sourceNode ∨ p.source=l.sourceTransition)
    (destinationEarly : p.destination+mode.wordBytes≤Listing8FullTableImage.start mode origin)
    (current : Listing8OriginalGraphMacroRun.Certificate mode origin g p memory) : Certificate mode origin l g memory := by
  obtain ⟨packet,allowed,headers⟩:=current
  rcases allowed with restored | ⟨addresses,size⟩
  · exact ⟨packet,Or.inl restored,headers⟩
  · rcases addresses with src | dst
    · exact ⟨packet,Or.inr ⟨src ▸ source,size⟩,headers⟩
    · refine ⟨⟨0,[]⟩,Or.inl rfl,?_⟩
      intro template member _
      have lower:=Listing8OriginalGraphInputFields.lower mode origin g template member
      apply headers template member
      left;rw [dst,size];exact destinationEarly.trans lower

theorem pair (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (Property mode origin l g)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state current.entry current.forward
    (Listing8MainCopyImage.node_current mode l _ _ image.prefixCurrent.copying)
  have nextReady:=Listing8LiveCopies.second_ready mode l ctx.resources state ready
    (Listing8MainCopyImage.rule_current mode l _ _ image.prefixCurrent.copying)
  have initial:=Listing8OriginalGraphCatalog.from_initial mode origin g _ current.nodes current.rules
  have bounds:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have positions:=coordinates mode l
  have codeEarly : codeEnd mode l≤Listing8FullTableImage.start mode origin := by omega
  have nodeEnd : (nodeParams mode l).destination+(nodeParams mode l).size≤codeEnd mode l := by
    have exactEnd : (nodeParams mode l).destination+(nodeParams mode l).size+transitionSpan mode=codeEnd mode l := rfl
    omega
  have ruleEnd : (transitionParams mode l).destination+(transitionParams mode l).size=codeEnd mode l := rfl
  have nodeWord : mode.wordBytes≤(nodeParams mode l).size := by change mode.wordBytes≤nodeSpan mode;cases mode <;> decide
  have ruleWord : mode.wordBytes≤(transitionParams mode l).size := by change mode.wordBytes≤transitionSpan mode;cases mode <;> decide
  have first:=Listing8OriginalGraphMacroRun.complete mode origin g (nodeParams mode l) state ready (by
      change secondStart mode l≤Listing8FullTableImage.start mode origin;omega) (nodeEnd.trans codeEarly) initial
  have afterFirst:=Listing8OriginalGraphMacroRun.endpoint mode origin g (nodeParams mode l) state ready (nodeEnd.trans codeEarly) initial
  change Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
    (Listing8CopyTrace.first mode l state).principal.memory at afterFirst
  have second:=Listing8OriginalGraphMacroRun.complete mode origin g (transitionParams mode l) _ nextReady (by
      change patchStart mode l≤Listing8FullTableImage.start mode origin;omega) (by rw [ruleEnd];exact codeEarly) afterFirst
  have firstRun : StringWrites.run mode
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
        (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
    rw [StringWrites.run_lift_string]
    exact (StringExecution.trace_run mode (StringMacroTrace.trace mode _ state ready)).symm
  have originals : StringTemplateStates.Run mode (fun reached => Certificate mode origin l g reached.principal.memory)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
    change StringTemplateStates.Run mode _
      (((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
        (StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state
    rw [List.map_append,StringTemplateStates.append,firstRun]
    exact ⟨StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => from_macro mode origin l g _ reached.principal.memory
        (Or.inl rfl) (by omega) headers) first,
      StringTemplateStates.monotone mode _ _ _ _ (fun reached headers => from_macro mode origin l g _ reached.principal.memory
        (Or.inr rfl) (by omega) headers) second⟩
  exact JointTemplateStates.join mode _ _ _ _
    (Listing8CrossMacroCatalog.pair mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying global) originals

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Property mode origin l g)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state current).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state current)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state current) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state current]
      exact ending)
  exact pair mode origin l t g node rule ctx old state current.body.state.head.graph initialGlobal

/-- Existing exact copied-byte/header certificates and the full original graph
certificate describe the same actual MOVS prefixes, with a single common packet. -/
theorem movs_joint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Listing8JointCopyOwnerPrefixes.Bound mode origin l (values mode origin g node rule) state ∧
    (∀ before after : List (StringStack.Form mode),
      (StringMoves.forms mode (StringPlan.widths mode (nodeParams mode l).size)).map (StringWrites.liftString mode)=before++after →
      Property mode origin l g (StringWrites.run mode
        ((StringSetup.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination).map (StringWrites.liftString mode)++before) state)) ∧
    (∀ before after : List (StringStack.Form mode),
      (StringMoves.forms mode (StringPlan.widths mode (transitionParams mode l).size)).map (StringWrites.liftString mode)=before++after →
      Property mode origin l g (StringWrites.run mode
        ((StringSetup.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination).map (StringWrites.liftString mode)++before)
        (Listing8CopyTrace.first mode l state))) := by
  have kept:=maintained mode origin l t g node rule ctx old state current
  have graph:=current.body.state.head.graph
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated graph
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state graph.entry graph.forward
    (Listing8MainCopyImage.node_current mode l _ _ image.prefixCurrent.copying)
  have firstRun : StringWrites.run mode
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
        (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
    rw [StringWrites.run_lift_string]
    exact (StringExecution.trace_run mode (StringMacroTrace.trace mode _ state ready)).symm
  change StringTemplateStates.Run mode (Property mode origin l g)
    (((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state at kept
  rw [List.map_append,StringTemplateStates.append,firstRun] at kept
  exact ⟨Listing8JointCopyOwnerPrefixes.maintained mode origin l t g node rule ctx old state current,
    fun before after cut => Listing8JointCopyOwnerPrefixes.macro_prefix mode _ _ state before after cut kept.1,
    fun before after cut => Listing8JointCopyOwnerPrefixes.macro_prefix mode _ _ _ before after cut kept.2⟩

end SmcTuring.Appendix.Listing8JointOriginalGraphCopies
