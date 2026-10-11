module
public import SmcTuring.Appendix.Listing8JointLocalCatalog

public section
namespace SmcTuring.Appendix.Listing8JointLocalContinuation
open Native Listing8CopyImage Listing8SourceGraph Listing8JointLocalCatalog
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem head_tail_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8DirectionLayout.selectionEnd mode (head mode l))) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8HeadTailTrace.program mode (head mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  let layout:=head mode l
  let owns:=Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have bounds:=Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head
  have first:=DwordXorRegionRuns.sequence mode owns (Listing8HeadTailBounds.xorLayouts mode layout)
    (Listing8DirectionLayout.selectionEnd mode layout) (Listing8HeadTailBounds.xor_chain mode layout)
    (Listing8HeadTailBounds.xor_valid mode layout bounds) (head_xors mode origin l t g node rule ctx) state entry
  have fields:=head_packets mode origin l t g node rule ctx
  have middle:=DwordXorRegionRuns.packets mode owns (Listing8DirectionLayout.masks mode layout)
    (Listing8DirectionLayout.maskPC mode layout) (Listing8HeadTailBounds.masks_chain mode layout)
    (fun site member => Listing8HeadTailBounds.packets_valid mode layout bounds site (List.mem_append_left _ member))
    (fun site member => fields site (by simp only [Listing8DirectionTemplateFields.sites,List.mem_append];exact Or.inl (Or.inr member)))
    (Listing8HeadTailTrace.xorFinish mode layout state) (Listing8HeadTailTrace.xor_endpoint mode layout bounds state entry)
  have last:=DwordXorRegionRuns.packets mode owns (Listing8DirectionLayout.heads mode layout)
    (Listing8DirectionLayout.directionPC mode layout) (Listing8HeadTailBounds.heads_chain mode layout)
    (fun site member => Listing8HeadTailBounds.packets_valid mode layout bounds site (List.mem_append_right _ member))
    (fun site member => fields site (by simp only [Listing8DirectionTemplateFields.sites,List.mem_append];exact Or.inr member))
    (Listing8HeadTailTrace.maskFinish mode layout state) (Listing8HeadTailTrace.mask_endpoint mode layout bounds state entry)
  rw [Listing8HeadTailTrace.program,List.map_append,List.map_append,StringStoreRegions.append,
    StringStoreRegions.append,StringWrites.run_append,DwordXorWrites.sequence_run]
  unfold Listing8HeadTailTrace.xorFinish
  rw [DwordPacketWrites.run]
  simpa only [Listing8HeadTailTrace.maskFinish,Listing8HeadTailTrace.xorFinish] using And.intro (And.intro first middle) last

theorem head_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (head mode l).start) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8WholeHeadTemplates.program mode (head mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  let layout:=head mode l
  let owns:=Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have first:=CopyStoreRegions.sequence mode owns (Listing8DirectionLayout.helpers mode layout) layout.start
    (Listing8DirectionLayout.helper_chain mode layout) (Listing8DirectionBounds.helper_valid mode layout ctx.body.state.head.capacity)
    (head_helpers mode origin l t g node rule ctx) state entry
  have fields:=head_packets mode origin l t g node rule ctx
  have second:=DwordXorRegionRuns.packets mode owns (Listing8DirectionLayout.arithmetic mode layout)
    (Listing8DirectionLayout.backPC mode layout) (Listing8DirectionLayout.arithmetic_chain mode layout)
    (Listing8DirectionBounds.arithmetic_valid mode layout ctx.body.state.head.capacity)
    (fun site member => fields site (by simp only [Listing8DirectionTemplateFields.sites,List.mem_append];exact Or.inl (Or.inl member)))
    (Listing8DirectionTrace.helperFinish mode layout state)
    (Listing8DirectionTrace.helper_endpoint mode layout ctx.body.state.head.capacity state entry)
  have direction : StringStoreRegions.Run mode owns
      ((Listing8DirectionTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
    rw [Listing8DirectionTrace.program,List.map_append,StringStoreRegions.append,StringDwordRuns.run]
    exact ⟨first,second⟩
  have actual : StringWrites.run mode ((Listing8DirectionTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state=
      Listing8DirectionTrace.finish mode layout state := by
    rw [Listing8DirectionTrace.program,List.map_append,StringWrites.run_append,StringDwordRuns.run]
    unfold Listing8DirectionTrace.helperFinish
    rw [DwordPacketWrites.run];rfl
  rw [Listing8WholeHeadTemplates.program,List.map_append,StringStoreRegions.append,actual]
  exact ⟨direction,head_tail_regions mode origin l t g node rule ctx _
    (Listing8DirectionTrace.endpoint mode layout ctx.body.state.head.capacity state entry)⟩

theorem state_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (transition mode l).start) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8StateTrace.program mode (transition mode l) state).map (StringStoreWrites.liftDword mode)) state := by
  let layout:=transition mode l
  let owns:=Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have bounds:=Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state
  have first:=CopyStoreRegions.sequence mode owns (Listing8StateLayout.helpers mode layout) layout.start
    (Listing8StateLayout.helper_chain mode layout) (Listing8StateBounds.helper_valid mode layout bounds)
    (state_helpers mode origin l t g node rule ctx) state entry
  have last:=DwordXorRegionRuns.packets mode owns (Listing8StateLayout.packets mode layout)
    (Listing8StateLayout.newPC mode layout) (Listing8StateLayout.packet_chain mode layout)
    (Listing8StateBounds.packet_valid mode layout bounds) (state_packets mode origin l t g node rule ctx)
    (Listing8StateTrace.helperFinish mode layout state) (Listing8StateTrace.helper_endpoint mode layout bounds state entry)
  rw [Listing8StateTrace.program,List.map_append,StringStoreRegions.append,StringDwordRuns.run]
  exact ⟨first,last⟩

theorem failure_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat)
    (allowed : Listing8FailureStoreRegions.Allowed mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) address count) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address count := by
  let layout:=failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have cursor:=Listing8PointerCopies.cursor_before mode l
  change layout.cursor+mode.wordBytes≤codeEnd mode l at cursor
  have before:=ctx.resources.inputAfter
  have order:=ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have geometry:=Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx
  have slots:=Listing8GlobalControlLayout.ordered mode origin
  have sentinel : Listing8FailureLayout.callPC mode layout+5≤layout.sentinel := by
    have later:=geometry.sentinelLater
    change Listing8FullTableImage.start mode origin≤layout.sentinel at later
    have atCall:=geometry.callAt
    change Listing8FailureLayout.callPC mode layout=Listing8JumpLayout.callPC mode origin at atCall
    omega
  simp only [Listing8FailureStoreRegions.Allowed,Listing8FailureStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply exterior
    · exact Or.inl (cursor.trans before)
    · exact Or.inl ((cursor.trans before).trans (order.1.trans (order.2.1.trans order.2.2.1)))
  · apply exterior
    · right
      cases mode <;> simp [Listing8FailureLayout.source,StringInit.field,StringCodec.fieldOffset,Listing8FailureLayout.ownerPC] <;> omega
    · exact Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩))
  · apply exterior
    · right;unfold Listing8FailureLayout.mask Listing8FailureLayout.xorPC Listing8FailureLayout.andPC Listing8FailureLayout.storePC Listing8FailureLayout.notPC Listing8FailureLayout.comparisonPC Listing8FailureLayout.ownerPC;omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _,by omega⟩)))
  · apply exterior
    · right;unfold Listing8FailureLayout.andPC Listing8FailureLayout.storePC Listing8FailureLayout.notPC Listing8FailureLayout.comparisonPC Listing8FailureLayout.ownerPC;omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _,by omega⟩))))
  · apply exterior
    · right
      change layout.start≤Listing8FailureLayout.callPC mode layout+1
      unfold Listing8FailureLayout.callPC Listing8FailureLayout.endPC Listing8FailureLayout.xorPC Listing8FailureLayout.andPC Listing8FailureLayout.storePC Listing8FailureLayout.notPC Listing8FailureLayout.comparisonPC Listing8FailureLayout.ownerPC
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_refl _,by omega⟩))))
  · apply exterior
    · right;exact order.2.2.2.trans sentinel
    · exact Or.inr (Or.inl sentinel)

theorem failure_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start)
    (current : Listing8FailureReuseImage.Current mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) state.principal.memory) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8FailureTrace.program mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) state).map StringStack.Form.previous) state :=
  BoundedStoreRegions.monotone mode _ _ _ state (failure_fields mode origin l t g node rule ctx)
    (Listing8FailureStoreRegions.regions mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) state entry current)

theorem from_snapshot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state reached : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (snapshot : Listing8InactiveLocalCatalog.Snapshot mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      state.principal.memory reached.principal.memory)
    (input : DwordTemplateCollection.All (Listing8InputExecutableTemplates.templates mode l.input) reached.principal.memory)
    (fixed : MixedFixedTemplates.All mode (Listing8InputFixedTemplates.entries mode l.input) reached.principal.memory) :
    Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory := by
  have known:=Listing8InactiveLocalInput.from_snapshot mode origin l t g node rule ctx old state reached current snapshot
  let layout:=failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have reuse:=Listing8FailureReuseTransport.current mode layout state.principal.memory reached.principal.memory current.body.failure
    (fun observed count lower upper => snapshot (observed,count) (Or.inr (Or.inr ⟨lower,by
      have endBefore : Listing8FailureLayout.endPC mode layout≤Listing8FailureLayout.callPC mode layout+5 := by
        unfold Listing8FailureLayout.callPC;omega
      exact upper.trans endBefore⟩)))
  have callAt:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode layout=Listing8JumpLayout.callPC mode origin at callAt
  have original : RelativeCallTemplate.Intact (Listing8FailureLayout.callPC mode layout) state.principal.memory := by
    rw [callAt]
    exact RelativeCallTemplate.initial mode _ _ state.principal.memory current.callImage
  have lower : layout.start≤Listing8FailureLayout.callPC mode layout := by
    unfold Listing8FailureLayout.callPC Listing8FailureLayout.endPC Listing8FailureLayout.xorPC Listing8FailureLayout.andPC Listing8FailureLayout.storePC Listing8FailureLayout.notPC Listing8FailureLayout.comparisonPC Listing8FailureLayout.ownerPC
    omega
  have callHeader : RelativeCallTemplate.Intact (Listing8FailureLayout.callPC mode layout) reached.principal.memory :=
    (snapshot (Listing8FailureLayout.callPC mode layout,1) (Or.inr (Or.inr ⟨lower,by
      change Listing8FailureLayout.callPC mode layout+1≤Listing8FailureLayout.callPC mode layout+5
      omega⟩))).trans original
  exact ⟨input,fixed,known.1.1,known.1.2.1,known.1.2.2,known.2.1.1,known.2.1.2,
    Listing8FailureExecutableTemplates.initial mode layout reached.principal.memory reuse callHeader⟩

theorem input_templates (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      DwordTemplateCollection.All (Listing8InputExecutableTemplates.templates mode l.input) reached.principal.memory ∧
      MixedFixedTemplates.All mode (Listing8InputFixedTemplates.entries mode l.input) reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  have arithmetic:=Listing8InputExecutableTemplates.mask_templates mode l.input _ _ old.pending _ old.mask ctx.resources.inputFits
    (Listing8InputBounds.masks mode l bounds.input.prefixBounds.fields)
    (Listing8InputBounds.update mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources)
    (Listing8InputBounds.outside mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources) _
    (Listing8MainPrefix.entry mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    (Listing8MainInputImage.current mode l t _ old bounds.input state current.entry current.forward image)
    (Listing8MainPrefixFrames.head_cursor mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
  have fixed:=Listing8InputFixedTemplates.all_states mode l.input _ _ old.pending _ old.mask ctx.resources.inputFits
    (Listing8InputBounds.masks mode l bounds.input.prefixBounds.fields)
    (Listing8InputBounds.update mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources)
    (Listing8InputBounds.outside mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources) _
    (Listing8MainPrefix.entry mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    (Listing8MainInputImage.current mode l t _ old bounds.input state current.entry current.forward image)
    (Listing8MainPrefixFrames.head_cursor mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
  exact JointTemplateStates.join mode _ _ _ _ arithmetic fixed

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => from_snapshot mode origin l t g node rule ctx old state reached current all.1 all.2.1 all.2.2)
    (JointTemplateStates.join mode _ _ _ _
      (Listing8InactiveLocalInput.snapshots mode origin l t g node rule ctx old state current)
      (input_templates mode origin l t g node rule ctx old state current.body.state.head.graph))

theorem input_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  exact StringDwordWritesBridge.trace mode (Listing8MainInput.input_trace mode l t _ old bounds state current.entry current.forward image)

theorem through_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointInputCatalog.forms mode l (values mode origin g node rule)++
        Listing8JointHeadCatalog.forms mode l (Listing8MainInput.finish mode l t (values mode origin g node rule) state))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=input_trace mode origin l t g node rule ctx old state current.body.state.head.graph
  have leading:=input mode origin l t g node rule ctx old state current
  have seed:=Listing8InputCatalogInitial.endpoint mode _ _ _ _ leading actual
  have b:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body.state.head
  have entry:=Listing8MainInput.endpoint mode l t _ old b.input state current.body.state.head.graph.entry current.body.state.head.graph.forward image.input
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,StringStoreTemplateRuns.preserve mode _ _ _ _ seed (store mode l _ _)
    (head_regions mode origin l t g node rule ctx _ entry)⟩

theorem through_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointOriginalGraphState.forms mode l t (values mode origin g node rule) state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=StringStack.trace_append mode (input_trace mode origin l t g node rule ctx old state current.body.state.head.graph)
    (Listing8JointOriginalGraphState.head_trace mode origin l t g node rule ctx old state current.body.state.head)
  have leading:=through_head mode origin l t g node rule ctx old state current
  have seed:=Listing8InputCatalogInitial.endpoint mode _ _ _ _ leading actual
  have b:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body.state
  have entry:=Listing8LoopHead.endpoint mode l t _ old b.head state current.body.state.head.graph.entry current.body.state.head.graph.forward image.head
  rw [Listing8JointOriginalGraphState.forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,StringStoreTemplateRuns.preserve mode _ _ _ _ seed (store mode l _ _)
    (state_regions mode origin l t g node rule ctx _ entry)⟩


theorem through_failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointOriginalGraphFailure.failureForms mode origin l t g node rule state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have actual:=Listing8JointOriginalGraphFailure.prefix_trace mode origin l t g node rule ctx old state current
  have leading:=through_state mode origin l t g node rule ctx old state current
  have seed:=Listing8InputCatalogInitial.endpoint mode _ _ _ _ leading actual
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have entry:=current.body.state.head.graph.entry
  have forward:=current.body.state.head.graph.forward
  have position:=Listing8LoopState.endpoint mode l t _ old b.state state entry forward image.state
  have ready:=Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ b state entry forward image
  rw [Listing8JointOriginalGraphFailure.failureForms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,StringStoreTemplateRuns.preserve mode _ _ _ _ seed (store mode l _ _)
    (failure_regions mode origin l t g node rule ctx _ position ready)⟩

theorem control_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (slots : Listing4StackTemplates.Slots mode origin address count) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address count := by
  have before:=Listing8ControlStoreFields.slot_bound mode origin l t g node rule ctx address count slots
  have placement:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have inputBefore : address+count≤l.input.start := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at placement <;> omega
  have order:=ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  exact exterior mode l _ _ address count (Or.inl inputBefore)
    (Or.inl (inputBefore.trans (order.1.trans (order.2.1.trans order.2.2.1))))

theorem through_control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      (Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have ending:=StringStack.previous_trace mode (Listing8LoopFailure.failure_trace mode l t _ _ _ old b state
    current.body.state.head.graph.entry current.body.state.head.graph.forward image)
  have actual:=StringStack.trace_append mode
    (Listing8JointOriginalGraphFailure.prefix_trace mode origin l t g node rule ctx old state current) ending
  change StringStack.Trace mode _ (Listing8JointOriginalGraphFailure.failureForms mode origin l t g node rule state) _ at actual
  have leading:=through_failure mode origin l t g node rule ctx old state current
  have seed:=Listing8InputCatalogInitial.endpoint mode _ _ _ _ leading actual
  have position:=Listing8LoopControl.entry mode origin l t g node rule ctx old state current
  have capacity:=Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  have ready:=Listing8LoopControl.current mode origin l t g node rule ctx old state current
  have regions:=BoundedStoreRegions.monotone mode _ _ _ _ (control_fields mode origin l t g node rule ctx)
    (Listing8JumpSlotRegions.complete mode origin _ _ position capacity ready)
  rw [Listing8JointOriginalGraphFailure.forms,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,StringStoreTemplateRuns.preserve mode _ _ _ _ seed (store mode l _ _) regions⟩

/-- The same prefix has every fixed local executable and one shared exact
original/copied owner packet. Existing restoration certificates are retained. -/
@[expose] def Joint (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) : Prop :=
  Listing8JointOriginalGraphFailure.Property mode origin l v g memory ∧
  Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  Listing8JointInputCatalog.Local mode l v memory

theorem all_decodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      Listing8JointInputCatalog.Local mode l (values mode origin g node rule) reached.principal.memory)
      (Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  StringTemplateStates.monotone mode _ _ _ _ (fun reached known => ⟨known,decodes mode l _ _ reached.principal.memory known,
      input_windows mode l (values mode origin g node rule) _ _ reached.principal.memory known⟩)
    (through_control mode origin l t g node rule ctx old state current)

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Joint mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  JointTemplateStates.join mode _ _ _ _
    (Listing8JointOriginalGraphFailure.through_control mode origin l t g node rule ctx old state current global)
    (all_decodes mode origin l t g node rule ctx old state current)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Joint mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) :=
  JointTemplateStates.join mode _ _ _ _
    (Listing8JointOriginalGraphFailure.maintained mode origin l t g node rule ctx old state current)
    (all_decodes mode origin l t g node rule ctx old state current)


theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
      (Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state)
      (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have ending:=StringStack.previous_trace mode (Listing8LoopFailure.failure_trace mode l t _ _ _ old b state
    current.body.state.head.graph.entry current.body.state.head.graph.forward image)
  have actual:=StringStack.trace_append mode
    (Listing8JointOriginalGraphFailure.prefix_trace mode origin l t g node rule ctx old state current) ending
  change StringStack.Trace mode _ (Listing8JointOriginalGraphFailure.failureForms mode origin l t g node rule state) _ at actual
  exact StringStack.trace_append mode actual (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state current)

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Joint mode origin l (values mode origin g node rule) g (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory :=
  Listing8InputCatalogInitial.endpoint mode _ _ _ _ (maintained mode origin l t g node rule ctx old state current)
    (trace mode origin l t g node rule ctx old state current)

theorem at_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (before after : List (StringStack.Form mode))
    (cut : Listing8JointOriginalGraphFailure.forms mode origin l t g node rule state=before++after) :
    Joint mode origin l (values mode origin g node rule) g
      (StringWrites.run mode before (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)).principal.memory := by
  have all:=maintained mode origin l t g node rule ctx old state current
  rw [cut] at all
  exact StringTemplateStates.at_prefix mode _ before after _ all


end SmcTuring.Appendix.Listing8JointLocalContinuation
