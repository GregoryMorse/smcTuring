module
public import SmcTuring.Appendix.Listing8JointLocalPrefixFields

public section
namespace SmcTuring.Appendix.Listing8JointLocalPrefixRun
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8JointLocalCatalog
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state.principal.memory :=
  Listing8JointLocalContinuation.from_snapshot mode origin l t g node rule ctx old state state current (fun _ _ => rfl)
    (Listing8InputExecutableTemplates.mask_initial mode l.input old.rule old.tape old.pending old.fresh old.mask
      state.principal.memory current.body.state.head.graph.input)
    (Listing8InputFixedTemplates.mask_initial mode l.input old.rule old.tape old.pending old.fresh old.mask
      state.principal.memory current.body.state.head.graph.input)

theorem copy_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have placed:=Listing8JointLocalPrefixFields.copy_placements mode origin l t g node rule ctx
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current)
  have next:=Listing8LiveCopies.second_ready mode l ctx.resources state ready
    (Listing8MainCopyImage.rule_current mode l _ _ current)
  change StringStoreRegions.Run mode _
    (((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (secondStart mode l) (transitionParams mode l).source
        (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state
  rw [List.map_append,StringStoreRegions.append]
  constructor
  · exact Listing8JointLocalPrefixFields.macro_regions mode l _ _ _ placed.1 _ state (StringMacroTemplateWrites.complete mode _ state ready)
  · have firstRun : StringWrites.run mode
        ((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
          (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
      apply StringWrites.trace_run_eq mode
      have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
          StringWrites.liftString mode := by funext form;rfl
      simpa only [List.map_map,Function.comp_def,Listing8CopyTrace.first,lifting,nodeParams] using
        StringStack.previous_trace mode (StringControl.previous_trace mode
          (StringDword.string_trace mode (StringMacroTrace.trace mode _ _ ready)))
    rw [firstRun]
    exact Listing8JointLocalPrefixFields.macro_regions mode l _ _ _ placed.2 _ _ (StringMacroTemplateWrites.complete mode _ _ next)

theorem retarget_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have placed : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),
      0≤site.owner+2 ∧ site.owner+6≤l.input.start := by
    intro site member
    have upper:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
    change site.owner+10≤codeEnd mode l at upper
    have before:=ctx.resources.inputAfter
    exact ⟨Nat.zero_le _,by omega⟩
  have patches:=StringRetargetWrites.owned mode 0 l.input.start _ (patchStart mode l)
    (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l ctx.resources) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    placed state entry
  have actual:=StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l _ ctx.resources state entry current)
  have fits:=Listing8OwnerImage.source_field_fits mode l ctx.resources
  have write:=StringStoreWrites.located mode (Listing8LiteralInput.sourceField mode l.input) (Listing8LiteralInput.sourceField mode l.input+4)
    (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) (values mode origin g node rule).tape
    (Listing8LiveRetarget.patched mode l state) (Listing8LiveRetarget.patched_pc mode l ctx.resources state entry)
    ctx.fields.tapeReach (by omega) ⟨Nat.le_refl _,Nat.le_refl _⟩
  have last:=StringStoreRegions.bounded_packet mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (Listing8LiteralInput.sourceField mode l.input) _ (Listing8LiveRetarget.patched mode l state) write
    (StringStoreWrites.length mode _ _ _) (Listing8JointLocalPrefixFields.input_fields mode l _ _ _ (Or.inr (Or.inl rfl)))
  rw [Listing8LiveRetarget.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode actual]
  exact ⟨BoundedStoreRegions.interval mode _ _ _ _ state (fun address count _ upper =>
    Listing8JointLocalPrefixFields.exterior mode l _ _ address count (Or.inl upper)) patches,⟨last,trivial⟩⟩

theorem owner_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) :=
  Listing8OwnerStoreRegions.regions mode _ _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8JointLocalPrefixFields.owner_placements mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

theorem pointer_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=Listing8JointLocalPrefixFields.word_fields mode origin l t g node rule ctx
  have first:=CopyStoreRegions.word mode _ (Listing8PointerCopies.word mode l) ctx.copies.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) ctx.copies.wordValid state.principal entry];rfl
  have last:=CopyStoreRegions.sequence mode _ (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t)
    ctx.copies.dwordValid (Listing8JointLocalPrefixFields.dword_fields mode origin l t g node rule ctx) _ next
  rw [Listing8PointerCopies.program,List.map_append,StringStoreRegions.append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

theorem through_retarget_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have mapping : (((Listing8MainCopies.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
      (Listing8MainCopies.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
  have firstRun : StringWrites.run mode ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state=
      Listing8MainCopies.finish mode l state := by
    apply StringWrites.trace_run_eq mode
    have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
        StringWrites.liftString mode := by funext form;rfl
    simpa only [List.map_map,Function.comp_def,lifting] using StringStack.previous_trace mode (StringControl.previous_trace mode
      (StringDword.string_trace mode (Listing8MainCopies.trace mode l _ ctx.resources state entry forward current)))
  rw [Listing8MainRetarget.program,List.map_append,mapping,StringStoreRegions.append,firstRun]
  exact ⟨copy_regions mode origin l t g node rule ctx state entry forward current,
    retarget_regions mode origin l t g node rule ctx _ (Listing8MainCopies.registers mode l _ ctx.resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l _ ctx.resources state entry forward current)⟩

theorem prefix_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have ready:=image.prefixCurrent.copying
  have entry:=current.entry
  have forward:=current.forward
  have first:=through_retarget_regions mode origin l t g node rule ctx state entry forward ready
  have middle:=owner_regions mode origin l t g node rule ctx state entry forward ready
  have firstTrace:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward ready)
  have middleTrace:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward ready)
  rw [Listing8MainPrefix.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode middleTrace]
  refine ⟨?_,pointer_regions mode origin l t g node rule ctx _
    (Listing8MainLiveOwners.registers mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
      ctx.fields.tapeReach state entry forward ready).1⟩
  rw [Listing8MainLiveOwners.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode firstTrace]
  exact ⟨first,middle⟩

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state :=
  StringStoreTemplateRuns.preserve mode _ _ _ state (initial mode origin l t g node rule ctx old state current)
    (store mode l _ _) (prefix_regions mode origin l t g node rule ctx old state current.body.state.head.graph)


end SmcTuring.Appendix.Listing8JointLocalPrefixRun
