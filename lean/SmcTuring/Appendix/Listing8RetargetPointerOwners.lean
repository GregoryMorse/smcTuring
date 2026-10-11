module
public import SmcTuring.Appendix.Listing8MainCatalogTransport
public import SmcTuring.Appendix.Listing8JointMainMacroCatalog

public section
namespace SmcTuring.Appendix.Listing8RetargetPointerOwners
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringTemplateStates.Run
@[expose] def templates (mode : Mode) (l : Layout) : List (Template mode) :=
  [.pointer (backEntry mode l.sourceNode) (backEntry mode l.sourceNode),
   .pointer (backEntry mode l.sourceNode) (backEntry mode (nodeParams mode l).destination),
   .pointer (forwardEntry mode l.sourceNode) (forwardEntry mode l.sourceNode),
   .pointer (forwardEntry mode l.sourceNode) (forwardEntry mode (nodeParams mode l).destination),
   .pointer l.sourceTransition l.sourceTransition,
   .pointer l.sourceTransition (transitionParams mode l).destination,
   .pointer (stateEntry mode l.sourceTransition) (stateEntry mode l.sourceTransition),
   .pointer (stateEntry mode l.sourceTransition) (stateEntry mode (transitionParams mode l).destination)]

theorem catalog_member (mode : Mode) (l : Layout) (v : Values mode) (template : Template mode)
    (member : template∈templates mode l) :
    template∈Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v) := by
  simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries]

theorem initial (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    All mode (templates mode l) (Listing8MainCopies.finish mode l state).principal.memory := by
  have originals:=Listing8MainCopies.source_packets mode l v resources state entry forward current
  simp only [sourceNodeBytes,sourceTransitionBytes] at originals
  have copied:=Listing8MainCopies.copied_packets mode l v resources state entry forward current
  have nodeOriginal:=Listing8OwnerImage.node_windows mode l.sourceNode l.sourceNode v.tape v.back v.forward _ (by simpa only [node_length] using originals.1)
  have nodeCopied:=Listing8OwnerImage.node_windows mode l.sourceNode (nodeParams mode l).destination v.tape v.back v.forward _ copied.1
  have ruleOriginal:=Listing8OwnerImage.transition_windows mode l.sourceTransition l.sourceTransition v.next v.newState v.rule v.fresh v.direction _ (by simpa only [transition_length] using originals.2)
  have ruleCopied:=Listing8OwnerImage.transition_windows mode l.sourceTransition (transitionParams mode l).destination v.next v.newState v.rule v.fresh v.direction _ copied.2
  intro template member
  simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Listing8PointerTemplate.initial mode _ _ v.back _ nodeOriginal.1
  · exact Listing8PointerTemplate.initial mode _ _ v.back _ nodeCopied.1
  · exact Listing8PointerTemplate.initial mode _ _ v.forward _ nodeOriginal.2
  · exact Listing8PointerTemplate.initial mode _ _ v.forward _ nodeCopied.2
  · exact Listing8PointerTemplate.initial mode _ _ v.next _ ruleOriginal.1
  · exact Listing8PointerTemplate.initial mode _ _ v.next _ ruleCopied.1
  · exact Listing8PointerTemplate.initial mode _ _ v.newState _ ruleOriginal.2
  · exact Listing8PointerTemplate.initial mode _ _ v.newState _ ruleCopied.2

theorem patch_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (site : Listing8ModeOffsets.Site) (inside : site∈Listing8ModeOffsets.sites mode (patchLayout mode l)) :
    Listing8OwnerPointerFrames.CompatibleAll mode (templates mode l) (site.owner+2) 4 := by
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have bounds:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site inside
  change patchStart mode l+40≤site.owner ∧ site.owner+10≤codeEnd mode l ∧ _ at bounds
  intro template member
  cases mode <;> simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8ModeOffsets.sites,List.mem_cons,List.not_mem_nil,or_false] at inside
  all_goals rcases inside with rfl | rfl | rfl | rfl
  all_goals simp only [Listing8OwnerPointerFrames.Compatible,start,span,field,width,pointerField,
    nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
    backEntry,forwardEntry,stateEntry,currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan,pointerSpan,
    ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes] at bounds ⊢
  all_goals omega

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8OwnerPointerFrames.CompatibleAll mode (templates mode l))
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have valid:=Listing8ModeOffsets.valid mode (patchLayout mode l) (block_capacity mode l ctx.resources)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l))
  have patches:=Listing8RetargetExecutableTemplates.owned mode (Listing8ModeOffsets.sites mode (patchLayout mode l))
    (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l)) valid
    (Listing8OwnerPointerFrames.CompatibleAll mode (templates mode l))
    (patch_fields mode origin l t g node rule ctx) state.principal entry
  have first:=StringStoreRegions.mixed mode _ _ _ patches
  have trace:=StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l _ ctx.resources state entry current)
  have fields:=Listing8OwnerImage.source_field_bounds mode l
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have after:=ctx.resources.inputAfter
  change codeEnd mode l≤l.input.start at after
  have fits:=Listing8OwnerImage.source_field_fits mode l ctx.resources
  have tape:=StringStoreWrites.located mode (Listing8LiteralInput.sourceField mode l.input) (Listing8LiteralInput.sourceField mode l.input+4)
    (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) (values mode origin g node rule).tape _
    (Listing8LiveRetarget.patched_pc mode l ctx.resources state entry) ctx.fields.tapeReach fits ⟨Nat.le_refl _,by omega⟩
  rw [Listing8LiveRetarget.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  constructor
  · simpa only [Listing8InputRetargetTemplateBindings.retarget_forms] using first
  · exact BoundedStoreRegions.interval mode _ _ _ _ _ (fun address count lower upper template member =>
      Listing8MainCatalogTransport.owners mode origin l t g node rule ctx address count
        (Or.inr (Or.inl ⟨by omega,by omega⟩)) template (catalog_member mode l _ template member)) ⟨tape,trivial⟩

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (templates mode l) reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) (Listing8MainCopies.finish mode l state) :=
  StringStoreTemplateRuns.preserve mode (Listing8OwnerPointerFrames.CompatibleAll mode (templates mode l))
    (All mode (templates mode l)) _ _ (initial mode l _ ctx.resources state entry forward current)
    (Listing8OwnerPointerFrames.store mode (templates mode l))
    (regions mode origin l t g node rule ctx _ (Listing8MainCopies.registers mode l _ ctx.resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l _ ctx.resources state entry forward current))

end SmcTuring.Appendix.Listing8RetargetPointerOwners
