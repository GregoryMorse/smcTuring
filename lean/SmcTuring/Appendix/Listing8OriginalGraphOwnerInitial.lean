module
public import SmcTuring.Appendix.Listing8JointOriginalGraphFailure

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8MainRetarget.finish mode l (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  have copy:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have nodeEnd : (nodeParams mode l).destination+nodeSpan mode≤codeEnd mode l := by
    have endAt : (nodeParams mode l).destination+nodeSpan mode+transitionSpan mode=codeEnd mode l := rfl
    omega
  have ruleEnd : (transitionParams mode l).destination+transitionSpan mode=codeEnd mode l := rfl
  have fields:=Listing8OwnerImage.source_field_bounds mode l
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  apply Listing8MainRetarget.window mode l _ ctx.resources ctx.fields.tapeReach state entry forward current observed count
  · left;omega
  · left;omega
  · intro site member
    have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
    change site.owner+10≤codeEnd mode l at bound
    left;omega
  · left;omega

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have rules : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state).principal.memory := by
    rw [Listing8TransitionTable.Initial,window mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying _ _ (Nat.le_refl _)]
    exact current.rules
  have nodes : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g)
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state).principal.memory := by
    have after : Listing8FullTableImage.start mode origin≤Listing8GraphLayout.input mode origin g.transitions := by
      have first:=Listing8GraphLayout.transition_lower mode origin g.transitions
      change Listing8FullTableImage.start mode origin≤Listing8GraphLayout.reset mode origin g.transitions at first
      exact first.trans (Listing8GraphLayout.table_before_input mode origin g.transitions)
    rw [Listing8NodeTable.Initial,window mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent.copying _ _ after]
    exact current.nodes
  exact Listing8OriginalGraphCatalog.from_initial mode origin g _ nodes rules

theorem scalar_targets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (pc target : Nat) (value : BitVec 32)
    (member : Listing8OwnerSequence.Owner.scalar pc target value∈Listing8OwnerImage.owners mode l (values mode origin g node rule)) :
    target+4≤Listing8FullTableImage.start mode origin := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=Listing8GlobalMainBounds.direction mode origin l t g node rule ctx
  have geometry:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
  have located:=ctx.body.state.head.direction
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h <;> cases h
  · omega
  · omega
  · rw [located]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at geometry <;> omega

theorem pointer_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=Listing8GlobalPointerRegions.word mode origin l t g node rule ctx
  have first:=StringCopyWrites.word mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    (Listing8PointerCopies.word mode l) ctx.copies.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) ctx.copies.wordValid state.principal entry]
    rfl
  have last:=StringSequenceWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t) ctx.copies.dwordValid
    (Listing8GlobalPointerRegions.dwords mode origin l t g node rule ctx) _ next
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  apply BoundedStoreRegions.interval mode _ (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    _ state (fun _ _ _ upper => by omega)
  rw [Listing8PointerCopies.program,List.map_append,StringWrites.owned_run_append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial
