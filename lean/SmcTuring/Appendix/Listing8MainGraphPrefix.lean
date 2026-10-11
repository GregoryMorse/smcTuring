module
public import SmcTuring.Appendix.Listing8MainGraphImage
public import SmcTuring.Appendix.Listing8MainInputFrames
public import SmcTuring.Appendix.Listing8GraphNextInputBounds

public section
namespace SmcTuring.Appendix.Listing8MainGraphPrefix
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8MainInput.Bounds mode l t (values mode origin g node rule) := by
  refine ⟨⟨⟨ctx.resources,owners mode origin l t g node rule ctx,ctx.copies,ctx.body.state.head.input.fields,
    ctx.body.state.head.input.joined,ctx.fields.tapeReach⟩,ctx.body.state.head.input.targetsAfter⟩,?_⟩
  intro writer member
  have after:=Nat.le_trans (Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx)
    (Listing8GraphOwnerBounds.node_after_table mode origin g node)
  rw [←ctx.nodeLocated] at after
  exact Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body _ after writer member)

/-- All generic prefix writers precede the original rule/node declarations.
The current complete graph is an observation of the entry, not a later image. -/
theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have b:=(bounds mode origin l t g node rule ctx).input.prefixBounds
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have inputBefore:=Listing8GraphCopyResources.input_before_table mode origin l t g node rule ctx
  have direction:=Listing8GraphNextOwnerBounds.direction_before_table mode origin l t g node rule ctx
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have cursor:=Listing8PointerCopies.cursor_before_patch mode l
  have coords:=coordinates mode l
  have d:=destinations mode l
  apply Listing8MainPrefixFrames.window mode l t _ b state current.entry current.forward image.prefixCurrent observed count
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · intro site member
    have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
    change site.owner+10≤codeEnd mode l at bound
    exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · intro writer member
    exact Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body observed
      (Nat.le_trans (Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx) after) writer member)

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have inputAfter:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule ctx old state current _ _ inputAfter]
    exact current.nodes
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule ctx old state current _ _ (Nat.le_refl _)]
    exact current.rules

/-- Input preserves every original declaration window except the selected
symbol field, whose write is covered by the separate logical graph update. -/
theorem input_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed)
    (tape : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory observed count := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have inputBefore:=Listing8GraphCopyResources.input_before_table mode origin l t g node rule ctx
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  apply Listing8MainInputFrames.input_window mode l t _ old (bounds mode origin l t g node rule ctx)
    state current.entry current.forward image observed count
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,?_⟩
  · simpa only [ctx.body.state.head.input.fields.headLabel] using tape
  · intro writer member
    exact Or.inl (Nat.le_trans (Listing8GraphNextInputBounds.masks_before_table mode origin l t g node rule ctx writer member) after)

end SmcTuring.Appendix.Listing8MainGraphPrefix
