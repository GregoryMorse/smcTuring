module
public import SmcTuring.Appendix.Listing8GlobalInputRegions

public section
namespace SmcTuring.Appendix.Listing8InputStoreFields
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual input phase writes later main-code operands, the first
macro cursor word, or the original node symbol operand. -/
@[expose] def Allowed (mode : Mode) (origin : Nat) (l : Layout) (address count : Nat) : Prop :=
  (codeEnd mode l≤address ∧ address+count≤Listing8JumpLayout.jumpPC mode origin) ∨
    (address=StringCodec.sourceField mode l.start ∧ count≤mode.wordBytes) ∨
    (address=l.sourceNode+6 ∧ count≤4)

theorem masks (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈Listing8LiteralInput.distributionLayouts mode l.input,
      Allowed mode origin l helper.destination 4 := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have inputPositions:=Listing8LiteralInput.positions mode l.input
  have failure:=Listing8FailureLayout.positions mode
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
  have endAt:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  have failureBefore : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤
      Listing8JumpLayout.jumpPC mode origin := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at failure <;> omega
  intro helper member
  have after:=ctx.body.state.head.input.fields.masksAfter helper member
  have startBefore : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have ending:=inputPositions.2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega
  have prefixSize:=(Listing8PointerCopies.sizes mode l t).2.1
  have joined:=ctx.body.state.head.input.joined
  left
  refine ⟨by omega,Nat.le_trans ?_ failureBefore⟩
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
  rw [ctx.body.state.mask,ctx.body.state.head.mask] at member
  cases mode
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8FailureGeometry.region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
    Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8StateGeometry.region,Listing8DirectionLayout.endPC,
    Listing8DirectionLayout.maskPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]

theorem fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8InputTemplateRegions.Fields mode l.input (Allowed mode origin l) := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have internal:=Listing8LiteralComposition.field_bounds mode l.input
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have prefixSize:=(Listing8PointerCopies.sizes mode l t).2.1
  have joined:=ctx.body.state.head.input.joined
  have body (address : Nat) (inside : l.input.start≤address ∧ address+4≤Listing8LiteralInput.endPC mode l.input) :
      Allowed mode origin l address 4 := Or.inl ⟨by omega,inside.2.trans input.2⟩
  refine ⟨body _ internal.1,body _ source,body _ internal.2.1,body _ internal.2.2,?_,?_,masks mode origin l t g node rule ctx⟩
  · right;left
    exact ⟨ctx.body.state.head.input.fields.cursorLabel,Nat.le_refl _⟩
  · right;right
    rw [ctx.body.state.head.input.fields.headLabel]
    exact ⟨rfl,Nat.le_refl _⟩

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Allowed mode origin l)
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule
        (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map
          (StringStoreWrites.liftDword mode)) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have bounds:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  apply StringStoreRegions.mixed mode _ _ _
  exact Listing8InputTemplateRegions.mask_complete mode l.input _ _ old.pending _ old.mask ctx.resources.inputFits
    (Listing8InputBounds.masks mode l bounds.input.prefixBounds.fields)
    (Listing8InputBounds.update mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources)
    (Listing8InputBounds.outside mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources) _
    (Listing8MainPrefix.entry mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    (Listing8MainInputImage.current mode l t _ old bounds.input state current.entry current.forward image)
    (Listing8MainPrefixFrames.head_cursor mode l t _ bounds.input.prefixBounds state current.entry current.forward image.prefixCurrent)
    _ (fields mode origin l t g node rule ctx)


end SmcTuring.Appendix.Listing8InputStoreFields
