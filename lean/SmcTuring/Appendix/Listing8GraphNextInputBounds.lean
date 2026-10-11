module
public import SmcTuring.Appendix.Listing8GraphNextPointerFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextInputBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem masks_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (helper : DwordLayout.Layout) (member : helper∈Listing8LiteralInput.distributionLayouts mode l.input) :
    helper.destination+4≤Listing8FullTableImage.start mode origin := by
  have later:=Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
  rw [ctx.body.state.mask,ctx.body.state.head.mask] at member
  cases mode
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8FailureGeometry.region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,
    Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8StateGeometry.region,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at later ⊢ <;> omega

theorem fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8InputBounds.Fields mode (nextLayout mode origin l g node rule target) := by
  have old:=ctx.body.state.head.input.fields
  refine ⟨old.cursorLabel,rfl,old.masksAfter,old.masksFit,old.masksReach,?_⟩
  intro helper member
  have before:=masks_before_table mode origin l t g node rule ctx helper member
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  exact Or.inl (by change helper.destination+4≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6;omega)

theorem update (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    InputUpdate.Valid mode (Listing8LiteralInput.updateLayout mode (nextLayout mode origin l g node rule target).input) :=
  Listing8InputBounds.update mode _ t (fields mode origin l t g node rule target ctx) ctx.body.state.head.input.joined
    (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)

theorem outside (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LiteralComposition.DataOutside mode (nextLayout mode origin l g node rule target).input :=
  Listing8InputBounds.outside mode _ t (fields mode origin l t g node rule target ctx) ctx.body.state.head.input.joined
    (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)

end SmcTuring.Appendix.Listing8GraphNextInputBounds
