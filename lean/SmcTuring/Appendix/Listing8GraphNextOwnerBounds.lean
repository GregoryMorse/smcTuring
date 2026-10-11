module
public import SmcTuring.Appendix.Listing8GraphPatchBlock

public section
namespace SmcTuring.Appendix.Listing8GraphNextOwnerBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem direction_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    l.direction+10≤Listing8FullTableImage.start mode origin := by
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  rw [ctx.boot.packed] at input
  rw [ctx.body.state.head.direction,Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;>
    simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at input ⊢ <;>
    simp [Listing8DirectionGeometry.region,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

/-- All eight fixed scalar-owner conditions transfer to any next graph
labels; direction/source separation follows from packed code placement. -/
theorem fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8GraphOwnerBounds.Fields mode (nextLayout mode origin l g node rule target) := by
  have before:=direction_before_table mode origin l t g node rule ctx
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  refine ⟨ctx.fields.directionAfter,ctx.fields.directionFits,Or.inr ?_,Or.inr ?_,
    ctx.fields.tapeReach,ctx.fields.ruleReach,ctx.fields.freshReach,ctx.fields.directionReach⟩
  · exact Nat.le_trans before nodeAfter
  · exact Nat.le_trans before ruleAfter
theorem owner_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8CopiedOwners.Bounds mode (nextLayout mode origin l g node rule target)
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :=
  Listing8GraphOwnerBounds.bounds mode origin (nextLayout mode origin l g node rule target)
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target ctx.boot.packed
    (fields mode origin l t g node rule target ctx) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)
theorem pointer_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8PointerCopies.Bounds mode (nextLayout mode origin l g node rule target) t := ⟨ctx.copies.wordValid,ctx.copies.dwordValid,ctx.copies.targetsAfter⟩
theorem boot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8BootImage.Bounds mode origin (nextLayout mode origin l g node rule target) := by
  have code:=code_length mode l
  have before:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  refine ⟨ctx.boot.packed,Or.inr ?_,Or.inr ?_⟩
  · change l.start≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule);omega
  · change l.start≤Listing8GraphLayout.transition mode origin target.val;omega

end SmcTuring.Appendix.Listing8GraphNextOwnerBounds
