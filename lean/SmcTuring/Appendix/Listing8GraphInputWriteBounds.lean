module
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds
public import SmcTuring.Appendix.Listing8LiteralInputWrites

public section
namespace SmcTuring.Appendix.Listing8GraphInputWriteBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem cursor_tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    (origin≤l.input.cursor ∧ l.input.cursor+mode.wordBytes≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
    (origin≤l.input.head+6 ∧ l.input.head+10≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) := by
  have placed:=Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx
  have cursor:=Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  have sourceBounds:=placed.node
  have nodeLarge : 10≤nodeSpan mode := by cases mode <;> decide
  have block:=placed.block
  refine ⟨⟨by omega,by omega⟩,?_⟩
  rw [ctx.body.state.head.input.fields.headLabel]
  exact ⟨by omega,by omega⟩

theorem masks (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    ∀ helper∈Listing8LiteralInput.distributionLayouts mode l.input,
      origin≤helper.destination ∧ helper.destination+4≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have input:=Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx
  have inputPositions:=Listing8LiteralInput.positions mode l.input
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  have failureBefore : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body <;> omega
  intro helper member
  have after:=ctx.body.state.head.input.fields.masksAfter helper member
  have lower : origin≤helper.destination := by
    have ending:=inputPositions.2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega
  refine ⟨lower,Nat.le_trans ?_ failureBefore⟩
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
  rw [ctx.body.state.mask,ctx.body.state.head.mask] at member
  cases mode
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8FailureGeometry.region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
    Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8StateGeometry.region,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]

theorem placement (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LiteralInputWrites.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) l.input :=
  ⟨Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx,
    (cursor_tape mode origin l t g node rule ctx).1,(cursor_tape mode origin l t g node rule ctx).2,
    masks mode origin l t g node rule ctx⟩

end SmcTuring.Appendix.Listing8GraphInputWriteBounds
