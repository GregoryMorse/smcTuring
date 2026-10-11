module
public import SmcTuring.Appendix.Listing8GraphNextDirectionBounds

public section
namespace SmcTuring.Appendix.Listing8DirectionPrefixFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

theorem code_before (mode : Mode) (l : Layout) (r : Resources mode l) (w : Nat × Nat)
    (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) : codeEnd mode l≤w.1 := by
  have lower:=(Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member).1
  change Listing8LiteralInput.endPC mode l.input≤w.1 at lower
  have input:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have before:=r.inputAfter
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega

theorem direction_store_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    l.direction+10≤w.1 ∨ w.1+w.2≤l.direction+6 := by
  rw [bounds.direction]
  cases mode
  all_goals simp only [Listing8DirectionWindows.windows,Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,
    Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem pointer_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l))
    (writer : DwordLayout.Layout) (writerMember : writer∈Listing8PointerCopies.layouts mode l t) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  have after:=bounds.stateAfter
  simp only [Listing8PointerCopies.layouts] at writerMember
  rw [bounds.back,bounds.forward] at writerMember
  cases mode
  all_goals simp only [Listing8DirectionWindows.windows,Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,
    Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem distribution_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l))
    (writer : DwordLayout.Layout) (writerMember : writer∈Listing8LiteralInput.distributionLayouts mode l.input) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  have after:=bounds.transitionMaskAfter
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at writerMember
  rw [bounds.mask] at writerMember
  cases mode
  all_goals simp only [Listing8DirectionWindows.windows,Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,
    Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    Listing8InputWindows.Outside mode l.input w.1 w.2 := by
  have spans:=Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member
  have lower:=spans.1
  change Listing8LiteralInput.endPC mode l.input≤w.1 at lower
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have large : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  have before:=(Listing8DirectionGeometry.positions mode l t bounds).1
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,distribution_outside mode l t bounds w member⟩
  rw [bounds.input.fields.headLabel]
  rcases bounds.nodeOutside with early | late
  · left;omega
  · right;omega

end SmcTuring.Appendix.Listing8DirectionPrefixFrames
