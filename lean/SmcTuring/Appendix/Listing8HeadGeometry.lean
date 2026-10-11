module
public import SmcTuring.Appendix.Listing8HeadTailTrace

public section
namespace SmcTuring.Appendix.Listing8HeadGeometry
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def windows (mode : Mode) (l : Listing8DirectionLayout.Layout) : List (Nat × Nat) :=
  match mode with
  | .x86 => [(Listing8DirectionLayout.selectionEnd mode l,18),
      (Listing8DirectionLayout.maskPC mode l,6),(Listing8DirectionLayout.directionPC mode l,6)]
  | .x64 => [(Listing8DirectionLayout.selectionEnd mode l,36),
      (Listing8DirectionLayout.maskPC mode l,6),(Listing8DirectionLayout.maskPC mode l+10,6),
      (Listing8DirectionLayout.directionPC mode l,6),(Listing8DirectionLayout.directionPC mode l+10,6)]

theorem tail_bounds (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) :
    Listing8HeadTailBounds.Bounds mode (region mode l) := by
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  refine ⟨bounds.capacity,?_,?_⟩
  all_goals simp only [region] at input ⊢
  all_goals cases mode <;> simp [Mode.wordBytes] at input ⊢ <;> omega

theorem window_span (mode : Mode) (l : Listing8DirectionLayout.Layout) (w : Nat × Nat)
    (member : w ∈ windows mode l) : l.start ≤ w.1 ∧ w.1+w.2 ≤ Listing8DirectionLayout.endPC mode l := by
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,
    Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem direction_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) :
    l.direction+10 ≤ w.1 ∨ w.1+w.2 ≤ l.direction+6 := by
  rw [bounds.direction]
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem distribution_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ Listing8LiteralInput.distributionLayouts mode l.input) :
    writer.destination+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.destination := by
  have after := bounds.transitionMaskAfter
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at writerMember
  rw [bounds.mask] at writerMember
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at after ⊢ <;> omega

theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) : Listing8InputWindows.Outside mode l.input w.1 w.2 := by
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have span := window_span mode (region mode l) w member
  have lower := span.1
  change Listing8LiteralInput.endPC mode l.input ≤ w.1 at lower
  have global := positions mode l t bounds
  have nodeLarge : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,
    distribution_outside mode l t bounds w member⟩
  rw [bounds.input.fields.headLabel]
  rcases bounds.nodeOutside with early | late
  · left;omega
  · right;omega

theorem pointer_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ Listing8PointerCopies.layouts mode l t) :
    writer.destination+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.destination := by
  have after := bounds.stateAfter
  simp only [Listing8PointerCopies.layouts] at writerMember
  rw [bounds.back,bounds.forward] at writerMember
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount] at after ⊢ <;> omega

theorem helper_outside (mode : Mode) (l : Listing8DirectionLayout.Layout)
    (w : Nat × Nat) (member : w ∈ windows mode l) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ Listing8DirectionLayout.helpers mode l) :
    writer.destination+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.destination := by
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem packet_outside (mode : Mode) (l : Listing8DirectionLayout.Layout)
    (w : Nat × Nat) (member : w ∈ windows mode l) (writer : DwordPackets.Site)
    (writerMember : writer ∈ Listing8DirectionLayout.arithmetic mode l) :
    writer.target+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.target := by
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem masks_separate (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) :
    Listing8LiteralMaskTrace.Separate mode l.input := by
  apply Listing8LiteralMaskTrace.fields_separate
  right
  rw [bounds.mask]
  have after := bounds.transitionMaskAfter
  cases mode <;> simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at after ⊢ <;> omega

theorem cursor_input_outside (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t) :
    Listing8InputWindows.Outside mode l.input l.input.cursor mode.wordBytes := by
  have cursor := Listing8InputBounds.cursor_bounds mode l t bounds.input.fields bounds.input.joined r
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have outside := Listing8InputBounds.outside mode l t bounds.input.fields bounds.input.joined r
  have span := positions mode l t bounds
  have inputEnd := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have nodeLarge : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),?_,outside.maskCursor⟩
  rw [bounds.input.fields.headLabel]
  rcases r.nodeOutside with early | late
  · left;omega
  · right
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at inputEnd ⊢ <;> omega

theorem cursor_helpers (mode : Mode) (l : Listing8DirectionLayout.Layout) (bounds : Listing8HeadTailBounds.Bounds mode l)
    (writer : DwordLayout.Layout) (member : writer ∈ Listing8DirectionLayout.helpers mode l) :
    writer.destination+4 ≤ l.cursor ∨ l.cursor+mode.wordBytes ≤ writer.destination := by
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals right
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before ⊢ <;> omega

theorem cursor_packets (mode : Mode) (l : Listing8DirectionLayout.Layout) (bounds : Listing8HeadTailBounds.Bounds mode l)
    (writer : DwordPackets.Site) (member : writer ∈ Listing8DirectionLayout.arithmetic mode l) :
    writer.target+4 ≤ l.cursor ∨ l.cursor+mode.wordBytes ≤ writer.target := by
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals right
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before ⊢ <;> omega

@[expose] def maskFields (mode : Mode) (l : Listing8DirectionLayout.Layout) : List Nat :=
  match mode with
  | .x86 => [Listing8DirectionLayout.maskPC mode l+6]
  | .x64 => [Listing8DirectionLayout.maskPC mode l+6,Listing8DirectionLayout.maskPC mode l+16]

theorem mask_helpers (mode : Mode) (l : Listing8DirectionLayout.Layout) (observed : Nat) (field : observed ∈ maskFields mode l)
    (writer : DwordLayout.Layout) (member : writer ∈ Listing8DirectionLayout.helpers mode l) :
    writer.destination+4 ≤ observed ∨ observed+4 ≤ writer.destination := by
  cases mode
  all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases field with rfl | rfl
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem mask_packets (mode : Mode) (l : Listing8DirectionLayout.Layout) (observed : Nat) (field : observed ∈ maskFields mode l)
    (writer : DwordPackets.Site) (member : writer ∈ Listing8DirectionLayout.arithmetic mode l) :
    writer.target+4 ≤ observed ∨ observed+4 ≤ writer.target := by
  cases mode
  all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases field with rfl | rfl
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem source_field_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (field : Nat) (span : l.start ≤ field ∧ field+4 ≤ Listing8DirectionLayout.endPC mode (region mode l)) :
    field+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ field := by
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  rcases bounds.nodeOutside with early | late
  · right;omega
  · left;omega

end SmcTuring.Appendix.Listing8HeadGeometry
