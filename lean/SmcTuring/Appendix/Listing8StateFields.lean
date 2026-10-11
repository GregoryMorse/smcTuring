module
public import SmcTuring.Appendix.Listing8GlobalState

public section
namespace SmcTuring.Appendix.Listing8StateFields
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def newFields (mode : Mode) (l : Listing8StateLayout.Layout) : List Nat :=
  match mode with
  | .x86 => [Listing8StateLayout.newPC mode l+6]
  | .x64 => [Listing8StateLayout.newPC mode l+6,Listing8StateLayout.newPC mode l+16]
@[expose] def maskFields (mode : Mode) (l : Listing8StateLayout.Layout) : List Nat :=
  match mode with
  | .x86 => [Listing8StateLayout.maskPC mode l+6]
  | .x64 => [Listing8StateLayout.maskPC mode l+6,Listing8StateLayout.maskPC mode l+16]

theorem field_span (mode : Mode) (l : Listing8StateLayout.Layout) (observed : Nat)
    (member : observed ∈ newFields mode l ++ maskFields mode l) :
    l.start ≤ observed ∧ observed+4 ≤ Listing8StateLayout.endPC mode l := by
  cases mode
  all_goals simp only [newFields,maskFields,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem new_input_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (observed : Nat) (member : observed ∈ newFields mode (region mode l)) : Listing8InputWindows.Outside mode l.input observed 4 := by
  have spans := field_span mode (region mode l) observed (List.mem_append_left _ member)
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have coords := positions mode l t bounds
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have lower : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input coords <;> omega
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,?_⟩
  · rw [bounds.head.input.fields.headLabel]
    rcases bounds.nodeOutside with early | late
    · left;cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
    · right;omega
  · intro writer writerMember
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at writerMember
    rw [bounds.mask,bounds.head.mask] at writerMember
    cases mode
    all_goals simp only [newFields,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at writerMember
    all_goals rcases member with rfl | rfl
    all_goals rcases writerMember with rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
      Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,region] <;> omega

theorem cursor_input_outside (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t) :
    Listing8InputWindows.Outside mode l.input (region mode l).cursor mode.wordBytes := by
  have before := Listing8PointerCopies.cursor_before mode l
  change (region mode l).cursor+mode.wordBytes ≤ codeEnd mode l at before
  have first := endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  change l.start ≤ secondStart mode l at first
  have lower : l.start ≤ (region mode l).cursor := by simp only [region,StringCodec.sourceField];omega
  have after := r.inputAfter
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),?_,?_⟩
  · rw [bounds.head.input.fields.headLabel]
    rcases r.nodeOutside with early | late
    · left;omega
    · right;cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  · intro writer member
    right
    have later := bounds.head.input.fields.masksAfter writer member
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega

theorem first_cursor_before (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) :
    l.input.cursor+mode.wordBytes ≤ (region mode l).cursor := by
  rw [bounds.head.input.fields.cursorLabel]
  have field := StringCodec.field_end mode l.start
  have body : StringCodec.bodyStart mode l.start ≤ secondStart mode l := by
    unfold secondStart StringCodec.endpoint StringCodec.bodyEnd;omega
  simp only [region,StringCodec.sourceField] at field ⊢
  unfold StringCodec.bodyStart at body
  omega

theorem cursor_selection_helpers (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t)
    (writer : DwordLayout.Layout) (member : writer ∈ Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l)) :
    writer.destination+4 ≤ (region mode l).cursor ∨ (region mode l).cursor+mode.wordBytes ≤ writer.destination := by
  have before := Listing8PointerCopies.cursor_before mode l
  have after := r.inputAfter
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  cases mode
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals right
  all_goals simp [Listing8PointerCopies.word,region,Listing8DirectionGeometry.region,Mode.wordBytes,
    Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at before input ⊢ <;> omega

theorem cursor_selection_packets (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t)
    (writer : DwordPackets.Site) (member : writer ∈ Listing8DirectionLayout.arithmetic mode (Listing8DirectionGeometry.region mode l)) :
    writer.target+4 ≤ (region mode l).cursor ∨ (region mode l).cursor+mode.wordBytes ≤ writer.target := by
  have before := Listing8PointerCopies.cursor_before mode l
  have after := r.inputAfter
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals right
  all_goals simp [Listing8PointerCopies.word,region,Listing8DirectionGeometry.region,Mode.wordBytes,
    Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at before input ⊢ <;> omega

theorem cursor_tail_xors (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t)
    (writer : DwordXorHelper.Layout) (member : writer ∈ Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l)) :
    writer.destination+4 ≤ (region mode l).cursor ∨ (region mode l).cursor+mode.wordBytes ≤ writer.destination := by
  have before := Listing8PointerCopies.cursor_before mode l
  have after := r.inputAfter
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  cases mode
  all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals right
  all_goals simp [Listing8PointerCopies.word,region,Listing8DirectionGeometry.region,Mode.wordBytes,
    Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at before input ⊢ <;> omega

theorem cursor_tail_packets (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t)
    (writer : DwordPackets.Site) (member : writer ∈ Listing8DirectionLayout.masks mode (Listing8DirectionGeometry.region mode l) ++
      Listing8DirectionLayout.heads mode (Listing8DirectionGeometry.region mode l)) :
    writer.target+4 ≤ (region mode l).cursor ∨ (region mode l).cursor+mode.wordBytes ≤ writer.target := by
  have before := Listing8PointerCopies.cursor_before mode l
  have first := first_cursor_before mode l t bounds
  have after := r.inputAfter
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  cases mode
  all_goals simp only [Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,Listing8DirectionLayout.group,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8PointerCopies.word,region,Listing8DirectionGeometry.region,Mode.wordBytes,
    Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at before first input ⊢ <;> omega

end SmcTuring.Appendix.Listing8StateFields
