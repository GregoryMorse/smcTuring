module
public import SmcTuring.Appendix.Listing8StateTrace

public section
namespace SmcTuring.Appendix.Listing8StateGeometry
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (l : Layout) : Listing8StateLayout.Layout :=
  ⟨Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l),StringCodec.sourceField mode (secondStart mode l)⟩
structure Bounds (mode : Mode) (l : Layout) (t : Targets) : Prop where
  head : Listing8DirectionGeometry.Bounds mode l t
  capacity : Listing8StateLayout.endPC mode (region mode l) < 2^(8*mode.wordBytes)
  state : t.state = Listing8StateLayout.newPC mode (region mode l)
  mask : l.input.transitionMask = Listing8StateLayout.maskPC mode (region mode l)+6
  nodeOutside : l.sourceNode+nodeSpan mode ≤ l.start ∨ Listing8StateLayout.endPC mode (region mode l) ≤ l.sourceNode
  transitionOutside : l.sourceTransition+transitionSpan mode ≤ l.start ∨ Listing8StateLayout.endPC mode (region mode l) ≤ l.sourceTransition

theorem positions (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) :
    (region mode l).start = l.start+(if mode = .x86 then 597 else 932) ∧
    Listing8StateLayout.endPC mode (region mode l) = l.start+(if mode = .x86 then 644 else 1028) := by
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have head := (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2
  have state := (Listing8StateLayout.positions mode (region mode l)).2.2.2
  simp only [region,Listing8DirectionGeometry.region] at head state ⊢
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input head state ⊢ <;> omega

theorem local_bounds (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (bounds : Bounds mode l t) :
    Listing8StateBounds.Bounds mode (region mode l) := by
  have before := Listing8PointerCopies.cursor_before mode l
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have coords := positions mode l t bounds
  have first := endpoint_lower mode l.start (nodeSpan mode)
  change l.start ≤ secondStart mode l at first
  have after := r.inputAfter
  refine ⟨bounds.capacity,?_,?_⟩
  all_goals simp only [region,Listing8PointerCopies.word] at before coords ⊢
  all_goals cases mode <;> simp [StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at before ⊢ <;>
    simp only [reduceCtorEq,ite_true,ite_false] at input coords <;> omega

@[expose] def windows (mode : Mode) (l : Listing8StateLayout.Layout) : List (Nat × Nat) :=
  match mode with
  | .x86 => [(l.start,17),(Listing8StateLayout.newPC mode l,6),(Listing8StateLayout.maskPC mode l,6),(Listing8StateLayout.updatePC mode l,6)]
  | .x64 => [(l.start,36),(Listing8StateLayout.newPC mode l,6),(Listing8StateLayout.newPC mode l+10,6),
      (Listing8StateLayout.maskPC mode l,6),(Listing8StateLayout.maskPC mode l+10,6),
      (Listing8StateLayout.updatePC mode l,6),(Listing8StateLayout.updatePC mode l+10,6)]

theorem window_span (mode : Mode) (l : Listing8StateLayout.Layout) (w : Nat × Nat) (member : w ∈ windows mode l) :
    l.start ≤ w.1 ∧ w.1+w.2 ≤ Listing8StateLayout.endPC mode l := by
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem direction_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (observed : Nat) (after : (region mode l).start ≤ observed) : l.direction+10 ≤ observed := by
  rw [bounds.head.direction]
  change Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l) ≤ observed at after
  cases mode <;> simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at after ⊢ <;> omega

theorem distribution_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ Listing8LiteralInput.distributionLayouts mode l.input) :
    writer.destination+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.destination := by
  simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at writerMember
  rw [bounds.mask,bounds.head.mask] at writerMember
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,region] <;> omega

theorem pointer_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ Listing8PointerCopies.layouts mode l t) :
    writer.destination+4 ≤ w.1 ∨ w.1+w.2 ≤ writer.destination := by
  simp only [Listing8PointerCopies.layouts] at writerMember
  rw [bounds.state,bounds.head.back,bounds.head.forward] at writerMember
  cases mode
  all_goals simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,region] <;> omega

theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) : Listing8InputWindows.Outside mode l.input w.1 w.2 := by
  have spans := window_span mode (region mode l) w member
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have coords := positions mode l t bounds
  have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have lower : Listing8LiteralInput.endPC mode l.input ≤ w.1 := by
    have upper := (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2
    change (region mode l).start = Listing8LiteralInput.endPC mode l.input+(if mode = .x86 then 91 else 202) at upper
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at upper <;> omega
  have large : 10 ≤ nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,distribution_outside mode l t bounds w member⟩
  rw [bounds.head.input.fields.headLabel]
  rcases bounds.nodeOutside with early | late
  · left
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input coords <;> omega
  · right;omega

end SmcTuring.Appendix.Listing8StateGeometry
