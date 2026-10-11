module
public import SmcTuring.Appendix.Listing8DirectionTrace
public import SmcTuring.Appendix.Listing8GlobalWindows

public section
namespace SmcTuring.Appendix.Listing8DirectionGeometry
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets
abbrev Region := Listing8DirectionLayout.Layout
@[expose] def region (mode : Mode) (l : Layout) : Region := ⟨Listing8LiteralInput.endPC mode l.input,l.input.cursor⟩
structure Bounds (mode : Mode) (l : Layout) (t : Targets) : Prop where
  input : Listing8GlobalInput.Bounds mode l t
  capacity : Listing8DirectionLayout.endPC mode (region mode l) < 2^(8*mode.wordBytes)
  direction : l.direction = Listing8DirectionLayout.directionPC mode (region mode l)
  back : t.back = Listing8DirectionLayout.backPC mode (region mode l)
  forward : t.forward = Listing8DirectionLayout.forwardPC mode (region mode l)
  mask : l.input.directionMask = Listing8DirectionLayout.maskPC mode (region mode l)+6
  transitionMaskAfter : Listing8DirectionLayout.endPC mode (region mode l) ≤ l.input.transitionMask
  stateAfter : Listing8DirectionLayout.endPC mode (region mode l) ≤ t.state
  nodeOutside : l.sourceNode+nodeSpan mode ≤ l.start ∨ Listing8DirectionLayout.endPC mode (region mode l) ≤ l.sourceNode
  transitionOutside : l.sourceTransition+transitionSpan mode ≤ l.start ∨ Listing8DirectionLayout.endPC mode (region mode l) ≤ l.sourceTransition

theorem positions (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) :
    l.start ≤ (region mode l).start ∧
    Listing8DirectionLayout.selectionEnd mode (region mode l) ≤ Listing8DirectionLayout.endPC mode (region mode l) ∧
    Listing8DirectionLayout.selectionEnd mode (region mode l) ≤ l.direction+6 := by
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  have coords := Listing8DirectionLayout.positions mode (region mode l)
  simp only [region] at coords ⊢
  rw [bounds.direction]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,region] at input coords ⊢ <;> omega

theorem helper_bytes (mode : Mode) (l : Layout) :
    (region mode l).start+(DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length =
      Listing8DirectionLayout.backPC mode (region mode l) := by
  cases mode <;> simp [DwordMixedSequence.bytes,Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,
    Listing8DirectionLayout.copy,DwordMixedImage.bytes_length,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem arithmetic_header_bounds (mode : Mode) (l : Layout) (reader : DwordPackets.Site)
    (member : reader ∈ Listing8DirectionLayout.arithmetic mode (region mode l)) :
    (region mode l).start ≤ reader.pc ∧ reader.pc+6 ≤ Listing8DirectionLayout.selectionEnd mode (region mode l) := by
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,
    Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem input_window (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (observed count : Nat) (lower : (region mode l).start ≤ observed)
    (upper : observed+count ≤ Listing8DirectionLayout.selectionEnd mode (region mode l)) :
    Listing8InputWindows.Outside mode l.input observed count := by
  have scalar := Listing8CopiedOwners.scalar_bounds mode l
  have fields := Listing8LiteralComposition.field_bounds mode l.input
  have span := positions mode l t bounds
  have nodeLarge : 10 ≤ nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),
    Or.inl (by change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),
    Or.inl (by change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),?_,?_⟩
  · rw [bounds.input.fields.headLabel]
    rcases bounds.nodeOutside with early | late
    · left;omega
    · right;omega
  · intro helper member
    right
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
    rw [bounds.mask] at member
    have coords := Listing8DirectionLayout.positions mode (region mode l)
    have transition := bounds.transitionMaskAfter
    cases mode
    all_goals simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts,
      List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp only [reduceCtorEq,ite_true,ite_false] at coords
    all_goals simp only;omega

theorem pointer_headers (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (reader : DwordPackets.Site) (readerMember : reader ∈ Listing8DirectionLayout.arithmetic mode (region mode l))
    (writer : DwordLayout.Layout) (writerMember : writer ∈ Listing8PointerCopies.layouts mode l t) :
    writer.destination+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.destination := by
  have after := bounds.stateAfter
  simp only [Listing8PointerCopies.layouts] at writerMember
  rw [bounds.back,bounds.forward] at writerMember
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at readerMember
  all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases readerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem pointer_helpers (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (writer : DwordLayout.Layout) (member : writer ∈ Listing8PointerCopies.layouts mode l t) :
    (region mode l).start+(DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length ≤
      writer.destination := by
  rw [helper_bytes]
  have after := bounds.stateAfter
  simp only [Listing8PointerCopies.layouts] at member
  rw [bounds.back,bounds.forward] at member
  cases mode
  all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

end SmcTuring.Appendix.Listing8DirectionGeometry
