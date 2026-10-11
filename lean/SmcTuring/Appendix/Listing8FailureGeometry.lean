module
public import SmcTuring.Appendix.Listing8GlobalState
public import SmcTuring.Appendix.Listing8FailureBounds

public section
namespace SmcTuring.Appendix.Listing8FailureGeometry
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (l : Layout) (sentinel begin : Nat) : Listing8FailureLayout.Layout :=
  ⟨Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l),
    (Listing8StateGeometry.region mode l).cursor,sentinel,begin⟩
structure Bounds (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) : Prop where
  state : Listing8StateGeometry.Bounds mode l t
  capacity : Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5 < 2^(8*mode.wordBytes)
  sentinelFits : sentinel+mode.wordBytes < 2^(8*mode.wordBytes)
  sentinelOutside : sentinel+mode.wordBytes ≤ Listing8FailureLayout.ownerPC (region mode l sentinel begin) ∨
    Listing8FailureLayout.comparisonPC mode (region mode l sentinel begin) ≤ sentinel
  nodeOutside : l.sourceNode+nodeSpan mode ≤ l.start ∨ Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5 ≤ l.sourceNode
  transitionOutside : l.sourceTransition+transitionSpan mode ≤ l.start ∨ Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5 ≤ l.sourceTransition

theorem positions (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (bounds : Bounds mode l t sentinel begin) :
    (region mode l sentinel begin).start=l.start+(if mode=.x86 then 644 else 1028) ∧
    Listing8FailureLayout.endPC mode (region mode l sentinel begin)=l.start+(if mode=.x86 then 743 else 1150) ∧
    Listing8FailureLayout.callPC mode (region mode l sentinel begin)=l.start+(if mode=.x86 then 749 else 1172) := by
  have prior:=Listing8StateGeometry.positions mode l t bounds.state
  have next:=Listing8FailureLayout.positions mode (region mode l sentinel begin)
  have entry : (region mode l sentinel begin).start=l.start+(if mode=.x86 then 644 else 1028) := prior.2
  refine ⟨entry,?_,?_⟩
  all_goals cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at entry next ⊢ <;> omega

theorem local_bounds (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) : Listing8FailureBounds.Bounds mode (region mode l sentinel begin) := by
  have old:=Listing8StateGeometry.local_bounds mode l t r bounds.state
  have coords:=positions mode l t sentinel begin bounds
  have prior:=Listing8StateGeometry.positions mode l t bounds.state
  have earlier:=Listing8CopyImage.endpoint_lower mode l.start (nodeSpan mode)
  change l.start ≤ secondStart mode l at earlier
  have before:=old.cursorBefore
  refine ⟨bounds.capacity,?_,?_,bounds.sentinelFits,bounds.sentinelOutside⟩
  · cases mode <;> simp [region,Listing8StateGeometry.region,Listing8StateLayout.endPC,
      Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
      Listing8PointerCopies.halfCount,Mode.wordBytes] at before ⊢ <;> omega
  · have failure:=Listing8FailureLayout.positions mode (region mode l sentinel begin)
    cases mode <;> simp [region,Listing8StateGeometry.region,StringCodec.sourceField,StringCodec.fieldOffset] at coords failure ⊢ <;> omega

theorem pointer_outside (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (bounds : Bounds mode l t sentinel begin)
    (observed : Nat) (after : (region mode l sentinel begin).start ≤ observed)
    (writer : DwordLayout.Layout) (member : writer ∈ Listing8PointerCopies.layouts mode l t) : writer.destination+4 ≤ observed := by
  simp only [Listing8PointerCopies.layouts] at member
  rw [bounds.state.state,bounds.state.head.back,bounds.state.head.forward] at member
  cases mode
  all_goals simp only [Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [region,Listing8StateGeometry.region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,
    Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.maskPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (bounds : Bounds mode l t sentinel begin)
    (observed count : Nat) (after : (region mode l sentinel begin).start ≤ observed)
    (upper : observed+count ≤ Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5) :
    Listing8InputWindows.Outside mode l.input observed count := by
  have coords:=positions mode l t sentinel begin bounds
  have input:=Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  have large : 10 ≤ nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,?_⟩
  · rw [bounds.state.head.input.fields.headLabel]
    rcases bounds.nodeOutside with early | late
    · left
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
    · right;omega
  · intro writer member
    left
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
    rw [bounds.state.mask,bounds.state.head.mask] at member
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp [region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
      Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8StateGeometry.region,
      Listing8DirectionLayout.endPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.directionPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem state_helpers_before (mode : Mode) (l : Layout) (sentinel begin : Nat) (writer : DwordLayout.Layout)
    (member : writer ∈ Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l)) :
    writer.destination+4 ≤ (region mode l sentinel begin).start := by
  cases mode
  all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
    Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem state_packets_before (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) (writer : DwordPackets.Site)
    (member : writer ∈ Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l)) :
    writer.target+4 ≤ (region mode l sentinel begin).start := by
  have before:=(Listing8StateGeometry.local_bounds mode l t r bounds.state).cursorBefore
  cases mode
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
    Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
    Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before ⊢ <;> omega

end SmcTuring.Appendix.Listing8FailureGeometry
