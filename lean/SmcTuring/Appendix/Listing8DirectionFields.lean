module
public import SmcTuring.Appendix.Listing8GlobalDirection
public import SmcTuring.Appendix.Listing8DirectionMemory

public section
namespace SmcTuring.Appendix.Listing8DirectionFields
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Dword := BitVec 32
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def fields (mode : Mode) (l : Layout) :=
  [Listing8DirectionLayout.directionPC mode (region mode l)+6,
    Listing8DirectionLayout.backPC mode (region mode l)+6,Listing8DirectionLayout.forwardPC mode (region mode l)+6] ++
  (if mode = .x86 then [] else [Listing8DirectionLayout.directionPC mode (region mode l)+16,
    Listing8DirectionLayout.backPC mode (region mode l)+16,Listing8DirectionLayout.forwardPC mode (region mode l)+16])
@[expose] def low (mode : Mode) (value : Word mode) : Dword :=
  match mode with | .x86 => value | .x64 => X64.HalfWords.low value

theorem field_bounds (mode : Mode) (l : Layout) (observed : Nat) (member : observed ∈ fields mode l) :
    (region mode l).start ≤ observed ∧ observed+4 ≤ Listing8DirectionLayout.endPC mode (region mode l) := by
  cases mode
  all_goals simp only [fields,reduceCtorEq,ite_true,ite_false,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
    Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t)
    (observed : Nat) (member : observed ∈ fields mode l) : Listing8InputWindows.Outside mode l.input observed 4 := by
  have span := field_bounds mode l observed member
  have scalar := Listing8CopiedOwners.scalar_bounds mode l
  have input := Listing8LiteralComposition.field_bounds mode l.input
  have before := (positions mode l t bounds).1
  have nodeLarge : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  refine ⟨Or.inl (by have lower := span.1;change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),
    Or.inl (by have lower := span.1;change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),
    Or.inl (by have lower := span.1;change Listing8LiteralInput.endPC mode l.input ≤ observed at lower;omega),?_,?_⟩
  · rw [bounds.input.fields.headLabel]
    rcases bounds.nodeOutside with early | late
    · left;omega
    · right;omega
  · intro helper helperMember
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at helperMember
    rw [bounds.mask] at helperMember
    have after := bounds.transitionMaskAfter
    cases mode
    all_goals simp only [fields,reduceCtorEq,ite_true,ite_false,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [reduceCtorEq,ite_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at helperMember
    all_goals rcases helperMember with rfl | rfl | rfl | rfl
    all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem input_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed : Nat) (member : observed ∈ fields mode l) :
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory observed =
      DwordCode.get (Listing8PointerImage.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory observed := by
  have window := Listing8GlobalWindows.input mode l t v r owners copies bounds.input
    (Listing8DirectionImage.backing mode l extra) seed observed 4 (input_outside mode l t bounds observed member)
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) window

theorem pointer_low (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (value : Word mode) :
    DwordCode.get (Listing8PointerValues.putPointer mode memory pc value) (pc+6) = low mode value := by
  cases mode with
  | x86 => exact DwordCode.get_put memory (pc+6) value
  | x64 =>
    rw [Listing8PointerValues.putPointer,DwordCode.get_frame _ (pc+16) (pc+6) _ (by
      intro index;have bound := index.isLt;simp only [ByteMemory.Inside];omega),DwordCode.get_put]
    rfl

theorem pointer_high (memory : ByteMemory.Memory) (pc : Nat) (value : Word .x64) :
    DwordCode.get (Listing8PointerValues.putPointer .x64 memory pc value) (pc+16) = X64.HalfWords.high value :=
  DwordCode.get_put _ _ _

theorem pointer_frame (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (value : Word mode)
    (observed : Nat) (outside : pc+(if mode = .x86 then 10 else 20) ≤ observed ∨ observed+4 ≤ pc+6) :
    DwordCode.get (Listing8PointerValues.putPointer mode memory pc value) observed = DwordCode.get memory observed := by
  cases mode with
  | x86 =>
    apply DwordCode.get_frame
    intro index
    have bound := index.isLt
    simp only [ByteMemory.Inside]
    simp only [reduceCtorEq,ite_true] at outside
    rcases outside with early | late <;> omega
  | x64 =>
    simp only [Listing8PointerValues.putPointer]
    rw [DwordCode.get_frame _ (pc+16) observed _ (by
      intro index;have bound := index.isLt;simp only [ByteMemory.Inside];
      simp only [reduceCtorEq,ite_false] at outside;rcases outside with early | late <;> omega),
      DwordCode.get_frame _ (pc+6) observed _ (by
      intro index;have bound := index.isLt;simp only [ByteMemory.Inside];
      simp only [reduceCtorEq,ite_false] at outside;rcases outside with early | late <;> omega)]

end SmcTuring.Appendix.Listing8DirectionFields
