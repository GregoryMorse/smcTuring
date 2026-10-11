module
public import SmcTuring.Appendix.Listing8GlobalHead

public section
namespace SmcTuring.Appendix.Listing8StateLayout
open Native
structure Layout where
  start : Nat
  cursor : Nat
@[expose] def halves (mode : Mode) := Listing8PointerCopies.halfCount mode
@[expose] def newPC (mode : Mode) (l : Layout) := l.start+halves mode*DwordLayout.span mode
@[expose] def maskPC (mode : Mode) (l : Layout) := newPC mode l+halves mode*10
@[expose] def updatePC (mode : Mode) (l : Layout) := maskPC mode l+halves mode*10
@[expose] def endPC (mode : Mode) (l : Layout) := updatePC mode l+halves mode*10
@[expose] def helpers (mode : Mode) (l : Layout) :=
  Listing8PointerCopies.split mode l.start l.cursor (updatePC mode l+6)
@[expose] def newPackets (mode : Mode) (l : Layout) := Listing8DirectionLayout.group mode (newPC mode l) 10 (updatePC mode l+6) .bitXor
@[expose] def masks (mode : Mode) (l : Layout) := Listing8DirectionLayout.group mode (maskPC mode l) 10 (updatePC mode l+6) .bitAnd
@[expose] def updates (mode : Mode) (l : Layout) : List DwordPackets.Site :=
  match mode with
  | .x86 => [⟨updatePC mode l,.bitXor,l.cursor⟩]
  | .x64 => [⟨updatePC mode l,.bitXor,l.cursor⟩,⟨updatePC mode l+10,.bitXor,l.cursor+4⟩]
@[expose] def packets (mode : Mode) (l : Layout) := newPackets mode l ++ masks mode l ++ updates mode l
@[expose] def bytes (mode : Mode) (l : Layout) :=
  DwordMixedSequence.bytes mode (helpers mode l) ++ DwordPackets.bytes mode (packets mode l) Listing8DirectionLayout.force

theorem helper_chain (mode : Mode) (l : Layout) : StringDwordSequence.Contiguous mode l.start (helpers mode l) := by
  cases mode <;> simp [helpers,Listing8PointerCopies.split,DwordMixedSequence.Contiguous,DwordLayout.endPC,
    DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,DwordLayout.span,Nat.add_assoc]

theorem packet_chain (mode : Mode) (l : Layout) : DwordPackets.Contiguous (newPC mode l) (packets mode l) := by
  cases mode <;> simp [packets,newPackets,masks,updates,Listing8DirectionLayout.group,DwordPackets.Contiguous,
    DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,maskPC,updatePC,halves,Listing8PointerCopies.halfCount,Nat.add_assoc]

theorem positions (mode : Mode) (l : Layout) :
    newPC mode l = l.start+(if mode = .x86 then 17 else 36) ∧
    maskPC mode l = l.start+(if mode = .x86 then 27 else 56) ∧
    updatePC mode l = l.start+(if mode = .x86 then 37 else 76) ∧
    endPC mode l = l.start+(if mode = .x86 then 47 else 96) := by
  cases mode <;> simp [newPC,maskPC,updatePC,endPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem helper_length (mode : Mode) (l : Layout) : (helpers mode l).length = halves mode := by cases mode <;> rfl

theorem packet_length (mode : Mode) (l : Layout) : (packets mode l).length = 3*halves mode := by cases mode <;> rfl

theorem helper_span (mode : Mode) (l : Layout) :
    l.start+(DwordMixedSequence.bytes mode (helpers mode l)).length = newPC mode l := by
  cases mode <;> simp [helpers,Listing8PointerCopies.split,DwordMixedSequence.bytes,DwordMixedImage.bytes_length,
    newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem packet_span (mode : Mode) (l : Layout) :
    newPC mode l+((packets mode l).map DwordPackets.size).sum = endPC mode l := by
  cases mode <;> simp [packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,endPC,updatePC,maskPC,halves,
    Listing8PointerCopies.halfCount,Nat.add_assoc]

theorem bytes_length (mode : Mode) (l : Layout) : (bytes mode l).length = if mode = .x86 then 47 else 96 := by
  cases mode <;> simp [bytes,helpers,Listing8PointerCopies.split,DwordMixedSequence.bytes,DwordMixedImage.bytes_length,
    DwordPackets.bytes_length,packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,DwordLayout.span,DwordLayout.storeSize]

end SmcTuring.Appendix.Listing8StateLayout
