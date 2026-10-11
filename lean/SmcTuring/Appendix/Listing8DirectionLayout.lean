module
public import SmcTuring.Native.DwordPackets
public import SmcTuring.Appendix.Listing8PointerCopies

public section
namespace SmcTuring.Appendix.Listing8DirectionLayout
open Native
abbrev Dword := BitVec 32
structure Layout where
  start : Nat
  cursor : Nat
@[expose] def halves (mode : Mode) := Listing8PointerCopies.halfCount mode
@[expose] def duplicateSpan (mode : Mode) := if mode = .x86 then 0 else DwordLayout.span mode
@[expose] def copyStart (mode : Mode) (l : Layout) := l.start+duplicateSpan mode
@[expose] def backPC (mode : Mode) (l : Layout) := copyStart mode l+halves mode*DwordLayout.span mode
@[expose] def notPC (mode : Mode) (l : Layout) := backPC mode l+halves mode*10
@[expose] def forwardPC (mode : Mode) (l : Layout) := notPC mode l+halves mode*6
@[expose] def combinedPC (mode : Mode) (l : Layout) := forwardPC mode l+halves mode*10
@[expose] def selectionEnd (mode : Mode) (l : Layout) := combinedPC mode l+halves mode*10
@[expose] def maskPC (mode : Mode) (l : Layout) := selectionEnd mode l+halves mode*18
@[expose] def directionPC (mode : Mode) (l : Layout) := maskPC mode l+halves mode*10
@[expose] def endPC (mode : Mode) (l : Layout) := directionPC mode l+halves mode*10
@[expose] def duplicate (mode : Mode) (l : Layout) : List DwordLayout.Layout :=
  match mode with
  | .x86 => []
  | .x64 => [⟨l.start,directionPC mode l+6,directionPC mode l+16⟩]
@[expose] def copy (mode : Mode) (l : Layout) : List DwordLayout.Layout :=
  match mode with
  | .x86 => [⟨copyStart mode l,directionPC mode l+6,combinedPC mode l+6⟩]
  | .x64 => [⟨copyStart mode l,directionPC mode l+6,combinedPC mode l+6⟩,
      ⟨copyStart mode l+DwordLayout.span mode,directionPC mode l+16,combinedPC mode l+16⟩]
@[expose] def helpers (mode : Mode) (l : Layout) := duplicate mode l ++ copy mode l
@[expose] def group (mode : Mode) (pc stride target : Nat) (op : DwordPackets.Operation) : List DwordPackets.Site :=
  match mode with
  | .x86 => [⟨pc,op,target⟩]
  | .x64 => [⟨pc,op,target⟩,⟨pc+stride,op,target+10⟩]
@[expose] def arithmetic (mode : Mode) (l : Layout) :=
  group mode (backPC mode l) 10 (combinedPC mode l+6) .bitAnd ++
  group mode (notPC mode l) 6 (directionPC mode l+6) .complement ++
  group mode (forwardPC mode l) 10 (directionPC mode l+6) .bitAnd ++
  group mode (combinedPC mode l) 10 (directionPC mode l+6) .bitOr
@[expose] def masks (mode : Mode) (l : Layout) := group mode (maskPC mode l) 10 (directionPC mode l+6) .bitAnd
/-- The final two XOR packets address adjacent pointer halves, not packet-stride halves. -/
@[expose] def heads (mode : Mode) (l : Layout) : List DwordPackets.Site :=
  match mode with
  | .x86 => [⟨directionPC mode l,.bitXor,l.cursor⟩]
  | .x64 => [⟨directionPC mode l,.bitXor,l.cursor⟩,⟨directionPC mode l+10,.bitXor,l.cursor+4⟩]
@[expose] def differenceBytes (mode : Mode) (pc source target : Nat) :=
  Native.encode .x86 (.memory .exchangeAcc (Relocation.memoryDisp mode (pc+6) source)) ++
  Native.encode .x86 (.memory .bitXor (Relocation.memoryDisp mode (pc+12) target)) ++
  Native.encode .x86 (.memory .exchangeAcc (Relocation.memoryDisp mode (pc+18) source))
@[expose] def differences (mode : Mode) (l : Layout) :=
  differenceBytes mode (selectionEnd mode l) l.cursor (directionPC mode l+6) ++
    (if mode = .x86 then [] else
      differenceBytes mode (selectionEnd mode l+18) (l.cursor+4) (directionPC mode l+16))
@[expose] def force : Dword := 0x80000000
@[expose] def packets (mode : Mode) (sites : List DwordPackets.Site) :=
  DwordPackets.bytes mode sites force
@[expose] def bytes (mode : Mode) (l : Layout) :=
  DwordMixedSequence.bytes mode (helpers mode l) ++ packets mode (arithmetic mode l) ++
    differences mode l ++ packets mode (masks mode l) ++ packets mode (heads mode l)

theorem helper_chain (mode : Mode) (l : Layout) :
    StringDwordSequence.Contiguous mode l.start (helpers mode l) := by
  cases mode <;> simp [helpers,duplicate,copy,copyStart,duplicateSpan,DwordMixedSequence.Contiguous,
    DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,DwordLayout.span,Nat.add_assoc]

theorem arithmetic_chain (mode : Mode) (l : Layout) :
    DwordPackets.Contiguous (backPC mode l) (arithmetic mode l) := by
  cases mode <;> simp [arithmetic,group,DwordPackets.Contiguous,DwordPackets.size,DwordPackets.raw,
    DwordArithmetic.length,notPC,forwardPC,combinedPC,halves,Listing8PointerCopies.halfCount,Nat.add_assoc]

theorem positions (mode : Mode) (l : Layout) :
    backPC mode l = l.start+(if mode = .x86 then 17 else 54) ∧
    notPC mode l = l.start+(if mode = .x86 then 27 else 74) ∧
    forwardPC mode l = l.start+(if mode = .x86 then 33 else 86) ∧
    combinedPC mode l = l.start+(if mode = .x86 then 43 else 106) ∧
    selectionEnd mode l = l.start+(if mode = .x86 then 53 else 126) ∧
    maskPC mode l = l.start+(if mode = .x86 then 71 else 162) ∧
    directionPC mode l = l.start+(if mode = .x86 then 81 else 182) ∧
    endPC mode l = l.start+(if mode = .x86 then 91 else 202) := by
  cases mode <;> simp [backPC,notPC,forwardPC,combinedPC,selectionEnd,maskPC,directionPC,endPC,
    copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem helpers_length (mode : Mode) (l : Layout) :
    (helpers mode l).length = if mode = .x86 then 1 else 3 := by cases mode <;> rfl

theorem arithmetic_length (mode : Mode) (l : Layout) :
    (arithmetic mode l).length = if mode = .x86 then 4 else 8 := by cases mode <;> rfl

theorem packet_lengths (mode : Mode) (sites : List DwordPackets.Site) :
    (packets mode sites).length = (sites.map DwordPackets.size).sum :=
  DwordPackets.bytes_length mode sites force

theorem bytes_length (mode : Mode) (l : Layout) :
    (bytes mode l).length = if mode = .x86 then 91 else 202 := by
  simp only [bytes,List.length_append,packet_lengths,DwordMixedSequence.bytes,List.length_flatMap]
  cases mode <;> simp [helpers,duplicate,copy,arithmetic,masks,heads,group,differences,differenceBytes,
    DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,DwordMixedImage.bytes_length,
    DwordLayout.span,DwordLayout.storeSize,Native.encode,MemoryOp.prefix,MemoryOp.tag,MemoryOp.trailer,wordPrefix]

end SmcTuring.Appendix.Listing8DirectionLayout
