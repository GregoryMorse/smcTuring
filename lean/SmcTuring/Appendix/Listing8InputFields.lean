module
public import SmcTuring.Appendix.Listing8InputMask

public section
namespace SmcTuring.Appendix.Listing8InputFields
open Native Listing8LiteralInput
abbrev Dword := BitVec 32

@[expose] def beforeTape (mode : Mode) (l : Layout) (rule : Dword) :=
  DwordArithmetic.encode (resetForm mode l) ++ DwordMixedImage.bytes mode (copyLayout mode l) ++
    DwordArithmetic.encode (ownerForm mode l rule) ++ [0x81,0x2d] ++
    LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (ownerPC mode l+20) (scalarField mode l))
@[expose] def afterTape (mode : Mode) (l : Layout) (pending fresh oldMask : Dword) :=
  DwordArithmetic.encode (DwordArithmetic.located mode (.negate 0) (ownerPC mode l+20) (scalarField mode l)) ++
    DwordArithmetic.encode (DwordArithmetic.located mode (.sbbZero 0) (ownerPC mode l+26) (maskField mode l)) ++
    DwordArithmetic.encode (DwordArithmetic.located mode (.complement 0) (ownerPC mode l+33) (maskField mode l)) ++
    distributionBytes mode l ++ DwordArithmetic.encode (InputUpdate.xorForm mode (updateLayout mode l) fresh) ++
    [0x81,0x25] ++ LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode l+20) (pendingField mode l)) ++
    LittleEndian.wordEncode 4 oldMask ++ Listing8InputMask.trailing mode l pending

theorem tape_spelling (mode : Mode) (l : Layout) (rule tape pending fresh oldMask : Dword) :
    Listing8InputMask.bytes mode l rule tape pending fresh oldMask =
      beforeTape mode l rule ++ LittleEndian.wordEncode 4 tape ++ afterTape mode l pending fresh oldMask := by
  simp [Listing8InputMask.bytes,Listing8InputMask.leading,beforeTape,afterTape,prefixBytes,
    DwordComparisonTail.bytes,DwordComparisonTail.form,DwordComparisonTail.raw,DwordComparisonTail.offset,
    DwordComparisonTail.target,tailLayout,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,DwordArithmetic.encode,List.append_assoc,Nat.add_assoc]

theorem tape_position (mode : Mode) (l : Layout) (rule : Dword) :
    l.start+(beforeTape mode l rule).length = sourceField mode l := by
  simp only [beforeTape,List.length_append,DwordArithmetic.encode_length,resetForm,ownerForm,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,DwordMixedImage.bytes_length,
    List.length_cons,List.length_nil,LittleEndian.word_encode_length]
  unfold sourceField ownerPC copyStart
  omega

/-- A live tape-owner store patches only the SUB immediate while retaining
the entire input region, including its arbitrary old AND mask. -/
theorem tape_patch (mode : Mode) (l : Layout) (rule old fresh pending newSymbol oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode l rule old pending newSymbol oldMask memory) :
    Listing8InputMask.Intact mode l rule fresh pending newSymbol oldMask (DwordCode.put memory (sourceField mode l) fresh) := by
  have initial : ByteMemory.bytesAt memory l.start
      (beforeTape mode l rule ++ LittleEndian.wordEncode 4 old ++ afterTape mode l pending newSymbol oldMask).length =
      beforeTape mode l rule ++ LittleEndian.wordEncode 4 old ++ afterTape mode l pending newSymbol oldMask := by
    rw [←tape_spelling]
    exact current
  have patched := BytePatch.current memory l.start (beforeTape mode l rule)
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 fresh) (afterTape mode l pending newSymbol oldMask)
    (by simp only [LittleEndian.word_encode_length]) initial
  rw [tape_position,←tape_spelling] at patched
  exact patched

end SmcTuring.Appendix.Listing8InputFields
