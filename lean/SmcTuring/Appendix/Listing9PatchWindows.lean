module
public import SmcTuring.Appendix.Listing9SelfDeclaration

public section
namespace SmcTuring.Appendix.Listing9PatchWindows
open Native

theorem patch_window (first second : ByteMemory.Memory) (written : Nat) (bytes : List LittleEndian.Byte)
    (observed count : Nat) (same : ByteMemory.bytesAt first observed count=ByteMemory.bytesAt second observed count) :
    ByteMemory.bytesAt (ByteMemory.putBytes first written bytes) observed count=
      ByteMemory.bytesAt (ByteMemory.putBytes second written bytes) observed count := by
  apply congrArg List.ofFn
  funext index
  apply Listing8LoopOriginalImage.patch_point
  have value:=congrArg (fun values : List LittleEndian.Byte => values[index.val]?) same
  simp only [ByteMemory.bytesAt,List.getElem?_ofFn,index.isLt,dite_eq_left] at value
  exact Option.some.inj value

theorem overwrite (memory : ByteMemory.Memory) (written : Nat) (old fresh : List LittleEndian.Byte)
    (width : old.length=fresh.length) :
    ByteMemory.putBytes (ByteMemory.putBytes memory written old) written fresh=ByteMemory.putBytes memory written fresh := by
  funext position
  by_cases inside : ByteMemory.Inside written fresh.length position
  · simp only [ByteMemory.putBytes,dite_eq_left inside]
  · have previous : ¬ByteMemory.Inside written old.length position := by rw [width];exact inside
    simp only [ByteMemory.putBytes,dite_eq_right inside,dite_eq_right previous]

theorem word_overwrite (mode : Mode) (memory : ByteMemory.Memory) (field : Nat) (old fresh : Word mode) :
    ByteMemory.putWord mode (ByteMemory.putWord mode memory field old) field fresh=ByteMemory.putWord mode memory field fresh :=
  overwrite memory field _ _ (by rw [LittleEndian.word_encode_length,LittleEndian.word_encode_length])

end SmcTuring.Appendix.Listing9PatchWindows
