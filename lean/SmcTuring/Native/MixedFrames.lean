module
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.DwordDataflow

public section
namespace SmcTuring.Native.MixedFrames

theorem word_after_word (mode : Mode) (memory : ByteMemory.Memory) (written observed : Nat) (value : Word mode)
    (separate : written+mode.wordBytes ≤ observed ∨ observed+mode.wordBytes ≤ written) :
    MixedMemory.getWord mode (ByteMemory.putWord mode memory written value) observed = MixedMemory.getWord mode memory observed := by
  have frame := ByteMemory.bytes_at_frame memory written (LittleEndian.wordEncode mode.wordBytes value) observed mode.wordBytes (by
    intro index;have bound:=index.isLt
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    rcases separate with before | after <;> omega)
  exact congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) frame

theorem word_after_dword (mode : Mode) (memory : ByteMemory.Memory) (written observed : Nat) (value : BitVec 32)
    (separate : written+4 ≤ observed ∨ observed+mode.wordBytes ≤ written) :
    MixedMemory.getWord mode (DwordCode.put memory written value) observed = MixedMemory.getWord mode memory observed := by
  apply MixedMemory.wide_after_dword
  intro index;have bound:=index.isLt
  simp only [ByteMemory.Inside]
  rcases separate with before | after <;> omega

theorem words_commute (mode : Mode) (memory : ByteMemory.Memory) (first second : Nat) (a b : Word mode)
    (separate : first+mode.wordBytes ≤ second ∨ second+mode.wordBytes ≤ first) :
    ByteMemory.putWord mode (ByteMemory.putWord mode memory first a) second b =
      ByteMemory.putWord mode (ByteMemory.putWord mode memory second b) first a := by
  apply Writes.put_words_commute
  intro index;have bound:=index.isLt
  simp only [ByteMemory.Inside]
  rcases separate with before | after <;> omega

theorem sub_zero (mode : Mode) (a b : Word mode) : a-b=0 ↔ a=b := by
  constructor
  · intro equal
    have back:=BitVec.sub_add_cancel a b
    rw [equal] at back
    exact ((BitVec.zero_add b).symm.trans back).symm
  · intro equal;rw [equal,BitVec.sub_self];rfl

theorem restored_pair (mode : Mode) (memory : ByteMemory.Memory) (source cursor : Nat) (temporary : Word mode)
    (separate : cursor+mode.wordBytes ≤ source ∨ source+mode.wordBytes ≤ cursor) :
    ByteMemory.putWord mode
      (ByteMemory.putWord mode (ByteMemory.putWord mode memory source temporary) cursor (MixedMemory.getWord mode memory cursor))
      source (MixedMemory.getWord mode memory source) = memory := by
  rw [words_commute mode memory source cursor temporary _ (Or.symm separate),Writes.put_word_overwrite,
    MixedMemory.put_get_back,MixedMemory.put_get_back]

end SmcTuring.Native.MixedFrames
