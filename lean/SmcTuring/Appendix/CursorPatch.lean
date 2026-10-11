module
public import SmcTuring.Appendix.CursorImage
public import SmcTuring.Native.BytePatch

public section
namespace SmcTuring.Appendix.CursorPatch
open Native CursorLayout
@[expose] def field (mode : Mode) (layout : Layout) : Nat := middlePC mode layout+3
@[expose] def leading (mode : Mode) (layout : Layout) : List LittleEndian.Byte :=
  MixedDword.encode mode (first mode layout) ++ [0x81,0x70,6]

theorem spelling (mode : Mode) (layout : Layout) (value : BitVec 32) :
    CursorImage.bytes mode layout value =
      leading mode layout ++ LittleEndian.wordEncode 4 value ++ MixedDword.encode mode (last mode layout) := by
  simp only [CursorImage.bytes,leading,middle,MixedDword.encode,DwordArithmetic.encode,List.append_assoc]

theorem leading_length (mode : Mode) (layout : Layout) :
    (leading mode layout).length = exchangeSize mode+3 := by
  simp only [leading,List.length_append,List.length_cons,List.length_nil,MixedDword.encode_length]
  rw [(lengths mode layout 0).1]

theorem current (mode : Mode) (layout : Layout) (old fresh : BitVec 32) (memory : ByteMemory.Memory)
    (intact : CursorImage.Intact mode layout old memory) :
    CursorImage.Intact mode layout fresh (DwordCode.put memory (field mode layout) fresh) := by
  have initialized : ByteMemory.bytesAt memory layout.start
      (leading mode layout ++ LittleEndian.wordEncode 4 old ++ MixedDword.encode mode (last mode layout)).length =
      leading mode layout ++ LittleEndian.wordEncode 4 old ++ MixedDword.encode mode (last mode layout) := by
    rw [←spelling,CursorImage.length]
    exact intact
  have patched := BytePatch.current memory layout.start (leading mode layout)
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 fresh)
    (MixedDword.encode mode (last mode layout)) (by simp) initialized
  have position : layout.start+(leading mode layout).length = field mode layout := by
    rw [leading_length,field,middlePC]
    omega
  rw [position,←spelling,CursorImage.length] at patched
  exact patched

theorem operand (mode : Mode) (layout : Layout) (value : BitVec 32) (memory : ByteMemory.Memory)
    (intact : CursorImage.Intact mode layout value memory) :
    DwordCode.get memory (field mode layout) = value := by
  have packet := CursorImage.middle_current mode layout value memory intact
  have current : ByteMemory.bytesAt memory (middlePC mode layout) 7 =
      [0x81,0x70,6] ++ LittleEndian.wordEncode 4 value := packet
  have selected := ByteWindow.packet memory (middlePC mode layout) [0x81,0x70,6]
    (LittleEndian.wordEncode 4 value) [] (by simpa using current)
  have window : ByteMemory.bytesAt memory (field mode layout) 4 = LittleEndian.wordEncode 4 value := by
    simpa only [LittleEndian.word_encode_length,List.length_cons,List.length_nil,field] using selected
  have restored := DwordCode.get_put memory (field mode layout) value
  have written : ByteMemory.bytesAt
      (ByteMemory.putBytes memory (field mode layout) (LittleEndian.wordEncode 4 value))
      (field mode layout) 4 = LittleEndian.wordEncode 4 value := by
    simpa only [LittleEndian.word_encode_length] using
      ByteMemory.bytes_at_put memory (field mode layout) (LittleEndian.wordEncode 4 value)
  rw [DwordCode.get,DwordCode.put,written] at restored
  simpa only [DwordCode.get,window] using restored

end SmcTuring.Appendix.CursorPatch
