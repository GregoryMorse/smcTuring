module
public import SmcTuring.Native.DwordPackets

public section
namespace SmcTuring.Native.DwordOperands

theorem shape (mode : Mode) (site : DwordPackets.Site) (value : BitVec 32)
    (binary : site.operation ≠ .complement) :
    DwordArithmetic.encode (DwordPackets.form mode site value)=DwordPackets.header mode site++LittleEndian.wordEncode 4 value := by
  cases site with
  | mk pc op target =>
    cases op <;> try rfl
    exact False.elim (binary rfl)

theorem value (mode : Mode) (site : DwordPackets.Site) (payload : BitVec 32) (memory : ByteMemory.Memory)
    (binary : site.operation ≠ .complement)
    (current : ByteMemory.bytesAt memory site.pc (DwordArithmetic.encode (DwordPackets.form mode site payload)).length=
      DwordArithmetic.encode (DwordPackets.form mode site payload)) :
    DwordCode.get memory (site.pc+6)=payload := by
  have packet:=ByteWindow.packet memory site.pc (DwordPackets.header mode site) (LittleEndian.wordEncode 4 payload) []
    (by simpa only [List.append_nil,←shape mode site payload binary] using current)
  rw [DwordPackets.header_length,LittleEndian.word_encode_length] at packet
  have decoded : ByteMemory.readWord .x86 memory (site.pc+6)=some payload := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (site.pc+6) 4)=some payload
    rw [packet,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

end SmcTuring.Native.DwordOperands
