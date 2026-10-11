module
public import SmcTuring.Native.StringFetchRequests

public section
namespace SmcTuring.Native.StringMixedRequests
open LittleEndian StringFetchRequests

theorem header (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc count : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet)
    (small : count≤3) : ByteMemory.bytesAt memory pc count=(bytes mode packet).take count := by
  rw [←Fetch.bytes_at_take memory pc (bytes mode packet).length count (by have enough:=packet_minimum mode packet;omega),current]

theorem string_count (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc count : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet)
    (classified : StringForm.lengthOfBytes mode (ByteMemory.bytesAt memory pc 3)=some count) :
    count≤(bytes mode packet).length := by
  rw [header mode packet memory pc 3 current (by decide)] at classified
  exact packet_string_count mode packet count classified

/-- The mixed decoder's own header, repeated arithmetic header, bare-copy
probe, and optional REX/native probe all fit the actual auxiliary packet. -/
theorem mixed_counts (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet) :
    ∀ count∈mixed mode memory pc,count≤(bytes mode packet).length := by
  have three:=header mode packet memory pc 3 current (by decide)
  have two:=header mode packet memory pc 2 current (by decide)
  have first:=congrArg (fun values : List Byte=>values[0]?) three
  change some (memory pc)=((bytes mode packet).take 3)[0]? at first
  intro count member
  unfold mixed arithmetic copy native at member
  rw [two,three] at member
  cases mode <;> cases packet
  all_goals try cases ‹MixedDword.Form _›
  all_goals try cases ‹DwordArithmetic.Form›
  all_goals try cases ‹DwordCode.Form _›
  all_goals
    dsimp [bytes,MixedDword.encode,DwordArithmetic.encode,DwordCode.encode,Native.encode,
      DwordXor.encode,WordNegation.encode,WordAddImmediate.encode,wordPrefix,MemoryOp.prefix,MemoryOp.tag] at first member
    simp at first
    simp [first,DwordArithmetic.packetSize,DwordCode.packetSize,selected,Fetch.lengthOfBytes,Fetch.coreLength,
      operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes] at member
    simp [bytes,MixedDword.encode_length,MixedDword.length,DwordArithmetic.length,DwordCode.length,
      WordNegation.encode_length,WordNegation.length,WordAddImmediate.encode_length,WordAddImmediate.length,
      DwordXor.encode,wordPrefix,Mode.wordBytes]
    omega

end SmcTuring.Native.StringMixedRequests
