module
public import SmcTuring.Native.StringStackImage

public section
namespace SmcTuring.Native.StringFetchRequests
open LittleEndian

@[expose] def selected : Option Nat→List Nat
  | none => []
  | some count => [count]
@[expose] def native (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  3::selected (Fetch.lengthOfBytes mode (ByteMemory.bytesAt memory pc 3))
@[expose] def string (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  3::selected (StringForm.lengthOfBytes mode (ByteMemory.bytesAt memory pc 3))
@[expose] def arithmetic (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  2::selected (DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2))
@[expose] def copy (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  [1,DwordCode.packetSize mode (memory pc)]
@[expose] def mixed (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  2::(match DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) with
    | some _ => arithmetic memory pc
    | none => match mode with
      | .x86 => copy .x86 memory pc
      | .x64 => 1::(if memory pc=0x48 then native .x64 memory pc else [DwordCode.packetSize .x64 (memory pc)]))
@[expose] def dword (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  string mode memory pc++(match StringForm.fetch mode memory pc with
    | some _ => []
    | none => mixed mode memory pc++(match MixedDword.fetch mode memory pc with
      | some _ => []
      | none => [6]))
@[expose] def control (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  dword mode memory pc++(match StringDword.fetch mode memory pc with
    | some _ => []
    | none => [WordNegation.length mode])
/-- Exact classifier and packet read widths, in call order, including failed
fallback decoders and repeated headers. Every request begins at the current PC. -/
@[expose] def requests (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : List Nat :=
  control mode memory pc++(match StringControl.fetch mode memory pc with
    | some _ => []
    | none => [WordAddImmediate.length mode])

inductive Packet (mode : Mode) where
  | mixed (form : MixedDword.Form mode)
  | xor (d : BitVec 32)
  | negation (d : BitVec 32)
  | addition (d : BitVec 32) (v : Byte)
@[expose] def bytes (mode : Mode) : Packet mode→List Byte
  | .mixed form => MixedDword.encode mode form
  | .xor d => DwordXor.encode d
  | .negation d => WordNegation.encode mode d
  | .addition d v => WordAddImmediate.encode mode d v

theorem packet_minimum (mode : Mode) (packet : Packet mode) : 3≤(bytes mode packet).length := by
  cases packet with
  | mixed form =>
    rw [bytes,MixedDword.encode_length]
    cases form with
    | arithmetic form => cases form <;> simp [MixedDword.length,DwordArithmetic.length]
    | copy form => cases mode <;> cases form <;> simp [MixedDword.length,DwordCode.length,Mode.wordBytes]
    | wideExchange => simp [MixedDword.length]
  | xor => simp [bytes,DwordXor.encode]
  | negation => cases mode <;> simp [bytes,WordNegation.encode,wordPrefix]
  | addition => cases mode <;> simp [bytes,WordAddImmediate.encode,wordPrefix]

/-- All auxiliary packet headers bound even an earlier unsuccessful string
classifier. Payload bytes do not enlarge the selected request. -/
theorem packet_string_count (mode : Mode) (packet : Packet mode) (count : Nat)
    (classified : StringForm.lengthOfBytes mode ((bytes mode packet).take 3)=some count) :
    count≤(bytes mode packet).length := by
  cases packet with
  | mixed form =>
    cases form with
    | arithmetic form =>
      cases mode <;> cases form <;>
        simp [bytes,MixedDword.encode,DwordArithmetic.encode,StringForm.lengthOfBytes,StringForm.extraLength,
          StringForm.headerLength,StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,
          operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix] at classified ⊢ <;> omega
    | copy form =>
      change count≤(DwordCode.encode mode form).length
      rw [DwordCode.encode_length]
      cases mode <;> cases form <;>
        simp [bytes,MixedDword.encode,DwordCode.encode,DwordCode.length,StringForm.lengthOfBytes,StringForm.extraLength,
          StringForm.headerLength,StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,
          operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes] at classified ⊢ <;> first | omega | (unfold StringForm.coreLength at classified; simp at classified; omega)
    | wideExchange =>
      simp [bytes,MixedDword.encode,Native.encode,StringForm.lengthOfBytes,StringForm.extraLength,
        StringForm.headerLength,StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,
        operationOfTag,MemoryOp.prefix,MemoryOp.trailer,MemoryOp.tag,wordPrefix] at classified ⊢
      omega
  | xor =>
    cases mode <;>
      simp [bytes,DwordXor.encode,StringForm.lengthOfBytes,StringForm.extraLength,StringForm.headerLength,
        StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix] at classified ⊢ <;> omega
  | negation =>
    cases mode <;>
      simp [bytes,WordNegation.encode,StringForm.lengthOfBytes,StringForm.extraLength,StringForm.headerLength,
        StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix] at classified ⊢ <;> omega
  | addition =>
    cases mode <;>
      simp [bytes,WordAddImmediate.encode,StringForm.lengthOfBytes,StringForm.extraLength,StringForm.headerLength,
        StringForm.coreLength,Fetch.lengthOfBytes,Fetch.coreLength,operationOfTag,MemoryOp.prefix,MemoryOp.trailer,wordPrefix] at classified ⊢ <;> omega

end SmcTuring.Native.StringFetchRequests
