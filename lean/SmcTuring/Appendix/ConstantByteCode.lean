module
public import SmcTuring.Appendix.MultiplyByteCode

public section
namespace SmcTuring.Appendix.ConstantByteCode

open Native.LittleEndian
abbrev Word := MultiplyByteCode.Word
abbrev Memory := MultiplyByteCode.Memory
/-- Actual counts 1..31. The emitter omits zero-count SHLs; arbitrary other
    C1 counts are outside this selected codec rather than assigned a write. -/
abbrev Count := Fin 31

inductive Form where
  | common (form : MultiplyByteCode.Form)
  | shiftImmediate (address : Word) (count : Count)
  deriving DecidableEq, Repr

@[expose] def encode : Form -> List Byte
  | .common form => MultiplyByteCode.encode form
  | .shiftImmediate address count =>
      ([0xc1, 0x25] ++ wordEncode 4 address) ++ [BitVec.ofNat 8 (count.val + 1)]

@[expose] def decodeShift (payload : List Byte) : Option Form :=
  match payload.drop 4 with
  | [count] =>
      if legal : 0 < count.toNat ∧ count.toNat < 32 then do
        let address ← wordDecode 4 (payload.take 4)
        return .shiftImmediate address ⟨count.toNat - 1, by omega⟩
      else none
  | _ => none

@[expose] def decode (bytes : List Byte) : Option Form :=
  match bytes with
  | opcode :: rest =>
      if opcode = 0xc1 then match rest with
        | modrm :: payload =>
            if modrm = 0x25 then decodeShift payload
            else (MultiplyByteCode.decode bytes).map Form.common
        | [] => (MultiplyByteCode.decode bytes).map Form.common
      else (MultiplyByteCode.decode bytes).map Form.common
  | [] => (MultiplyByteCode.decode bytes).map Form.common

theorem count_byte (count : Count) : (BitVec.ofNat 8 (count.val + 1)).toNat = count.val + 1 := by
  have below : count.val + 1 < 256 := by have h := count.isLt; omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]

theorem count_bounds (count : Count) : 0 < count.val + 1 ∧ count.val + 1 < 32 := by
  have h := count.isLt
  omega

@[simp] theorem shift_payload (address : Word) (count : Count) :
    decodeShift (wordEncode 4 address ++ [BitVec.ofNat 8 (count.val + 1)]) =
      some (.shiftImmediate address count) := by
  have taken : (wordEncode 4 address ++ [BitVec.ofNat 8 (count.val + 1)]).take 4 = wordEncode 4 address := rfl
  have dropped : (wordEncode 4 address ++ [BitVec.ofNat 8 (count.val + 1)]).drop 4 = [BitVec.ofNat 8 (count.val + 1)] := rfl
  simp only [decodeShift, taken, dropped, count_byte]
  rw [dite_eq_left (count_bounds count), word_decode_encode]
  simp

@[simp] theorem common_decode (form : MultiplyByteCode.Form) :
    decode (MultiplyByteCode.encode form) = some (.common form) := by
  cases form with
  | common form => cases form with
    | immediate op address value => cases op <;>
        simp [decode, ByteCode.encode, MultiplyByteCode.encode, ByteCode.ImmediateOp.tag,
          MultiplyByteCode.decode, MultiplyByteCode.operationOfTag, ByteCode.decode, ByteCode.immediateOfTag]
    | memory op address => cases op <;>
        simp [decode, ByteCode.encode, MultiplyByteCode.encode, ByteCode.MemoryOp.tag,
          MultiplyByteCode.decode, MultiplyByteCode.operationOfTag, ByteCode.decode,
          ByteCode.immediateOfTag, ByteCode.memoryOfTag]
    | storeAcc address => simp [decode, ByteCode.encode, MultiplyByteCode.encode,
        MultiplyByteCode.decode, ByteCode.decode]
    | callRelative value => simp [decode, ByteCode.encode, MultiplyByteCode.encode,
        MultiplyByteCode.decode, ByteCode.decode]
  | andAcc address => simp [decode, MultiplyByteCode.encode, MultiplyByteCode.decode,
      MultiplyByteCode.operationOfTag, MultiplyByteCode.decodePayload]
  | addImmediate address value => simp [decode, MultiplyByteCode.encode, MultiplyByteCode.decode,
      MultiplyByteCode.operationOfTag]
  | shiftLeft address => simp [decode, MultiplyByteCode.encode, MultiplyByteCode.decode,
      MultiplyByteCode.operationOfTag, MultiplyByteCode.decodePayload]
  | shiftRight address => simp [decode, MultiplyByteCode.encode, MultiplyByteCode.decode,
      MultiplyByteCode.operationOfTag, MultiplyByteCode.decodePayload]

theorem form_roundtrip (form : Form) : decode (encode form) = some form := by
  cases form with
  | common form => exact common_decode form
  | shiftImmediate address count => simp [encode, decode]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [form_roundtrip, Option.some.injEq] using decoded

@[expose] def instructionLength : Form -> Nat
  | .common form => MultiplyByteCode.instructionLength form
  | .shiftImmediate _ _ => 7

theorem encode_length (form : Form) : (encode form).length = instructionLength form := by
  cases form <;> simp [encode, instructionLength, MultiplyByteCode.encode_length]

theorem length_bounds (form : Form) : 2 ≤ instructionLength form ∧ instructionLength form ≤ 10 := by
  cases form with
  | common form => exact MultiplyByteCode.length_bounds form
  | shiftImmediate => simp [instructionLength]

@[expose] def lengthOfBytes (bytes : List Byte) : Option Nat :=
  match bytes with
  | opcode :: rest =>
      if opcode = 0xc1 then match rest with
        | modrm :: _ => if modrm = 0x25 then some 7 else MultiplyByteCode.lengthOfBytes bytes
        | [] => MultiplyByteCode.lengthOfBytes bytes
      else MultiplyByteCode.lengthOfBytes bytes
  | [] => MultiplyByteCode.lengthOfBytes bytes

theorem common_length (form : MultiplyByteCode.Form) (trailing : List Byte) :
    lengthOfBytes (MultiplyByteCode.encode form ++ trailing) = some (MultiplyByteCode.instructionLength form) := by
  have same : lengthOfBytes (MultiplyByteCode.encode form ++ trailing) =
      MultiplyByteCode.lengthOfBytes (MultiplyByteCode.encode form ++ trailing) := by
    cases form with
    | common form => cases form with
      | immediate op address value => cases op <;> rfl
      | memory op address => cases op <;> rfl
      | storeAcc => rfl
      | callRelative => rfl
    | _ => rfl
  rw [same]
  exact MultiplyByteCode.encoded_length form trailing

theorem encoded_length (form : Form) (trailing : List Byte) :
    lengthOfBytes (encode form ++ trailing) = some (instructionLength form) := by
  cases form with
  | common form => exact common_length form trailing
  | shiftImmediate address count => rfl

theorem length_take_two (bytes : List Byte) : lengthOfBytes (bytes.take 2) = lengthOfBytes bytes := by
  cases bytes with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second tail => rfl

@[expose] def fetch (memory : Memory) (pc : Nat) : Option Form :=
  (lengthOfBytes (Native.ByteMemory.bytesAt memory pc 2)).bind fun length =>
    decode (Native.ByteMemory.bytesAt memory pc length)

theorem fetch_current_encoding (memory : Memory) (pc : Nat) (form : Form)
    (current : Native.ByteMemory.bytesAt memory pc (encode form).length = encode form) :
    fetch memory pc = some form := by
  have bound : 2 ≤ (encode form).length := by rw [encode_length]; exact (length_bounds form).1
  have header : lengthOfBytes (Native.ByteMemory.bytesAt memory pc 2) = some (instructionLength form) := by
    rw [←Native.Fetch.bytes_at_take memory pc (encode form).length 2 bound, current, length_take_two]
    simpa only [List.append_nil] using encoded_length form []
  unfold fetch
  rw [header, Option.bind_some, ←encode_length, current, form_roundtrip]

theorem fetch_written_encoding (memory : Memory) (pc : Nat) (form : Form) :
    fetch (Native.ByteMemory.putBytes memory pc (encode form)) pc = some form :=
  fetch_current_encoding _ pc form (Native.ByteMemory.bytes_at_put memory pc (encode form))

theorem fetch_patched_current_add (memory : Memory) (pc : Nat) (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.common (.addImmediate address old))).length =
      encode (.common (.addImmediate address old))) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 6) fresh) pc =
      some (.common (.addImmediate address fresh)) := by
  change Native.ByteMemory.bytesAt memory pc (MultiplyByteCode.encode (.addImmediate address old)).length =
    MultiplyByteCode.encode (.addImmediate address old) at current
  have back : Native.ByteMemory.putBytes memory pc (MultiplyByteCode.encode (.addImmediate address old)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back, MultiplyByteCode.add_patch]
  exact fetch_written_encoding memory pc (.common (.addImmediate address fresh))

end SmcTuring.Appendix.ConstantByteCode
