module
public import SmcTuring.Appendix.ByteCode

public section

namespace SmcTuring.Appendix.MultiplyByteCode

open Native.LittleEndian
abbrev Word := ByteCode.Word
abbrev Memory := ByteCode.Memory

/-- The four additional literal DWORD forms in Listing 11. -/
inductive Operation where
  | andAcc | addImmediate | shiftLeft | shiftRight
  deriving DecidableEq, Repr

@[expose] def operationOfTag (opcode modrm : Byte) : Option Operation :=
  match opcode.toNat, modrm.toNat with
  | 0x21, 0x05 => some .andAcc
  | 0x81, 0x05 => some .addImmediate
  | 0xd1, 0x25 => some .shiftLeft
  | 0xd1, 0x2d => some .shiftRight
  | _, _ => none

inductive Form where
  | common (form : ByteCode.Form)
  | andAcc (address : Word)
  | addImmediate (address value : Word)
  | shiftLeft (address : Word)
  | shiftRight (address : Word)
  deriving DecidableEq, Repr

@[expose] def encode : Form → List Byte
  | .common form => ByteCode.encode form
  | .andAcc address => [0x21, 0x05] ++ wordEncode 4 address
  | .addImmediate address value => ([0x81, 0x05] ++ wordEncode 4 address) ++ wordEncode 4 value
  | .shiftLeft address => [0xd1, 0x25] ++ wordEncode 4 address
  | .shiftRight address => [0xd1, 0x2d] ++ wordEncode 4 address

@[expose] def decodePayload (op : Operation) (payload : List Byte) : Option Form :=
  match op with
  | .addImmediate => do
      let address ← wordDecode 4 (payload.take 4)
      let value ← wordDecode 4 (payload.drop 4)
      return .addImmediate address value
  | .andAcc => (wordDecode 4 payload).map Form.andAcc
  | .shiftLeft => (wordDecode 4 payload).map Form.shiftLeft
  | .shiftRight => (wordDecode 4 payload).map Form.shiftRight

/-- Existing branch forms keep their exact decoder. D1 shifts have implicit
count one; no count byte is accepted by these selected forms. -/
@[expose] def decode (bytes : List Byte) : Option Form :=
  match bytes with
  | [] => none
  | opcode :: rest =>
    if opcode = 0xa3 ∨ opcode = 0xe8 then (ByteCode.decode bytes).map Form.common
    else match rest with
      | [] => (ByteCode.decode bytes).map Form.common
      | modrm :: payload => match operationOfTag opcode modrm with
        | some op => decodePayload op payload
        | none => (ByteCode.decode bytes).map Form.common

@[simp] theorem common_decode (form : ByteCode.Form) :
    decode (ByteCode.encode form) = some (.common form) := by
  cases form with
  | immediate op address value => cases op <;>
      simp [decode, ByteCode.encode, ByteCode.ImmediateOp.tag, operationOfTag,
        ByteCode.decode, ByteCode.immediateOfTag]
  | memory op address => cases op <;>
      simp [decode, ByteCode.encode, ByteCode.MemoryOp.tag, operationOfTag,
        ByteCode.decode, ByteCode.immediateOfTag, ByteCode.memoryOfTag]
  | storeAcc address => simp [decode, ByteCode.encode, ByteCode.decode]
  | callRelative displacement => simp [decode, ByteCode.encode, ByteCode.decode]

@[simp] theorem add_payload (address value : Word) :
    decodePayload .addImmediate (wordEncode 4 address ++ wordEncode 4 value) =
      some (.addImmediate address value) := by
  have taken : (wordEncode 4 address ++ wordEncode 4 value).take 4 = wordEncode 4 address := rfl
  have dropped : (wordEncode 4 address ++ wordEncode 4 value).drop 4 = wordEncode 4 value := rfl
  simp only [decodePayload, taken, dropped, word_decode_encode]
  rfl

theorem form_roundtrip (form : Form) : decode (encode form) = some form := by
  cases form with
  | common form => exact common_decode form
  | andAcc address => simp [encode, decode, operationOfTag, decodePayload]
  | addImmediate address value => simp [encode, decode, operationOfTag]
  | shiftLeft address => simp [encode, decode, operationOfTag, decodePayload]
  | shiftRight address => simp [encode, decode, operationOfTag, decodePayload]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [form_roundtrip, Option.some.injEq] using decoded

@[expose] def instructionLength : Form → Nat
  | .common form => ByteCode.instructionLength form
  | .addImmediate _ _ => 10
  | _ => 6

theorem encode_length (form : Form) : (encode form).length = instructionLength form := by
  cases form <;> simp [encode, instructionLength, ByteCode.encode_length]

theorem length_bounds (form : Form) : 2 ≤ instructionLength form ∧ instructionLength form ≤ 10 := by
  cases form with
  | common form => exact ByteCode.length_bounds form
  | _ => simp [instructionLength]

@[expose] def Operation.length : Operation → Nat
  | .addImmediate => 10
  | _ => 6

@[expose] def lengthOfBytes (bytes : List Byte) : Option Nat :=
  match bytes with
  | [] => none
  | opcode :: rest =>
    if opcode = 0xa3 ∨ opcode = 0xe8 then some 5
    else match rest with
      | [] => ByteCode.lengthOfBytes bytes
      | modrm :: _ => match operationOfTag opcode modrm with
        | some op => some op.length
        | none => ByteCode.lengthOfBytes bytes

theorem common_length (form : ByteCode.Form) (trailing : List Byte) :
    lengthOfBytes (ByteCode.encode form ++ trailing) = some (ByteCode.instructionLength form) := by
  cases form with
  | immediate op address value => cases op <;>
      simp [lengthOfBytes, ByteCode.encode, ByteCode.ImmediateOp.tag, operationOfTag,
        ByteCode.lengthOfBytes, ByteCode.immediateOfTag, ByteCode.instructionLength, List.append_assoc]
  | memory op address => cases op <;>
      simp [lengthOfBytes, ByteCode.encode, ByteCode.MemoryOp.tag, operationOfTag,
        ByteCode.lengthOfBytes, ByteCode.immediateOfTag, ByteCode.memoryOfTag,
        ByteCode.instructionLength, ByteCode.MemoryOp.trailer]
  | storeAcc address =>
      rfl
  | callRelative displacement =>
      rfl

theorem encoded_length (form : Form) (trailing : List Byte) :
    lengthOfBytes (encode form ++ trailing) = some (instructionLength form) := by
  cases form with
  | common form => exact common_length form trailing
  | _ => simp [encode, instructionLength, lengthOfBytes, operationOfTag, Operation.length,
      List.append_assoc]

theorem length_take_two (bytes : List Byte) : lengthOfBytes (bytes.take 2) = lengthOfBytes bytes := by
  cases bytes with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second tail => rfl

/-- Decode length and operands from current unified memory. -/
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

/-- ADD consumes the actual freshly patched imm32 at +6. -/
theorem add_patch (memory : Memory) (pc : Nat) (address old fresh : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.addImmediate address old))) (pc + 6) fresh =
      Native.ByteMemory.putBytes memory pc (encode (.addImmediate address fresh)) := by
  exact Native.ByteMemory.patch_payload memory pc ([0x81, 0x05] ++ wordEncode 4 address)
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp)

theorem fetch_patched_add (memory : Memory) (pc : Nat) (address old fresh : Word) :
    fetch (Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.addImmediate address old))) (pc + 6) fresh) pc =
      some (.addImmediate address fresh) := by
  rw [add_patch, fetch_written_encoding]

theorem fetch_patched_current_add (memory : Memory) (pc : Nat) (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.addImmediate address old)).length =
      encode (.addImmediate address old)) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 6) fresh) pc = some (.addImmediate address fresh) := by
  have back : Native.ByteMemory.putBytes memory pc (encode (.addImmediate address old)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back]
  exact fetch_patched_add memory pc address old fresh

end SmcTuring.Appendix.MultiplyByteCode
