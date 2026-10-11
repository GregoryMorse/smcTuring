module
public import SmcTuring.Appendix.MultiplyByteCode

public section

namespace SmcTuring.Appendix.DivisionByteCode

open Native.LittleEndian
abbrev Word := MultiplyByteCode.Word
abbrev Memory := MultiplyByteCode.Memory

/-- The four additional literal DWORD forms in Listing 12. -/
inductive Operation where
  | subtractImmediate | right31 | adcZero | decrement
  deriving DecidableEq, Repr

@[expose] def operationOfTag (opcode modrm : Byte) : Option Operation :=
  match opcode.toNat, modrm.toNat with
  | 0x81, 0x2d => some .subtractImmediate
  | 0xc1, 0x2d => some .right31
  | 0x83, 0x15 => some .adcZero
  | 0xff, 0x0d => some .decrement
  | _, _ => none

inductive Form where
  | common (form : MultiplyByteCode.Form)
  | subtractImmediate (address value : Word)
  | right31 (address : Word)
  | adcZero (address : Word)
  | decrement (address : Word)
  deriving DecidableEq, Repr

@[expose] def encode : Form → List Byte
  | .common form => MultiplyByteCode.encode form
  | .subtractImmediate address value => ([0x81, 0x2d] ++ wordEncode 4 address) ++ wordEncode 4 value
  | .right31 address => ([0xc1, 0x2d] ++ wordEncode 4 address) ++ [31]
  | .adcZero address => ([0x83, 0x15] ++ wordEncode 4 address) ++ [0]
  | .decrement address => [0xff, 0x0d] ++ wordEncode 4 address

@[expose] def decodePayload (op : Operation) (payload : List Byte) : Option Form :=
  match op with
  | .subtractImmediate => do
      let address ← wordDecode 4 (payload.take 4)
      let value ← wordDecode 4 (payload.drop 4)
      return .subtractImmediate address value
  | .right31 =>
      if payload.drop 4 = [31] then (wordDecode 4 (payload.take 4)).map Form.right31 else none
  | .adcZero =>
      if payload.drop 4 = [0] then (wordDecode 4 (payload.take 4)).map Form.adcZero else none
  | .decrement => (wordDecode 4 payload).map Form.decrement

/-- Extra forms accept precisely the displayed immediate/count bytes;
all previous branch/multiplication forms retain their decoder. -/
@[expose] def decode (bytes : List Byte) : Option Form :=
  match bytes with
  | [] => none
  | opcode :: rest =>
    if opcode = 0xa3 ∨ opcode = 0xe8 then (MultiplyByteCode.decode bytes).map Form.common
    else match rest with
      | [] => (MultiplyByteCode.decode bytes).map Form.common
      | modrm :: payload => match operationOfTag opcode modrm with
        | some op => decodePayload op payload
        | none => (MultiplyByteCode.decode bytes).map Form.common

@[simp] theorem common_decode (form : MultiplyByteCode.Form) :
    decode (MultiplyByteCode.encode form) = some (.common form) := by
  cases form with
  | common form =>
    cases form with
    | immediate op address value => cases op <;>
        simp [decode, MultiplyByteCode.encode, ByteCode.encode, ByteCode.ImmediateOp.tag,
          operationOfTag, MultiplyByteCode.decode, MultiplyByteCode.operationOfTag,
          ByteCode.decode, ByteCode.immediateOfTag]
    | memory op address => cases op <;>
        simp [decode, MultiplyByteCode.encode, ByteCode.encode, ByteCode.MemoryOp.tag,
          operationOfTag, MultiplyByteCode.decode, MultiplyByteCode.operationOfTag,
          ByteCode.decode, ByteCode.immediateOfTag, ByteCode.memoryOfTag]
    | storeAcc address => simp [decode, MultiplyByteCode.encode, ByteCode.encode, MultiplyByteCode.decode, ByteCode.decode]
    | callRelative displacement => simp [decode, MultiplyByteCode.encode, ByteCode.encode, MultiplyByteCode.decode, ByteCode.decode]
  | _ => simp [decode, MultiplyByteCode.encode, operationOfTag, MultiplyByteCode.decode, MultiplyByteCode.operationOfTag, MultiplyByteCode.decodePayload]

@[simp] theorem subtract_payload (address value : Word) :
    decodePayload .subtractImmediate (wordEncode 4 address ++ wordEncode 4 value) =
      some (.subtractImmediate address value) := by
  have taken : (wordEncode 4 address ++ wordEncode 4 value).take 4 = wordEncode 4 address := rfl
  have dropped : (wordEncode 4 address ++ wordEncode 4 value).drop 4 = wordEncode 4 value := rfl
  simp only [decodePayload, taken, dropped, word_decode_encode]
  rfl

@[simp] theorem right_payload (address : Word) :
    decodePayload .right31 (wordEncode 4 address ++ [31]) = some (.right31 address) := by
  simp [decodePayload]

@[simp] theorem adc_payload (address : Word) :
    decodePayload .adcZero (wordEncode 4 address ++ [0]) = some (.adcZero address) := by
  simp [decodePayload]

theorem form_roundtrip (form : Form) : decode (encode form) = some form := by
  cases form with
  | common form => exact common_decode form
  | subtractImmediate address value => simp [encode, decode, operationOfTag]
  | right31 address => simp [encode, decode, operationOfTag, decodePayload]
  | adcZero address => simp [encode, decode, operationOfTag, decodePayload]
  | decrement address => simp [encode, decode, operationOfTag, decodePayload]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [form_roundtrip, Option.some.injEq] using decoded

@[expose] def instructionLength : Form → Nat
  | .common form => MultiplyByteCode.instructionLength form
  | .subtractImmediate _ _ => 10
  | .right31 _ | .adcZero _ => 7
  | _ => 6

theorem encode_length (form : Form) : (encode form).length = instructionLength form := by
  cases form <;> simp [encode, instructionLength, MultiplyByteCode.encode_length]

theorem length_bounds (form : Form) : 2 ≤ instructionLength form ∧ instructionLength form ≤ 10 := by
  cases form with
  | common form => exact MultiplyByteCode.length_bounds form
  | _ => simp [instructionLength]

@[expose] def Operation.length : Operation → Nat
  | .subtractImmediate => 10
  | .right31 | .adcZero => 7
  | _ => 6

@[expose] def lengthOfBytes (bytes : List Byte) : Option Nat :=
  match bytes with
  | [] => none
  | opcode :: rest =>
    if opcode = 0xa3 ∨ opcode = 0xe8 then some 5
    else match rest with
      | [] => MultiplyByteCode.lengthOfBytes bytes
      | modrm :: _ => match operationOfTag opcode modrm with
        | some op => some op.length
        | none => MultiplyByteCode.lengthOfBytes bytes

theorem common_length (form : MultiplyByteCode.Form) (trailing : List Byte) :
    lengthOfBytes (MultiplyByteCode.encode form ++ trailing) = some (MultiplyByteCode.instructionLength form) := by
  cases form with
  | common form =>
    cases form with
    | immediate op address value => cases op <;>
        simp [lengthOfBytes, MultiplyByteCode.encode, ByteCode.encode, ByteCode.ImmediateOp.tag,
          operationOfTag, MultiplyByteCode.lengthOfBytes, MultiplyByteCode.operationOfTag,
          ByteCode.lengthOfBytes, ByteCode.immediateOfTag, MultiplyByteCode.instructionLength,
          ByteCode.instructionLength, List.append_assoc]
    | memory op address => cases op <;>
        simp [lengthOfBytes, MultiplyByteCode.encode, ByteCode.encode, ByteCode.MemoryOp.tag,
          operationOfTag, MultiplyByteCode.lengthOfBytes, MultiplyByteCode.operationOfTag,
          ByteCode.lengthOfBytes, ByteCode.immediateOfTag, ByteCode.memoryOfTag,
          MultiplyByteCode.instructionLength, ByteCode.instructionLength, ByteCode.MemoryOp.trailer]
    | storeAcc address => rfl
    | callRelative displacement => rfl
  | _ => simp [lengthOfBytes, MultiplyByteCode.encode, operationOfTag,
      MultiplyByteCode.lengthOfBytes, MultiplyByteCode.operationOfTag,
      MultiplyByteCode.Operation.length, MultiplyByteCode.instructionLength, List.append_assoc]

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

/-- SUB consumes the actual freshly patched imm32 at +6. -/
theorem subtract_patch (memory : Memory) (pc : Nat) (address old fresh : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.subtractImmediate address old))) (pc + 6) fresh =
      Native.ByteMemory.putBytes memory pc (encode (.subtractImmediate address fresh)) := by
  exact Native.ByteMemory.patch_payload memory pc ([0x81, 0x2d] ++ wordEncode 4 address)
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp)

theorem fetch_patched_subtract (memory : Memory) (pc : Nat) (address old fresh : Word) :
    fetch (Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.subtractImmediate address old))) (pc + 6) fresh) pc =
      some (.subtractImmediate address fresh) := by
  rw [subtract_patch, fetch_written_encoding]

theorem fetch_patched_current_subtract (memory : Memory) (pc : Nat) (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.subtractImmediate address old)).length =
      encode (.subtractImmediate address old)) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 6) fresh) pc = some (.subtractImmediate address fresh) := by
  have back : Native.ByteMemory.putBytes memory pc (encode (.subtractImmediate address old)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back]
  exact fetch_patched_subtract memory pc address old fresh

end SmcTuring.Appendix.DivisionByteCode
