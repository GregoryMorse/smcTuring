module
public import SmcTuring.Native.Writes

public section

namespace SmcTuring.Appendix.ByteCode

open Native.LittleEndian

abbrev Word := BitVec 32
abbrev Memory := Native.ByteMemory.Memory

/-- Only the literal x86 DWORD/imm32 forms in the normalized branch emitter.
No claim about other encodings, long mode or the whole ISA is made. -/
inductive ImmediateOp where
  | store | bitXor | bitAnd
  deriving DecidableEq, Repr

inductive MemoryOp where
  | exchangeAcc | exchangeStack | subtractAcc | addAcc
  | negate | complement | sbbZero | addFour
  deriving DecidableEq, Repr

@[expose] def ImmediateOp.tag : ImmediateOp → Byte × Byte
  | .store => (0xc7, 0x05)
  | .bitXor => (0x81, 0x35)
  | .bitAnd => (0x81, 0x25)

@[expose] def MemoryOp.tag : MemoryOp → Byte × Byte
  | .exchangeAcc => (0x87, 0x05)
  | .exchangeStack => (0x87, 0x25)
  | .subtractAcc => (0x29, 0x05)
  | .addAcc => (0x01, 0x05)
  | .negate => (0xf7, 0x1d)
  | .complement => (0xf7, 0x15)
  | .sbbZero => (0x83, 0x1d)
  | .addFour => (0x83, 0x05)

@[expose] def MemoryOp.trailer : MemoryOp → List Byte
  | .sbbZero => [0]
  | .addFour => [4]
  | _ => []

inductive Form where
  | immediate (operation : ImmediateOp) (address value : Word)
  | memory (operation : MemoryOp) (address : Word)
  | storeAcc (address : Word)
  | callRelative (displacement : Word)
  deriving DecidableEq, Repr

@[expose] def encode : Form → List Byte
  | .immediate op address value =>
      ([op.tag.1, op.tag.2] ++ wordEncode 4 address) ++ wordEncode 4 value
  | .memory op address => [op.tag.1, op.tag.2] ++ (wordEncode 4 address ++ op.trailer)
  | .storeAcc address => [0xa3] ++ wordEncode 4 address
  | .callRelative displacement => [0xe8] ++ wordEncode 4 displacement

@[expose] def immediateOfTag (opcode modrm : Byte) : Option ImmediateOp :=
  match opcode.toNat, modrm.toNat with
  | 0xc7, 0x05 => some .store
  | 0x81, 0x35 => some .bitXor
  | 0x81, 0x25 => some .bitAnd
  | _, _ => none

@[expose] def memoryOfTag (opcode modrm : Byte) : Option MemoryOp :=
  match opcode.toNat, modrm.toNat with
  | 0x87, 0x05 => some .exchangeAcc
  | 0x87, 0x25 => some .exchangeStack
  | 0x29, 0x05 => some .subtractAcc
  | 0x01, 0x05 => some .addAcc
  | 0xf7, 0x1d => some .negate
  | 0xf7, 0x15 => some .complement
  | 0x83, 0x1d => some .sbbZero
  | 0x83, 0x05 => some .addFour
  | _, _ => none

@[simp] theorem immediate_tag (op : ImmediateOp) :
    immediateOfTag op.tag.1 op.tag.2 = some op := by cases op <;> rfl

@[simp] theorem memory_tag (op : MemoryOp) :
    memoryOfTag op.tag.1 op.tag.2 = some op := by cases op <;> rfl

@[simp] theorem memory_not_immediate (op : MemoryOp) :
    immediateOfTag op.tag.1 op.tag.2 = none := by cases op <;> rfl

@[expose] def decodeImmediatePayload (op : ImmediateOp) (payload : List Byte) : Option Form := do
  let address ← wordDecode 4 (payload.take 4)
  let value ← wordDecode 4 (payload.drop 4)
  return .immediate op address value

@[expose] def decodeMemoryPayload (op : MemoryOp) (payload : List Byte) : Option Form :=
  if payload.drop 4 = op.trailer then
    (wordDecode 4 (payload.take 4)).map (Form.memory op)
  else none

@[simp] theorem immediate_payload (op : ImmediateOp) (address value : Word) :
    decodeImmediatePayload op (wordEncode 4 address ++ wordEncode 4 value) =
      some (.immediate op address value) := by
  have taken : (wordEncode 4 address ++ wordEncode 4 value).take 4 = wordEncode 4 address := rfl
  have dropped : (wordEncode 4 address ++ wordEncode 4 value).drop 4 = wordEncode 4 value := rfl
  simp only [decodeImmediatePayload, taken, dropped, word_decode_encode]
  rfl

@[simp] theorem memory_payload (op : MemoryOp) (address : Word) :
    decodeMemoryPayload op (wordEncode 4 address ++ op.trailer) = some (.memory op address) := by
  have taken : (wordEncode 4 address ++ op.trailer).take 4 = wordEncode 4 address := by cases op <;> rfl
  have dropped : (wordEncode 4 address ++ op.trailer).drop 4 = op.trailer := by cases op <;> rfl
  simp only [decodeMemoryPayload, taken, dropped, ite_true, word_decode_encode, Option.map_some]

/-- A whole selected packet is decoded with exact operand widths and fixed
SBB zero/ADD four trailers. Mutable operands are not classified as headers. -/
@[expose] def decode : List Byte → Option Form
  | [] => none
  | opcode :: rest =>
    if opcode = 0xe8 then (wordDecode 4 rest).map Form.callRelative
    else if opcode = 0xa3 then (wordDecode 4 rest).map Form.storeAcc
    else match rest with
      | [] => none
      | modrm :: payload => match immediateOfTag opcode modrm with
        | some op => decodeImmediatePayload op payload
        | none => (memoryOfTag opcode modrm).bind (fun op => decodeMemoryPayload op payload)

theorem form_roundtrip (form : Form) : decode (encode form) = some form := by
  cases form with
  | immediate op address value => cases op <;>
      simp [encode, decode, ImmediateOp.tag, immediateOfTag]
  | memory op address => cases op <;>
      simp [encode, decode, MemoryOp.tag, immediateOfTag, memoryOfTag]
  | storeAcc address => simp [encode, decode]
  | callRelative displacement => simp [encode, decode]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [form_roundtrip, Option.some.injEq] using decoded

@[expose] def instructionLength : Form → Nat
  | .immediate _ _ _ => 10
  | .memory op _ => 6 + op.trailer.length
  | .storeAcc _ | .callRelative _ => 5

theorem encode_length (form : Form) : (encode form).length = instructionLength form := by
  cases form <;> simp [encode, instructionLength]
  omega

theorem length_bounds (form : Form) : 2 ≤ instructionLength form ∧ instructionLength form ≤ 10 := by
  cases form with
  | immediate => simp [instructionLength]
  | memory op address => cases op <;> simp [instructionLength, MemoryOp.trailer]
  | storeAcc => simp [instructionLength]
  | callRelative => simp [instructionLength]

/-- At most the first two bytes choose the packet length. The exact decoder
then validates all current operand bytes and required constant trailers. -/
@[expose] def lengthOfBytes : List Byte → Option Nat
  | [] => none
  | opcode :: rest =>
    if opcode = 0xe8 ∨ opcode = 0xa3 then some 5
    else match rest with
      | [] => none
      | modrm :: _ => match immediateOfTag opcode modrm with
        | some _ => some 10
        | none => (memoryOfTag opcode modrm).map (fun op => 6 + op.trailer.length)

theorem encoded_length (form : Form) (trailing : List Byte) :
    lengthOfBytes (encode form ++ trailing) = some (instructionLength form) := by
  cases form with
  | immediate op address value => cases op <;>
      simp [lengthOfBytes, encode, instructionLength, ImmediateOp.tag, immediateOfTag, List.append_assoc]
  | memory op address => cases op <;>
      simp [lengthOfBytes, encode, instructionLength, MemoryOp.tag, immediateOfTag, memoryOfTag]
  | storeAcc => rfl
  | callRelative => rfl

theorem length_take_two (bytes : List Byte) : lengthOfBytes (bytes.take 2) = lengthOfBytes bytes := by
  cases bytes with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second tail => rfl

/-- Actual current-memory fetch: derive a length from the live opcode/ModR/M,
then decode that whole live packet. No length or operand oracle is an input. -/
@[expose] def fetch (memory : Memory) (pc : Nat) : Option Form :=
  (lengthOfBytes (Native.ByteMemory.bytesAt memory pc 2)).bind fun length =>
    decode (Native.ByteMemory.bytesAt memory pc length)

theorem fetch_current_encoding (memory : Memory) (pc : Nat) (form : Form)
    (current : Native.ByteMemory.bytesAt memory pc (encode form).length = encode form) :
    fetch memory pc = some form := by
  have bound : 2 ≤ (encode form).length := by rw [encode_length]; exact (length_bounds form).1
  have header : lengthOfBytes (Native.ByteMemory.bytesAt memory pc 2) = some (instructionLength form) := by
    rw [←Native.Fetch.bytes_at_take memory pc (encode form).length 2 bound, current,
      length_take_two]
    simpa only [List.append_nil] using encoded_length form []
  unfold fetch
  rw [header, Option.bind_some, ←encode_length, current, form_roundtrip]

theorem fetch_written_encoding (memory : Memory) (pc : Nat) (form : Form) :
    fetch (Native.ByteMemory.putBytes memory pc (encode form)) pc = some form :=
  fetch_current_encoding _ pc form (Native.ByteMemory.bytes_at_put memory pc (encode form))

/-- A complete DWORD write at the real imm32 offset +6 changes only that
payload, including unchanged stores; the exact fetched operation is retained. -/
theorem immediate_patch (memory : Memory) (pc : Nat) (op : ImmediateOp) (address old fresh : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.immediate op address old))) (pc + 6) fresh =
      Native.ByteMemory.putBytes memory pc (encode (.immediate op address fresh)) := by
  have length : ([op.tag.1, op.tag.2] ++ wordEncode 4 address).length = 6 := by simp
  have patched := Native.ByteMemory.patch_payload memory pc
    ([op.tag.1, op.tag.2] ++ wordEncode 4 address)
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp)
  simpa only [encode, Native.ByteMemory.putWord, Native.Mode.wordBytes, length] using patched

theorem fetch_patched_immediate (memory : Memory) (pc : Nat) (op : ImmediateOp) (address old fresh : Word) :
    fetch (Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.immediate op address old))) (pc + 6) fresh) pc =
      some (.immediate op address fresh) := by
  rw [immediate_patch, fetch_written_encoding]

/-- Patching an already-current instruction needs no repeated initializer or
assumed future packet. MOV/AND/XOR's actual fresh immediate is consumed. -/
theorem fetch_patched_current_immediate (memory : Memory) (pc : Nat) (op : ImmediateOp)
    (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.immediate op address old)).length =
      encode (.immediate op address old)) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 6) fresh) pc = some (.immediate op address fresh) := by
  have back : Native.ByteMemory.putBytes memory pc (encode (.immediate op address old)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back]
  exact fetch_patched_immediate memory pc op address old fresh

/-- E8 owns its complete rel32 at +1. The CALL's live displacement changes,
while its opcode and every byte outside that four-byte field survive. -/
theorem call_patch (memory : Memory) (pc : Nat) (old fresh : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.callRelative old))) (pc + 1) fresh =
      Native.ByteMemory.putBytes memory pc (encode (.callRelative fresh)) := by
  exact Native.ByteMemory.patch_payload memory pc [0xe8] (wordEncode 4 old) (wordEncode 4 fresh) (by simp)

theorem fetch_patched_call (memory : Memory) (pc : Nat) (old fresh : Word) :
    fetch (Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.callRelative old))) (pc + 1) fresh) pc =
      some (.callRelative fresh) := by
  rw [call_patch, fetch_written_encoding]

theorem fetch_patched_current_call (memory : Memory) (pc : Nat) (old fresh : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.callRelative old)).length = encode (.callRelative old)) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 1) fresh) pc = some (.callRelative fresh) := by
  have back : Native.ByteMemory.putBytes memory pc (encode (.callRelative old)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back]
  exact fetch_patched_call memory pc old fresh

/-- Split a literal byte image into consecutive writes, preserving outside memory. -/
theorem put_bytes_append (memory : Memory) (pc : Nat) (first second : List Byte) :
    Native.ByteMemory.putBytes memory pc (first ++ second) =
      Native.ByteMemory.putBytes (Native.ByteMemory.putBytes memory pc first) (pc + first.length) second := by
  funext position
  by_cases before : position < pc
  · have outside : ¬Native.ByteMemory.Inside pc (first ++ second).length position := by
      simp only [Native.ByteMemory.Inside, List.length_append]; omega
    have firstOutside : ¬Native.ByteMemory.Inside pc first.length position := by
      unfold Native.ByteMemory.Inside; omega
    have secondOutside : ¬Native.ByteMemory.Inside (pc + first.length) second.length position := by
      unfold Native.ByteMemory.Inside; omega
    rw [Native.ByteMemory.put_frame _ _ _ _ outside,
      Native.ByteMemory.put_frame _ _ _ _ secondOutside, Native.ByteMemory.put_frame _ _ _ _ firstOutside]
  · have after : pc ≤ position := by omega
    by_cases inFirst : position < pc + first.length
    · have firstInside : Native.ByteMemory.Inside pc first.length position := ⟨after, inFirst⟩
      have bothInside : Native.ByteMemory.Inside pc (first.length + second.length) position := by
        unfold Native.ByteMemory.Inside; omega
      have secondOutside : ¬Native.ByteMemory.Inside (pc + first.length) second.length position := by
        unfold Native.ByteMemory.Inside; omega
      have index : position - pc < first.length := by omega
      rw [Native.ByteMemory.put_frame _ _ _ _ secondOutside]
      simp [Native.ByteMemory.putBytes, firstInside, bothInside, List.getElem_append_left index]
    · by_cases inSecond : position < pc + first.length + second.length
      · have secondInside : Native.ByteMemory.Inside (pc + first.length) second.length position := by
          unfold Native.ByteMemory.Inside; omega
        have bothInside : Native.ByteMemory.Inside pc (first.length + second.length) position := by
          unfold Native.ByteMemory.Inside; omega
        have index : first.length ≤ position - pc := by omega
        simp [Native.ByteMemory.putBytes, secondInside, bothInside,
          List.getElem_append_right index, Nat.sub_sub]
      · have outside : ¬Native.ByteMemory.Inside pc (first ++ second).length position := by
          simp only [Native.ByteMemory.Inside, List.length_append]; omega
        have firstOutside : ¬Native.ByteMemory.Inside pc first.length position := by
          unfold Native.ByteMemory.Inside; omega
        have secondOutside : ¬Native.ByteMemory.Inside (pc + first.length) second.length position := by
          unfold Native.ByteMemory.Inside; omega
        rw [Native.ByteMemory.put_frame _ _ _ _ outside,
          Native.ByteMemory.put_frame _ _ _ _ secondOutside, Native.ByteMemory.put_frame _ _ _ _ firstOutside]

/-- Operand replacement also preserves a following operand/trailer. This is
needed for DEFSTACK's address payload before its separate imm32 top word. -/
theorem patch_middle (memory : Memory) (pc : Nat) (leading old fresh trailing : List Byte)
    (sameWidth : old.length = fresh.length) :
    Native.ByteMemory.putBytes
      (Native.ByteMemory.putBytes memory pc ((leading ++ old) ++ trailing)) (pc + leading.length) fresh =
      Native.ByteMemory.putBytes memory pc ((leading ++ fresh) ++ trailing) := by
  rw [put_bytes_append memory pc (leading ++ old) trailing]
  have separate : ∀ position,
      Native.ByteMemory.Inside (pc + (leading ++ old).length) trailing.length position →
      ¬Native.ByteMemory.Inside (pc + leading.length) fresh.length position := by
    intro position inside
    simp only [Native.ByteMemory.Inside, List.length_append] at inside ⊢
    omega
  rw [Native.Writes.put_bytes_commute _ _ _ _ _ separate,
    Native.ByteMemory.patch_payload memory pc leading old fresh sameWidth]
  have location : pc + (leading ++ old).length = pc + (leading ++ fresh).length := by
    simp only [List.length_append, sameWidth]
  rw [location, ←put_bytes_append]

theorem address_patch (memory : Memory) (pc : Nat) (op : ImmediateOp) (old fresh value : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.immediate op old value))) (pc + 2) fresh =
      Native.ByteMemory.putBytes memory pc (encode (.immediate op fresh value)) := by
  exact patch_middle memory pc [op.tag.1, op.tag.2] (wordEncode 4 old)
    (wordEncode 4 fresh) (wordEncode 4 value) (by simp)

theorem fetch_patched_address (memory : Memory) (pc : Nat) (op : ImmediateOp) (old fresh value : Word) :
    fetch (Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory pc (encode (.immediate op old value))) (pc + 2) fresh) pc =
      some (.immediate op fresh value) := by
  rw [address_patch, fetch_written_encoding]

/-- The actual complete CALL return word can replace DEFSTACK's address field
without damaging its header or imm32; no fictitious disjoint return slot is used. -/
theorem fetch_patched_current_address (memory : Memory) (pc : Nat) (op : ImmediateOp)
    (old fresh value : Word)
    (current : Native.ByteMemory.bytesAt memory pc (encode (.immediate op old value)).length =
      encode (.immediate op old value)) :
    fetch (Native.ByteMemory.putWord .x86 memory (pc + 2) fresh) pc = some (.immediate op fresh value) := by
  have back : Native.ByteMemory.putBytes memory pc (encode (.immediate op old value)) = memory := by
    rw [←current]
    exact Native.Writes.put_bytes_back memory pc _
  rw [←back]
  exact fetch_patched_address memory pc op old fresh value

end SmcTuring.Appendix.ByteCode
