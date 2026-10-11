module
public import SmcTuring.Native.LittleEndian

public section

namespace SmcTuring.Native

open LittleEndian

inductive Mode where
  | x86 | x64
  deriving DecidableEq, Repr

@[expose] def Mode.wordBytes : Mode -> Nat
  | .x86 => 4
  | .x64 => 8

abbrev Word (mode : Mode) := BitVec (8 * mode.wordBytes)

/-- Full-width data instructions use REX.W in 64-bit mode. Near CALL's
implicit 64-bit operand uses no REX.W in the emitted selected forms. -/
@[expose] def wordPrefix : Mode -> List Byte
  | .x86 => []
  | .x64 => [0x48]

inductive MemoryOp where
  | exchangeAcc | storeAcc | add | subtract | bitXor | bitAnd
  | exchangeStack | storeStack | subtractBorrowZero | callIndirect
  deriving DecidableEq, Repr

/-- Opcode and ModR/M bytes for only the selected memory-destination forms.
Mod 00/rm 101 means disp32 absolute in x86, RIP-relative disp32 in x64. -/
@[expose] def MemoryOp.tag : MemoryOp -> Byte × Byte
  | .exchangeAcc => (0x87, 0x05)
  | .storeAcc => (0x89, 0x05)
  | .add => (0x01, 0x05)
  | .subtract => (0x29, 0x05)
  | .bitXor => (0x31, 0x05)
  | .bitAnd => (0x21, 0x05)
  | .exchangeStack => (0x87, 0x25)
  | .storeStack => (0x89, 0x25)
  | .subtractBorrowZero => (0x83, 0x1D)
  | .callIndirect => (0xFF, 0x15)

@[expose] def MemoryOp.prefix (operation : MemoryOp) (mode : Mode) : List Byte :=
  if operation = .callIndirect then [] else wordPrefix mode

@[expose] def MemoryOp.trailer : MemoryOp -> List Byte
  | .subtractBorrowZero => [0]
  | _ => []

/-- Address payloads of MOFFS use the mode's address width. Displacements are
always 32-bit in the selected forms, even with 64-bit data operands. -/
inductive Form (mode : Mode) where
  | moffs (address : Word mode)
  | memory (operation : MemoryOp) (displacement : BitVec 32)
  | exchangeIndirect
  | callRelative (displacement : BitVec 32)
  deriving DecidableEq, Repr

@[expose] def encode (mode : Mode) : Form mode -> List Byte
  | .moffs address => wordPrefix mode ++ [0xA3] ++ wordEncode mode.wordBytes address
  | .memory operation displacement => operation.prefix mode ++ [operation.tag.1, operation.tag.2] ++
      wordEncode 4 displacement ++ operation.trailer
  | .exchangeIndirect => wordPrefix mode ++ [0x87, 0x00]
  | .callRelative displacement => [0xE8] ++ wordEncode 4 displacement

@[expose] def operationOfTag (opcode modrm : Byte) : Option MemoryOp :=
  match opcode.toNat, modrm.toNat with
  | 0x87, 0x05 => some .exchangeAcc
  | 0x89, 0x05 => some .storeAcc
  | 0x01, 0x05 => some .add
  | 0x29, 0x05 => some .subtract
  | 0x31, 0x05 => some .bitXor
  | 0x21, 0x05 => some .bitAnd
  | 0x87, 0x25 => some .exchangeStack
  | 0x89, 0x25 => some .storeStack
  | 0x83, 0x1D => some .subtractBorrowZero
  | 0xFF, 0x15 => some .callIndirect
  | _, _ => none

@[simp] theorem operation_tag_roundtrip (operation : MemoryOp) :
    operationOfTag operation.tag.1 operation.tag.2 = some operation := by cases operation <;> rfl

/-- The only immediate suffix is the sign-extended imm8 zero of SBB /3. -/
@[expose] def decodeMemoryPayload (operation : MemoryOp) (payload : List Byte) : Option (BitVec 32) :=
  if payload.drop 4 = operation.trailer then wordDecode 4 (payload.take 4) else none

@[simp] theorem memory_payload_roundtrip (operation : MemoryOp) (displacement : BitVec 32) :
    decodeMemoryPayload operation (wordEncode 4 displacement ++ operation.trailer) = some displacement := by
  have taken : (wordEncode 4 displacement ++ operation.trailer).take 4 = wordEncode 4 displacement := by
    cases operation <;> rfl
  have dropped : (wordEncode 4 displacement ++ operation.trailer).drop 4 = operation.trailer := by
    cases operation <;> rfl
  simp only [decodeMemoryPayload, taken, dropped, ite_true, word_decode_encode]

@[expose] def decodeCore (mode : Mode) : List Byte -> Option (Form mode)
  | [] => none
  | opcode :: rest =>
    if opcode = 0xA3 then (wordDecode mode.wordBytes rest).map Form.moffs
    else match rest with
      | [] => none
      | modrm :: payload =>
        if opcode = 0x87 ∧ modrm = 0x00 ∧ payload = [] then some .exchangeIndirect
        else (operationOfTag opcode modrm).bind fun operation =>
          if operation = .callIndirect then none
          else (decodeMemoryPayload operation payload).map (Form.memory operation)

/-- A restricted decoder for the exact selected forms; no claim is made about
other ISA encodings, prefixes or execution modes. -/
@[expose] def decode (mode : Mode) : List Byte -> Option (Form mode)
  | [] => none
  | opcode :: rest =>
    if opcode = 0xE8 then (wordDecode 4 rest).map Form.callRelative
    else if opcode = 0xFF then match rest with
      | modrm :: payload =>
        if modrm = 0x15 then (decodeMemoryPayload .callIndirect payload).map (Form.memory .callIndirect)
        else none
      | [] => none
    else match mode with
      | .x86 => decodeCore .x86 (opcode :: rest)
      | .x64 => if opcode = 0x48 then decodeCore .x64 rest else none

/-- Every address/displacement bit survives encoding and decoding, in both modes. -/
theorem form_roundtrip (mode : Mode) (instruction : Form mode) : decode mode (encode mode instruction) = some instruction := by
  cases instruction with
  | moffs address => cases mode <;> simp [encode, decode, decodeCore, wordPrefix]
  | memory operation displacement =>
    cases mode <;> cases operation <;>
      simp [encode, decode, decodeCore, wordPrefix, MemoryOp.prefix, MemoryOp.tag,
        operationOfTag]
  | exchangeIndirect => cases mode <;> rfl
  | callRelative displacement => cases mode <;> simp [encode, decode]

/-- Distinct selected forms never have the same instruction bytes. -/
theorem form_encode_injective (mode : Mode) : Function.Injective (encode mode) := by
  intro first second same
  have decoded := congrArg (decode mode) same
  simpa only [form_roundtrip, Option.some.injEq] using decoded

@[expose] def instructionLength (mode : Mode) : Form mode -> Nat
  | .moffs _ => (wordPrefix mode).length + 1 + mode.wordBytes
  | .memory operation _ => (operation.prefix mode).length + 6 + operation.trailer.length
  | .exchangeIndirect => (wordPrefix mode).length + 2
  | .callRelative _ => 5

@[simp] theorem instruction_length (mode : Mode) (instruction : Form mode) :
    (encode mode instruction).length = instructionLength mode instruction := by
  cases instruction <;> simp [encode, instructionLength, Nat.add_assoc] <;> omega

/-- Every selected form respects the architectural 15-byte instruction limit. -/
theorem instruction_length_bound (mode : Mode) (instruction : Form mode) :
    instructionLength mode instruction ≤ 15 := by
  cases instruction with
  | moffs address => cases mode <;> simp [instructionLength, wordPrefix, Mode.wordBytes]
  | memory operation displacement =>
    cases mode <;> cases operation <;> simp [instructionLength, MemoryOp.prefix, MemoryOp.trailer, wordPrefix]
  | exchangeIndirect => cases mode <;> simp [instructionLength, wordPrefix]
  | callRelative displacement => simp [instructionLength]

@[expose] def moffsOperandOffset (mode : Mode) : Nat := (wordPrefix mode).length + 1

/-- Only the address payload is the owned mutable word of a MOFFS instruction. -/
theorem moffs_operand_bytes (mode : Mode) (address : Word mode) :
    (encode mode (.moffs address)).drop (moffsOperandOffset mode) = wordEncode mode.wordBytes address := by
  cases mode <;> rfl

theorem moffs_opcode_bytes (mode : Mode) (address : Word mode) :
    (encode mode (.moffs address)).take (moffsOperandOffset mode) = wordPrefix mode ++ [0xA3] := by
  cases mode <;> rfl

/-- A memory-form displacement remains four bytes with an optional imm8 trailer. -/
theorem memory_displacement_bytes (mode : Mode) (operation : MemoryOp) (displacement : BitVec 32) :
    ((encode mode (.memory operation displacement)).drop ((operation.prefix mode).length + 2)).take 4 =
      wordEncode 4 displacement := by
  cases mode <;> cases operation <;> rfl

end SmcTuring.Native
