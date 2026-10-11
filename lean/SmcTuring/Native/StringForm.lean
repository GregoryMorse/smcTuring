module
public import SmcTuring.Native.StringCodec
public import SmcTuring.Native.Fetch

public section
namespace SmcTuring.Native.StringForm
open LittleEndian

/-- Extension used by the literal Listing 5 macro. Native forms retain their
existing codec and effect; the new forms name the actual SI/DI and MOVS packets. -/
inductive Form (mode : Mode) where
  | native (form : Native.Form mode)
  | initialize32 (address value : BitVec 32)
  | exchangeIndex (destination : Bool) (displacement : BitVec 32)
  | subtractSmall (displacement : BitVec 32) (value : Byte)
  | subtractFull (displacement value : BitVec 32)
  | move (width : Nat)
  deriving DecidableEq

@[expose] def Legal (mode : Mode) : Form mode -> Prop
  | .initialize32 _ _ => mode = .x86
  | .move width => StringPlan.Legal mode width
  | _ => True

@[expose] def encode (mode : Mode) : Form mode -> List Byte
  | .native form => Native.encode mode form
  | .initialize32 address value => Appendix.ByteCode.encode (.immediate .store address value)
  | .exchangeIndex destination displacement => wordPrefix mode ++ [0x87, if destination then 0x3D else 0x35] ++ wordEncode 4 displacement
  | .subtractSmall displacement value => wordPrefix mode ++ [0x83,0x2D] ++ wordEncode 4 displacement ++ [value]
  | .subtractFull displacement value => wordPrefix mode ++ [0x81,0x2D] ++ wordEncode 4 displacement ++ wordEncode 4 value
  | .move width => StringPlan.opcode width

@[expose] def coreDecode (mode : Mode) (opcode modrm : Byte) (payload : List Byte) : Option (Form mode) :=
  if opcode = 0x87 ∧ modrm = 0x35 then (wordDecode 4 payload).map (.exchangeIndex false)
  else if opcode = 0x87 ∧ modrm = 0x3D then (wordDecode 4 payload).map (.exchangeIndex true)
  else if opcode = 0x83 ∧ modrm = 0x2D then do
    let displacement ← wordDecode 4 (payload.take 4)
    match payload.drop 4 with
    | [value] => some (.subtractSmall displacement value)
    | _ => none
  else if opcode = 0x81 ∧ modrm = 0x2D then do
    let displacement ← wordDecode 4 (payload.take 4)
    let value ← wordDecode 4 (payload.drop 4)
    return .subtractFull displacement value
  else if mode = .x86 ∧ opcode = 0xC7 ∧ modrm = 0x05 then do
    let address ← wordDecode 4 (payload.take 4)
    let value ← wordDecode 4 (payload.drop 4)
    return .initialize32 address value
  else none

@[expose] def corePacketDecode (mode : Mode) : List Byte -> Option (Form mode)
  | [] => none
  | opcode :: rest =>
    if opcode = 0x87 ∨ opcode = 0x83 ∨ opcode = 0x81 ∨ opcode = 0xC7 then
      match rest with | modrm :: payload => coreDecode mode opcode modrm payload | [] => none
    else none

@[expose] def extraDecode (mode : Mode) (bytes : List Byte) : Option (Form mode) :=
  if bytes = [0xA4] then some (.move 1)
  else if bytes = [0x66,0xA5] then some (.move 2)
  else if bytes = [0xA5] then some (.move 4)
  else if mode = .x64 ∧ bytes = [0x48,0xA5] then some (.move 8)
  else match mode with
    | .x86 => corePacketDecode .x86 bytes
    | .x64 => match bytes with
      | rex :: rest => if rex = 0x48 then corePacketDecode .x64 rest else none
      | [] => none

@[expose] def decode (mode : Mode) (bytes : List Byte) : Option (Form mode) :=
  match extraDecode mode bytes with
  | some form => some form
  | none => (Native.decode mode bytes).map Form.native

@[expose] def coreLength (mode : Mode) (opcode modrm : Byte) : Option Nat :=
  if opcode = 0x87 ∧ (modrm = 0x35 ∨ modrm = 0x3D) then some ((wordPrefix mode).length+6)
  else if opcode = 0x83 ∧ modrm = 0x2D then some ((wordPrefix mode).length+7)
  else if opcode = 0x81 ∧ modrm = 0x2D then some ((wordPrefix mode).length+10)
  else if mode = .x86 ∧ opcode = 0xC7 ∧ modrm = 0x05 then some 10
  else none

@[expose] def headerLength (mode : Mode) (first : Byte) (second third : Option Byte) : Option Nat :=
  if first = 0xA4 ∨ first = 0xA5 then some 1
  else if first = 0x66 then second.bind (fun next => if next = 0xA5 then some 2 else none)
  else match mode with
    | .x86 => second.bind (coreLength .x86 first)
    | .x64 => if first = 0x48 then second.bind fun core =>
        if core = 0xA5 then some 2 else third.bind (coreLength .x64 core)
      else none

@[expose] def extraLength (mode : Mode) (bytes : List Byte) : Option Nat :=
  match bytes with
  | [] => none
  | first :: rest => headerLength mode first rest.head? rest.tail.head?

@[expose] def lengthOfBytes (mode : Mode) (bytes : List Byte) : Option Nat :=
  match extraLength mode bytes with
  | some length => some length
  | none => Fetch.lengthOfBytes mode bytes

@[expose] def length (mode : Mode) (form : Form mode) : Nat := (encode mode form).length

/-- The existing native subset is disjoint from the new packet tags. -/
theorem native_extra_none (mode : Mode) (form : Native.Form mode) : extraDecode mode (Native.encode mode form) = none := by
  cases form with
  | moffs address => cases mode <;> simp [extraDecode,corePacketDecode,Native.encode,wordPrefix]
  | memory operation displacement => cases mode <;> cases operation <;>
      simp [extraDecode,corePacketDecode,Native.encode,wordPrefix,coreDecode,MemoryOp.prefix,MemoryOp.tag,MemoryOp.trailer]
  | exchangeIndirect => cases mode <;> simp [extraDecode,corePacketDecode,Native.encode,wordPrefix,coreDecode]
  | callRelative displacement => cases mode <;> simp [extraDecode,corePacketDecode,Native.encode]

theorem native_decode (mode : Mode) (form : Native.Form mode) : decode mode (encode mode (.native form)) = some (.native form) := by
  unfold decode encode
  rw [native_extra_none,Native.form_roundtrip]
  rfl

theorem form_roundtrip (mode : Mode) (form : Form mode) (legal : Legal mode form) : decode mode (encode mode form) = some form := by
  cases form with
  | native form => exact native_decode mode form
  | initialize32 address value =>
      have only : mode = .x86 := legal
      subst mode
      simp [decode,extraDecode,corePacketDecode,encode,Appendix.ByteCode.encode,Appendix.ByteCode.ImmediateOp.tag,coreDecode,word_decode_encode]
  | exchangeIndex destination displacement => cases mode <;> cases destination <;>
      simp [decode,extraDecode,corePacketDecode,encode,wordPrefix,coreDecode,word_decode_encode]
  | subtractSmall displacement value => cases mode <;>
      simp [decode,extraDecode,corePacketDecode,encode,wordPrefix,coreDecode,word_decode_encode]
  | subtractFull displacement value => cases mode <;>
      simp [decode,extraDecode,corePacketDecode,encode,wordPrefix,coreDecode,word_decode_encode]
  | move width =>
      rcases legal with one | two | four | eight
      · subst width; cases mode <;> rfl
      · subst width; cases mode <;> rfl
      · subst width; cases mode <;> rfl
      · rcases eight with ⟨rfl,rfl⟩; rfl

theorem native_extra_length_none (mode : Mode) (form : Native.Form mode) (trailing : List Byte) :
    extraLength mode (Native.encode mode form ++ trailing) = none := by
  cases form with
  | moffs address => cases mode <;> simp [extraLength,headerLength,Native.encode,wordPrefix,coreLength]
  | memory operation displacement => cases mode <;> cases operation <;>
      simp [extraLength,headerLength,Native.encode,wordPrefix,coreLength,MemoryOp.prefix,MemoryOp.tag,MemoryOp.trailer]
  | exchangeIndirect => cases mode <;> simp [extraLength,headerLength,Native.encode,wordPrefix,coreLength]
  | callRelative displacement => cases mode <;> simp [extraLength,headerLength,Native.encode,coreLength]

theorem encoded_length (mode : Mode) (form : Form mode) (legal : Legal mode form) (trailing : List Byte) :
    lengthOfBytes mode (encode mode form ++ trailing) = some (length mode form) := by
  cases form with
  | native form =>
      simp only [lengthOfBytes,encode,native_extra_length_none]
      simpa only [length,encode,instruction_length] using Fetch.encoded_length mode form trailing
  | initialize32 address value =>
      have only : mode = .x86 := legal
      subst mode
      simp [lengthOfBytes,extraLength,headerLength,coreLength,encode,length,Appendix.ByteCode.encode,Appendix.ByteCode.ImmediateOp.tag]
  | exchangeIndex destination displacement => cases mode <;> cases destination <;>
      simp [lengthOfBytes,extraLength,headerLength,coreLength,encode,length,wordPrefix]
  | subtractSmall displacement value => cases mode <;>
      simp [lengthOfBytes,extraLength,headerLength,coreLength,encode,length,wordPrefix]
  | subtractFull displacement value => cases mode <;>
      simp [lengthOfBytes,extraLength,headerLength,coreLength,encode,length,wordPrefix]
  | move width =>
      rcases legal with one | two | four | eight
      · subst width; cases mode <;> rfl
      · subst width; cases mode <;> rfl
      · subst width; cases mode <;> rfl
      · rcases eight with ⟨rfl,rfl⟩; rfl

theorem length_bound (mode : Mode) (form : Form mode) (legal : Legal mode form) : length mode form ≤ 15 := by
  cases form with
  | native form => simpa only [length,encode,instruction_length] using instruction_length_bound mode form
  | initialize32 address value => simp [length,encode,Appendix.ByteCode.encode,Appendix.ByteCode.ImmediateOp.tag]
  | exchangeIndex destination displacement => cases mode <;> cases destination <;> simp [length,encode,wordPrefix]
  | subtractSmall displacement value => cases mode <;> simp [length,encode,wordPrefix]
  | subtractFull displacement value => cases mode <;> simp [length,encode,wordPrefix]
  | move width =>
      rcases StringPlan.opcode_length mode width legal with one | two <;> change (StringPlan.opcode width).length ≤ 15 <;> omega

theorem length_take_three (mode : Mode) (bytes : List Byte) : lengthOfBytes mode (bytes.take 3) = lengthOfBytes mode bytes := by
  have extra : extraLength mode (bytes.take 3) = extraLength mode bytes := by
    cases bytes with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
        cases tail with
        | nil => rfl
        | cons third trailing => cases mode <;> simp [extraLength,headerLength]
  unfold lengthOfBytes
  rw [extra,Fetch.length_take_three]

@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  (lengthOfBytes mode (ByteMemory.bytesAt memory pc 3)).bind fun count => decode mode (ByteMemory.bytesAt memory pc count)

/-- Automatic current-byte fetch infers the length from the live opcode. -/
theorem fetch_current_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode) (legal : Legal mode form)
    (current : ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form) : fetch mode memory pc = some form := by
  have packet : (ByteMemory.bytesAt memory pc 15).take (encode mode form).length = encode mode form := by
    have bounded := length_bound mode form legal
    change (encode mode form).length ≤ 15 at bounded
    rw [Fetch.bytes_at_take memory pc 15 _ bounded,current]
  have window : ByteMemory.bytesAt memory pc 15 = encode mode form ++ (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length := by
    calc
      ByteMemory.bytesAt memory pc 15 = (ByteMemory.bytesAt memory pc 15).take (encode mode form).length ++
        (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length := (List.take_append_drop _ _).symm
      _ = _ := congrArg (fun leading => leading ++ (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length) packet
  have inferred : lengthOfBytes mode (ByteMemory.bytesAt memory pc 3) = some (length mode form) := by
    rw [←Fetch.bytes_at_take memory pc 15 3 (by omega),length_take_three,window,encoded_length mode form legal]
  unfold fetch
  rw [inferred,Option.bind_some]
  change decode mode (ByteMemory.bytesAt memory pc (encode mode form).length) = some form
  rw [current,form_roundtrip mode form legal]

end SmcTuring.Native.StringForm
