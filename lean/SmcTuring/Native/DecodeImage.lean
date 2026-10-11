module
public import SmcTuring.Native.DwordArithmetic

public section
namespace SmcTuring.Native.DecodeImage
open LittleEndian

theorem payload (operation : MemoryOp) (bytes : List Byte) (displacement : BitVec 32)
    (decoded : decodeMemoryPayload operation bytes = some displacement) :
    bytes = wordEncode 4 displacement ++ operation.trailer := by
  unfold decodeMemoryPayload at decoded
  split at decoded
  · rename_i trailing
    have leading := word_encode_decode 4 (bytes.take 4) displacement decoded
    rw [leading,←trailing]
    exact (List.take_append_drop 4 bytes).symm
  · cases decoded

theorem tag (opcode modrm : Byte) (operation : MemoryOp)
    (decoded : operationOfTag opcode modrm = some operation) :
    opcode = operation.tag.1 ∧ modrm = operation.tag.2 := by
  unfold operationOfTag at decoded
  split at decoded <;> cases decoded <;>
    constructor <;> apply BitVec.eq_of_toNat_eq <;> simp_all [MemoryOp.tag]

@[expose] def coreBytes (mode : Mode) : Form mode → List Byte
  | .moffs address => [0xa3] ++ wordEncode mode.wordBytes address
  | .memory operation displacement => [operation.tag.1,operation.tag.2] ++ wordEncode 4 displacement ++ operation.trailer
  | .exchangeIndirect => [0x87,0]
  | .callRelative displacement => [0xe8] ++ wordEncode 4 displacement
@[expose] def CoreLegal (mode : Mode) : Form mode → Prop
  | .memory operation _ => operation ≠ .callIndirect
  | .callRelative _ => False
  | _ => True

theorem core (mode : Mode) (bytes : List Byte) (form : Form mode)
    (decoded : decodeCore mode bytes = some form) : bytes = coreBytes mode form ∧ CoreLegal mode form := by
  cases bytes with
  | nil => cases decoded
  | cons opcode rest =>
    simp only [decodeCore] at decoded
    split at decoded
    · rename_i isMoffs
      rcases Option.map_eq_some_iff.mp decoded with ⟨address,value,same⟩
      cases same
      rw [←word_encode_decode mode.wordBytes rest address value,isMoffs]
      exact ⟨rfl,trivial⟩
    · cases rest with
      | nil => cases decoded
      | cons modrm bytes =>
        simp only at decoded
        split at decoded
        · rename_i exchange
          have same := Option.some.inj decoded
          subst form
          rcases exchange with ⟨rfl,rfl,rfl⟩
          exact ⟨rfl,trivial⟩
        · rcases Option.bind_eq_some_iff.mp decoded with ⟨operation,op,decoded⟩
          split at decoded
          · cases decoded
          · rename_i allowed
            rcases Option.map_eq_some_iff.mp decoded with ⟨displacement,field,same⟩
            cases same
            have tags := tag opcode modrm operation op
            rw [tags.1,tags.2,payload operation bytes displacement field]
            exact ⟨rfl,allowed⟩

theorem core_prefix (mode : Mode) (form : Form mode) (legal : CoreLegal mode form) :
    encode mode form = wordPrefix mode ++ coreBytes mode form := by
  cases form with
  | moffs address => simp [encode,coreBytes,List.append_assoc]
  | memory operation displacement =>
    simp only [CoreLegal] at legal
    simp [encode,coreBytes,MemoryOp.prefix,legal,List.append_assoc]
  | exchangeIndirect => rfl
  | callRelative displacement => cases legal

theorem native (mode : Mode) (bytes : List Byte) (form : Form mode)
    (decoded : decode mode bytes = some form) : bytes = encode mode form := by
  cases bytes with
  | nil => cases decoded
  | cons opcode rest =>
    simp only [decode] at decoded
    split at decoded
    · rename_i isCall
      rcases Option.map_eq_some_iff.mp decoded with ⟨displacement,field,same⟩
      cases same
      rw [←word_encode_decode 4 rest displacement field,isCall]
      rfl
    · split at decoded
      · rename_i indirect
        cases rest with
        | nil => cases decoded
        | cons modrm bytes =>
          simp only at decoded
          split at decoded
          · rename_i callTag
            rcases Option.map_eq_some_iff.mp decoded with ⟨displacement,field,same⟩
            cases same
            rw [payload .callIndirect bytes displacement field,indirect,callTag]
            rfl
          · cases decoded
      · cases mode with
        | x86 =>
          simp only at decoded
          exact (core .x86 (opcode::rest) form decoded).1.trans (core_prefix .x86 form (core .x86 _ form decoded).2).symm
        | x64 =>
          simp only at decoded
          split at decoded
          · rename_i rex
            have image := core .x64 rest form decoded
            rw [rex,image.1,core_prefix .x64 form image.2]
            rfl
          · cases decoded

theorem native_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode)
    (fetched : Fetch.fetch mode memory pc = some form) :
    ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form := by
  unfold Fetch.fetch at fetched
  rcases Option.bind_eq_some_iff.mp fetched with ⟨count,_,decoded⟩
  have image := native mode (ByteMemory.bytesAt memory pc count) form decoded
  have length := congrArg List.length image
  simp only [ByteMemory.bytes_at_length] at length
  rw [←length]
  exact image

end SmcTuring.Native.DecodeImage
