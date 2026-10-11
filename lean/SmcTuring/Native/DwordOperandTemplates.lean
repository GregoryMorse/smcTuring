module
public import SmcTuring.Native.PairedPayloadTemplate
public import SmcTuring.Native.StringMixedWrites

public section
namespace SmcTuring.Native.DwordOperandTemplates
open LittleEndian

inductive Kind where
  | store | subtract | bitXor | bitAnd | bitOr
  deriving DecidableEq, Repr

@[expose] def form (kind : Kind) (displacement value : BitVec 32) : DwordArithmetic.Form :=
  match kind with
  | .store => .store displacement value
  | .subtract => .subtract displacement value
  | .bitXor => .bitXor displacement value
  | .bitAnd => .bitAnd displacement value
  | .bitOr => .bitOr displacement value
@[expose] def header (kind : Kind) : List Byte :=
  match kind with
  | .store => [0xc7,0x05]
  | .subtract => [0x81,0x2d]
  | .bitXor => [0x81,0x35]
  | .bitAnd => [0x81,0x25]
  | .bitOr => [0x81,0x0d]
@[expose] def Intact (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) : Prop :=
  PayloadTemplate.Prefix memory pc (header kind)

theorem header_length (kind : Kind) : (header kind).length=2 := by cases kind <;> rfl

theorem shape (kind : Kind) (displacement value : BitVec 32) :
    DwordArithmetic.encode (form kind displacement value)=header kind++wordEncode 4 displacement++wordEncode 4 value := by
  cases kind <;> rfl

theorem length (kind : Kind) (displacement value : BitVec 32) :
    (DwordArithmetic.encode (form kind displacement value)).length=10 := by
  rw [shape]
  simp only [List.length_append,header_length,word_encode_length]

theorem initial (kind : Kind) (pc : Nat) (displacement value : BitVec 32) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory pc 10=DwordArithmetic.encode (form kind displacement value)) :
    Intact kind pc memory := by
  have h := StringWindow.packet_window memory pc [] (header kind) (wordEncode 4 displacement++wordEncode 4 value)
    (by simpa only [List.nil_append,List.append_assoc,List.length_append,header_length,word_encode_length,shape] using packet)
  simpa only [Intact,PayloadTemplate.Prefix,List.length_nil,Nat.add_zero] using h

/-- Both displacement and immediate may be partially rewritten. Each full
current DWORD is decoded from this memory, preserving the original opcode. -/
theorem current (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) (intact : Intact kind pc memory) :
    ByteMemory.bytesAt memory pc 10=DwordArithmetic.encode
      (form kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6))) := by
  have pair : PairedPayloadTemplate.Intact .x86 memory pc (header kind) [] [] := by
    refine ⟨intact,?_,?_⟩ <;> simp [PayloadTemplate.Prefix,ByteMemory.bytesAt]
  have h := PairedPayloadTemplate.current .x86 memory pc (header kind) [] [] pair
  rw [shape]
  simpa only [PairedPayloadTemplate.span,PairedPayloadTemplate.secondField,PairedPayloadTemplate.firstField,
    header_length,List.length_nil,Mode.wordBytes,Nat.add_zero,List.append_nil,Nat.reduceAdd,
    Protected.wordAt,DwordCode.get] using h

theorem decodes (mode : Mode) (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory)
    (intact : Intact kind pc memory) :
    StringStack.fetch mode memory pc=some (StringStoreWrites.liftDword mode
      (StringMixed.canonical mode (.arithmetic
        (form kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6)))))) := by
  have packet := current kind pc memory intact
  have fetched := MixedDword.arithmetic_encoding mode memory pc
    (form kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6)))
    (by simpa only [length] using packet)
  exact StringStack.previous_fetch mode memory pc _
    (StringControl.previous_fetch mode memory pc _ (StringMixed.fetched mode memory pc _ fetched))

theorem mutable_store (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List Byte) (intact : Intact kind pc memory)
    (lower : pc+2≤address) (upper : address+packet.length≤pc+10) :
    Intact kind pc (ByteMemory.putBytes memory address packet) ∧
    ∀ position,ByteMemory.Inside address packet.length position → ByteMemory.Inside (pc+2) 8 position := by
  constructor
  · apply PayloadTemplate.frame memory pc (header kind) address packet intact
    intro index inside
    have bound : index.val<2 := by simpa only [header_length] using index.isLt
    unfold ByteMemory.Inside at inside
    omega
  · intro position inside
    unfold ByteMemory.Inside at *
    omega

theorem frame (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List Byte) (intact : Intact kind pc memory)
    (outside : address+packet.length≤pc ∨ pc+10≤address) :
    Intact kind pc (ByteMemory.putBytes memory address packet) := by
  apply PayloadTemplate.frame memory pc (header kind) address packet intact
  intro index inside
  have bound : index.val<2 := by simpa only [header_length] using index.isLt
  unfold ByteMemory.Inside at inside
  rcases outside with before | after <;> omega

end SmcTuring.Native.DwordOperandTemplates
