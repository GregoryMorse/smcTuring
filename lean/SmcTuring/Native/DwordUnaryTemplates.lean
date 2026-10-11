module
public import SmcTuring.Native.DwordOperandTemplates

public section
namespace SmcTuring.Native.DwordUnaryTemplates
open LittleEndian

inductive Kind where
  | negate | complement | sbbZero | xorAtAccumulator
  deriving DecidableEq, Repr
@[expose] def form (kind : Kind) (value : BitVec 32) : DwordArithmetic.Form :=
  match kind with
  | .negate => .negate value
  | .complement => .complement value
  | .sbbZero => .sbbZero value
  | .xorAtAccumulator => .xorAtAccumulator value
@[expose] def header (kind : Kind) : List Byte :=
  match kind with
  | .negate => [0xf7,0x1d]
  | .complement => [0xf7,0x15]
  | .sbbZero => [0x83,0x1d]
  | .xorAtAccumulator => [0x81,0x70,6]
@[expose] def trailer (kind : Kind) : List Byte := match kind with | .sbbZero => [0] | _ => []
@[expose] def span (kind : Kind) : Nat := (header kind).length+4+(trailer kind).length
@[expose] def field (kind : Kind) (pc : Nat) : Nat := pc+(header kind).length
@[expose] def Intact (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) : Prop :=
  PayloadTemplate.Prefix memory pc (header kind) ∧
  PayloadTemplate.Prefix memory (field kind pc+4) (trailer kind)

theorem shape (kind : Kind) (value : BitVec 32) :
    DwordArithmetic.encode (form kind value)=header kind++wordEncode 4 value++trailer kind := by
  cases kind <;> simp only [form,DwordArithmetic.encode,header,trailer,List.append_nil]

theorem length (kind : Kind) (value : BitVec 32) :
    (DwordArithmetic.encode (form kind value)).length=span kind := by
  simp only [shape,List.length_append,word_encode_length,span]

theorem initial (kind : Kind) (pc : Nat) (value : BitVec 32) (memory : ByteMemory.Memory)
    (present : ByteMemory.bytesAt memory pc (span kind)=DwordArithmetic.encode (form kind value)) :
    Intact kind pc memory := by
  have whole : ByteMemory.bytesAt memory pc (header kind++wordEncode 4 value++trailer kind).length=
      header kind++wordEncode 4 value++trailer kind := by
    simpa only [shape,List.length_append,word_encode_length,span] using present
  have a := StringWindow.packet_window memory pc [] (header kind) (wordEncode 4 value++trailer kind)
    (by simpa only [List.nil_append,List.append_assoc] using whole)
  have b := StringWindow.packet_window memory pc (header kind++wordEncode 4 value) (trailer kind) []
    (by simpa only [List.append_nil] using whole)
  exact ⟨by simpa only [PayloadTemplate.Prefix,List.length_nil,Nat.add_zero] using a,
    by simpa only [PayloadTemplate.Prefix,field,List.length_append,word_encode_length,Nat.add_assoc] using b⟩

theorem current (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) (intact : Intact kind pc memory) :
    ByteMemory.bytesAt memory pc (span kind)=DwordArithmetic.encode (form kind (DwordCode.get memory (field kind pc))) := by
  rcases intact with ⟨a,b⟩
  have encoded := Protected.word_at_encoded .x86 memory (field kind pc)
  change wordEncode 4 (DwordCode.get memory (field kind pc))=ByteMemory.bytesAt memory (field kind pc) 4 at encoded
  simp only [PayloadTemplate.Prefix,field,Nat.add_assoc] at a b encoded ⊢
  rw [shape]
  simp only [span,Nat.add_assoc,Protected.bytes_at_append]
  rw [a,←encoded,b]
  simp only [List.append_assoc]

theorem decodes (mode : Mode) (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory)
    (intact : Intact kind pc memory) :
    StringStack.fetch mode memory pc=some (StringStoreWrites.liftDword mode (StringMixed.canonical mode
      (.arithmetic (form kind (DwordCode.get memory (field kind pc)))))) := by
  have fetched := MixedDword.arithmetic_encoding mode memory pc (form kind (DwordCode.get memory (field kind pc)))
    (by simpa only [length] using current kind pc memory intact)
  exact StringStack.previous_fetch mode memory pc _
    (StringControl.previous_fetch mode memory pc _ (StringMixed.fetched mode memory pc _ fetched))

theorem mutable_store (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List Byte)
    (intact : Intact kind pc memory) (lower : field kind pc≤address) (upper : address+packet.length≤field kind pc+4) :
    Intact kind pc (ByteMemory.putBytes memory address packet) := by
  refine ⟨PayloadTemplate.frame _ _ _ _ _ intact.1 ?_,PayloadTemplate.frame _ _ _ _ _ intact.2 ?_⟩ <;>
    intro index inside <;> have bound := index.isLt <;>
    unfold ByteMemory.Inside at inside <;> simp only [field] at * <;> omega

theorem frame (kind : Kind) (pc : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List Byte)
    (intact : Intact kind pc memory) (outside : address+packet.length≤pc ∨ pc+span kind≤address) :
    Intact kind pc (ByteMemory.putBytes memory address packet) := by
  refine ⟨PayloadTemplate.frame _ _ _ _ _ intact.1 ?_,PayloadTemplate.frame _ _ _ _ _ intact.2 ?_⟩ <;>
    intro index inside <;> have bound := index.isLt <;>
    unfold ByteMemory.Inside at inside <;> simp only [field,span] at * <;> rcases outside with before | after <;> omega

end SmcTuring.Native.DwordUnaryTemplates
