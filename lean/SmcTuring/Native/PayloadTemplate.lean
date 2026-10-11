module
public import SmcTuring.Native.Protected

public section
namespace SmcTuring.Native.PayloadTemplate
open LittleEndian

/-- The fixed bytes before a complete mutable operand. The operand is always
read from current memory, including after a partial architectural write. -/
@[expose] def Prefix (memory : ByteMemory.Memory) (start : Nat) (fixed : List Byte) : Prop :=
  ByteMemory.bytesAt memory start fixed.length = fixed

theorem current (mode : Mode) (memory : ByteMemory.Memory) (start : Nat) (fixed : List Byte)
    (intact : Prefix memory start fixed) :
    ByteMemory.bytesAt memory start (fixed.length+mode.wordBytes) =
      fixed ++ wordEncode mode.wordBytes (Protected.wordAt mode memory (start+fixed.length)) := by
  rw [Protected.bytes_at_append, intact, Protected.word_at_encoded]

theorem frame (memory : ByteMemory.Memory) (start : Nat) (fixed : List Byte)
    (address : Nat) (bytes : List Byte) (intact : Prefix memory start fixed)
    (outside : ∀ index : Fin fixed.length, ¬ByteMemory.Inside address bytes.length (start+index.val)) :
    Prefix (ByteMemory.putBytes memory address bytes) start fixed := by
  rw [Prefix, ByteMemory.bytes_at_frame memory address bytes start fixed.length outside]
  exact intact

/-- Even a partial operand write leaves the fixed template bytes intact.
This statement checks the entire write window, not only its first address. -/
theorem operand_store (mode : Mode) (memory : ByteMemory.Memory) (start : Nat) (fixed : List Byte)
    (address : Nat) (bytes : List Byte) (intact : Prefix memory start fixed)
    (lower : start+fixed.length ≤ address)
    (upper : address+bytes.length ≤ start+fixed.length+mode.wordBytes) :
    Prefix (ByteMemory.putBytes memory address bytes) start fixed ∧
    ByteMemory.bytesAt (ByteMemory.putBytes memory address bytes) start (fixed.length+mode.wordBytes) =
      fixed ++ wordEncode mode.wordBytes
        (Protected.wordAt mode (ByteMemory.putBytes memory address bytes) (start+fixed.length)) ∧
    ∀ position, ByteMemory.Inside address bytes.length position →
      ByteMemory.Inside (start+fixed.length) mode.wordBytes position := by
  have kept := frame memory start fixed address bytes intact (by
    intro index inside
    have small := index.isLt
    unfold ByteMemory.Inside at inside
    omega)
  refine ⟨kept,current mode _ start fixed kept,?_⟩
  intro position inside
  unfold ByteMemory.Inside at *
  omega

theorem replace (mode : Mode) (memory : ByteMemory.Memory) (start : Nat) (fixed : List Byte)
    (intact : Prefix memory start fixed) (fresh : Word mode) :
    ByteMemory.bytesAt (ByteMemory.putWord mode memory (start+fixed.length) fresh)
      start (fixed.length+mode.wordBytes) = fixed ++ wordEncode mode.wordBytes fresh := by
  have kept := (operand_store mode memory start fixed (start+fixed.length)
    (wordEncode mode.wordBytes fresh) intact (by omega) (by simp only [word_encode_length];omega)).1
  change Prefix (ByteMemory.putWord mode memory (start+fixed.length) fresh) start fixed at kept
  rw [current mode _ start fixed kept,Protected.word_at_put]

end SmcTuring.Native.PayloadTemplate
