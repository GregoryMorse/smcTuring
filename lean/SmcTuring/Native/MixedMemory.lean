module
public import SmcTuring.Native.DwordCode

public section
namespace SmcTuring.Native.MixedMemory
open LittleEndian DwordCode
/-- A full-width read at a natural byte address; no truncation through x86
occurs when a DWORD field is mixed with a long-mode pointer field. -/
@[expose] def getWord (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) : Word mode :=
  BitVec.ofNat (8*mode.wordBytes) (pack (ByteMemory.bytesAt memory address mode.wordBytes))

theorem read_total (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) :
    ByteMemory.readWord mode memory address = some (getWord mode memory address) := by
  cases mode <;> rfl

theorem get_put (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) (value : Word mode) :
    getWord mode (ByteMemory.putWord mode memory address value) address = value := by
  have read := ByteMemory.read_put_word mode memory address value
  rw [read_total] at read
  exact Option.some.inj read

theorem put_get_back (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) :
    ByteMemory.putWord mode memory address (getWord mode memory address) = memory := by
  have encoded := word_encode_decode mode.wordBytes _ _ (read_total mode memory address)
  unfold ByteMemory.putWord
  rw [encoded]
  exact Writes.put_bytes_back memory address mode.wordBytes

theorem load_nat (mode : Mode) (memory : ByteMemory.Memory) (address : Nat)
    (fits : address < 2^(8*mode.wordBytes)) :
    Execution.load mode memory (Arithmetic.encodeNat mode address) = getWord mode memory address := by
  unfold Execution.load
  rw [Arithmetic.encode_nat_toNat mode address fits]
  rfl

theorem wide_after_dword (mode : Mode) (memory : ByteMemory.Memory) (written observed : Nat)
    (value : DwordCode.Dword)
    (separate : ∀ index : Fin mode.wordBytes, ¬ByteMemory.Inside written 4 (observed+index.val)) :
    getWord mode (DwordCode.put memory written value) observed = getWord mode memory observed := by
  have frame := ByteMemory.bytes_at_frame memory written (wordEncode 4 value) observed mode.wordBytes
    (by simpa only [word_encode_length] using separate)
  exact congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (pack bytes)) frame

theorem dword_after_wide (mode : Mode) (memory : ByteMemory.Memory) (written observed : Nat)
    (value : Word mode)
    (separate : ∀ index : Fin 4, ¬ByteMemory.Inside written mode.wordBytes (observed+index.val)) :
    DwordCode.get (ByteMemory.putWord mode memory written value) observed = DwordCode.get memory observed := by
  have frame := ByteMemory.bytes_at_frame memory written (wordEncode mode.wordBytes value) observed 4
    (by simpa only [word_encode_length] using separate)
  exact congrArg (fun bytes => BitVec.ofNat 32 (pack bytes)) frame

theorem stores_commute (mode : Mode) (memory : ByteMemory.Memory) (wide dword : Nat)
    (fullValue : Word mode) (smallValue : DwordCode.Dword)
    (separate : wide+mode.wordBytes ≤ dword ∨ dword+4 ≤ wide) :
    DwordCode.put (ByteMemory.putWord mode memory wide fullValue) dword smallValue =
      ByteMemory.putWord mode (DwordCode.put memory dword smallValue) wide fullValue := by
  apply Writes.put_bytes_commute
  intro position inside
  simp only [word_encode_length,ByteMemory.Inside] at inside ⊢
  rcases separate with before | after <;> omega

theorem wide_frame (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) (value : Word mode)
    (position : Nat) (outside : ¬ByteMemory.Inside address mode.wordBytes position) :
    ByteMemory.putWord mode memory address value position = memory position :=
  ByteMemory.put_frame _ _ _ _ (by simpa only [word_encode_length] using outside)

end SmcTuring.Native.MixedMemory
