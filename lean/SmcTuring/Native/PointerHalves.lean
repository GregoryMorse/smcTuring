module
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.ByteWindow
public import SmcTuring.X64.HalfWords

public section
namespace SmcTuring.Native.PointerHalves
open LittleEndian

theorem pack_append (low high : List Byte) :
    pack (low++high) = pack low+256^low.length*pack high := by
  induction low with
  | nil => simp [pack]
  | cons byte rest ih =>
    simp only [List.cons_append,pack,List.length_cons,Nat.pow_succ,ih,Nat.mul_add]
    simp [Nat.mul_comm,Nat.mul_assoc,Nat.add_assoc]

/-- Consecutive four-byte reads are exactly the two halves of the full
little-endian pointer read, at natural addresses without x86 truncation. -/
theorem split_get (memory : ByteMemory.Memory) (address : Nat) :
    MixedMemory.getWord .x64 memory address =
      X64.HalfWords.pack (DwordCode.get memory address) (DwordCode.get memory (address+4)) := by
  have fullBound : pack (ByteMemory.bytesAt memory address 8) < 2^64 := by
    simpa only [ByteMemory.bytes_at_length,radix_power] using pack_bound (ByteMemory.bytesAt memory address 8)
  have lowBound : pack (ByteMemory.bytesAt memory address 4) < 2^32 := by
    simpa only [ByteMemory.bytes_at_length,radix_power] using pack_bound (ByteMemory.bytesAt memory address 4)
  have highBound : pack (ByteMemory.bytesAt memory (address+4) 4) < 2^32 := by
    simpa only [ByteMemory.bytes_at_length,radix_power] using pack_bound (ByteMemory.bytesAt memory (address+4) 4)
  have bytes : ByteMemory.bytesAt memory address 8 =
      ByteMemory.bytesAt memory address 4 ++ ByteMemory.bytesAt memory (address+4) 4 :=
    ByteWindow.append memory address 4 4
  apply BitVec.eq_of_toNat_eq
  simp only [MixedMemory.getWord,Mode.wordBytes,DwordCode.get,X64.HalfWords.pack,
    BitVec.toNat_ofNat,BitVec.toNat_append,Nat.mod_eq_of_lt fullBound,
    Nat.mod_eq_of_lt lowBound,Nat.mod_eq_of_lt highBound]
  rw [bytes,pack_append,ByteMemory.bytes_at_length]
  rw [←Nat.shiftLeft_add_eq_or_of_lt lowBound]
  simp [Nat.shiftLeft_eq,Nat.mul_comm,Nat.add_comm]

theorem low_get (memory : ByteMemory.Memory) (address : Nat) :
    DwordCode.get memory address = X64.HalfWords.low (MixedMemory.getWord .x64 memory address) := by
  rw [split_get,X64.HalfWords.low_pack]

theorem high_get (memory : ByteMemory.Memory) (address : Nat) :
    DwordCode.get memory (address+4) = X64.HalfWords.high (MixedMemory.getWord .x64 memory address) := by
  rw [split_get,X64.HalfWords.high_pack]

end SmcTuring.Native.PointerHalves
