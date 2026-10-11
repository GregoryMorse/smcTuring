module
public import SmcTuring.Native.WordAddImmediate

public section
namespace SmcTuring.Native.WordDecodeImage
open LittleEndian

theorem negation (mode : Mode) (bytes : List Byte) (d : BitVec 32)
    (decoded : WordNegation.decode mode bytes=some d) : bytes=WordNegation.encode mode d := by
  cases mode <;> simp only [WordNegation.decode] at decoded
  all_goals
    split at decoded
    · rename_i payload
      rw [←word_encode_decode 4 payload d decoded]
      rfl
    · cases decoded

theorem negation_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32)
    (fetched : WordNegation.fetch mode memory pc=some d) :
    ByteMemory.bytesAt memory pc (WordNegation.encode mode d).length=WordNegation.encode mode d := by
  rw [WordNegation.encode_length]
  exact negation mode _ d fetched

theorem add_payload (bytes : List Byte) (pair : BitVec 32×Byte)
    (decoded : WordAddImmediate.payload bytes=some pair) : bytes=wordEncode 4 pair.1++[pair.2] := by
  unfold WordAddImmediate.payload at decoded
  rcases Option.bind_eq_some_iff.mp decoded with ⟨d,field,tail⟩
  split at tail
  · rename_i value trailing
    cases Option.some.inj tail
    rw [word_encode_decode 4 (bytes.take 4) d field,←trailing]
    exact (List.take_append_drop 4 bytes).symm
  · cases tail

theorem addition (mode : Mode) (bytes : List Byte) (pair : BitVec 32×Byte)
    (decoded : WordAddImmediate.decode mode bytes=some pair) : bytes=WordAddImmediate.encode mode pair.1 pair.2 := by
  cases mode <;> simp only [WordAddImmediate.decode] at decoded
  all_goals
    split at decoded
    · rename_i payload
      rw [add_payload payload pair decoded]
      simp [WordAddImmediate.encode,wordPrefix]
    · cases decoded

theorem addition_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (pair : BitVec 32×Byte)
    (fetched : WordAddImmediate.fetch mode memory pc=some pair) :
    ByteMemory.bytesAt memory pc (WordAddImmediate.encode mode pair.1 pair.2).length=WordAddImmediate.encode mode pair.1 pair.2 := by
  rw [WordAddImmediate.encode_length]
  exact addition mode _ pair fetched

end SmcTuring.Native.WordDecodeImage
