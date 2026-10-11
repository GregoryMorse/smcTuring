module
public import SmcTuring.Native.DecodeImage

public section
namespace SmcTuring.Native.DwordDecodeImage
open LittleEndian

theorem two_words (constructor : BitVec 32 → BitVec 32 → DwordArithmetic.Form)
    (bytes : List Byte) (form : DwordArithmetic.Form)
    (decoded : DwordArithmetic.twoWords constructor bytes = some form) :
    ∃ d v, constructor d v = form ∧ bytes = wordEncode 4 d ++ wordEncode 4 v := by
  unfold DwordArithmetic.twoWords at decoded
  rcases Option.bind_eq_some_iff.mp decoded with ⟨d,first,decoded⟩
  rcases Option.bind_eq_some_iff.mp decoded with ⟨v,second,same⟩
  refine ⟨d,v,Option.some.inj same,?_⟩
  rw [word_encode_decode 4 _ d first,word_encode_decode 4 _ v second]
  exact (List.take_append_drop 4 bytes).symm

theorem arithmetic (bytes : List Byte) (form : DwordArithmetic.Form)
    (decoded : DwordArithmetic.decode bytes = some form) : bytes = DwordArithmetic.encode form := by
  unfold DwordArithmetic.decode at decoded
  split at decoded
  · rcases two_words .store _ _ decoded with ⟨d,v,same,parts⟩
    cases same
    simp_all [DwordArithmetic.encode]
  · rcases two_words .subtract _ _ decoded with ⟨d,v,same,parts⟩
    cases same
    simp_all [DwordArithmetic.encode]
  · rcases two_words .bitXor _ _ decoded with ⟨d,v,same,parts⟩
    cases same
    simp_all [DwordArithmetic.encode]
  · rcases two_words .bitAnd _ _ decoded with ⟨d,v,same,parts⟩
    cases same
    simp_all [DwordArithmetic.encode]
  · rcases two_words .bitOr _ _ decoded with ⟨d,v,same,parts⟩
    cases same
    simp_all [DwordArithmetic.encode]
  · rcases Option.map_eq_some_iff.mp decoded with ⟨d,word,same⟩
    cases same
    have parts := word_encode_decode 4 _ d word
    simp_all [DwordArithmetic.encode]
  · rcases Option.map_eq_some_iff.mp decoded with ⟨d,word,same⟩
    cases same
    have parts := word_encode_decode 4 _ d word
    simp_all [DwordArithmetic.encode]
  · rename_i rest
    split at decoded
    · rename_i suffix
      rcases Option.map_eq_some_iff.mp decoded with ⟨d,word,same⟩
      cases same
      have leading := word_encode_decode 4 _ d word
      have parts : rest = wordEncode 4 d ++ [0] := by
        rw [leading,←suffix];exact (List.take_append_drop 4 _).symm
      simp only [DwordArithmetic.encode,parts,List.cons_append,List.nil_append] <;> rfl
    · cases decoded
  · rcases Option.map_eq_some_iff.mp decoded with ⟨v,word,same⟩
    cases same
    have parts := word_encode_decode 4 _ v word
    simp_all [DwordArithmetic.encode]
  · cases decoded

theorem arithmetic_fetch (memory : ByteMemory.Memory) (pc : Nat) (form : DwordArithmetic.Form)
    (fetched : DwordArithmetic.fetch memory pc = some form) :
    ByteMemory.bytesAt memory pc (DwordArithmetic.encode form).length = DwordArithmetic.encode form := by
  unfold DwordArithmetic.fetch at fetched
  rcases Option.bind_eq_some_iff.mp fetched with ⟨count,_,decoded⟩
  have image := arithmetic (ByteMemory.bytesAt memory pc count) form decoded
  have length := congrArg List.length image
  simp only [ByteMemory.bytes_at_length] at length
  rw [←length];exact image

theorem copy (mode : Mode) (bytes : List Byte) (form : DwordCode.Form mode)
    (decoded : DwordCode.decode mode bytes = some form) : bytes = DwordCode.encode mode form := by
  unfold DwordCode.decode at decoded
  rcases Option.bind_eq_some_iff.mp decoded with ⟨native,current,decoded⟩
  have image := (DecodeImage.core mode bytes native current).1
  cases native with
  | moffs address =>
    have same := Option.some.inj decoded
    cases same
    exact image
  | memory operation displacement =>
    cases operation <;> simp only at decoded
    all_goals try cases decoded
    all_goals exact image
  | exchangeIndirect => cases decoded
  | callRelative displacement => cases decoded

theorem copy_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : DwordCode.Form mode)
    (fetched : DwordCode.fetch mode memory pc = some form) :
    ByteMemory.bytesAt memory pc (DwordCode.encode mode form).length = DwordCode.encode mode form := by
  have image := copy mode _ form fetched
  have length := congrArg List.length image
  simp only [ByteMemory.bytes_at_length] at length
  rw [←length];exact image

end SmcTuring.Native.DwordDecodeImage
