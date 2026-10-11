module
public import SmcTuring.Native.DecodeImage
public import SmcTuring.Native.StringForm

public section
namespace SmcTuring.Native.StringDecodeImage
open LittleEndian StringForm

theorem core (mode : Mode) (opcode modrm : Byte) (payload : List Byte) (form : StringForm.Form mode)
    (decoded : coreDecode mode opcode modrm payload=some form) :
    wordPrefix mode++[opcode,modrm]++payload=StringForm.encode mode form ∧ Legal mode form := by
  unfold coreDecode at decoded
  split at decoded
  · rename_i tags
    rcases Option.map_eq_some_iff.mp decoded with ⟨d,field,same⟩
    cases same
    rw [←word_encode_decode 4 payload d field]
    rcases tags with ⟨rfl,rfl⟩
    simp [StringForm.encode,Legal]
  · split at decoded
    · rename_i tags
      rcases Option.map_eq_some_iff.mp decoded with ⟨d,field,same⟩
      cases same
      rw [←word_encode_decode 4 payload d field]
      rcases tags with ⟨rfl,rfl⟩
      simp [StringForm.encode,Legal]
    · split at decoded
      · rename_i tags
        rcases Option.bind_eq_some_iff.mp decoded with ⟨d,field,tail⟩
        split at tail
        · rename_i value trailing
          cases Option.some.inj tail
          have leading:=word_encode_decode 4 (payload.take 4) d field
          have bytes : payload=wordEncode 4 d++[value] := by
            rw [leading,←trailing]
            exact (List.take_append_drop 4 payload).symm
          rcases tags with ⟨rfl,rfl⟩
          simp [StringForm.encode,Legal,bytes,List.append_assoc]
        · cases tail
      · split at decoded
        · rename_i tags
          rcases Option.bind_eq_some_iff.mp decoded with ⟨d,first,tail⟩
          rcases Option.bind_eq_some_iff.mp tail with ⟨v,second,same⟩
          cases Option.some.inj same
          have bytes : payload=wordEncode 4 d++wordEncode 4 v := by
            rw [word_encode_decode 4 (payload.take 4) d first,word_encode_decode 4 (payload.drop 4) v second]
            exact (List.take_append_drop 4 payload).symm
          rcases tags with ⟨rfl,rfl⟩
          simp [StringForm.encode,Legal,bytes,List.append_assoc]
        · split at decoded
          · rename_i tags
            rcases Option.bind_eq_some_iff.mp decoded with ⟨d,first,tail⟩
            rcases Option.bind_eq_some_iff.mp tail with ⟨v,second,same⟩
            cases Option.some.inj same
            have bytes : payload=wordEncode 4 d++wordEncode 4 v := by
              rw [word_encode_decode 4 (payload.take 4) d first,word_encode_decode 4 (payload.drop 4) v second]
              exact (List.take_append_drop 4 payload).symm
            rcases tags with ⟨rfl,rfl,rfl⟩
            simp [StringForm.encode,Legal,wordPrefix,Appendix.ByteCode.encode,Appendix.ByteCode.ImmediateOp.tag,bytes]
          · cases decoded

theorem packet (mode : Mode) (bytes : List Byte) (form : StringForm.Form mode)
    (decoded : corePacketDecode mode bytes=some form) :
    wordPrefix mode++bytes=StringForm.encode mode form ∧ Legal mode form := by
  cases bytes with
  | nil => cases decoded
  | cons opcode rest =>
    simp only [corePacketDecode] at decoded
    split at decoded
    · cases rest with
      | nil => cases decoded
      | cons modrm payload => simpa only [List.append_assoc,List.cons_append,List.nil_append] using core mode opcode modrm payload form decoded
    · cases decoded

theorem extra (mode : Mode) (bytes : List Byte) (form : StringForm.Form mode)
    (decoded : extraDecode mode bytes=some form) : bytes=StringForm.encode mode form ∧ Legal mode form := by
  unfold extraDecode at decoded
  split at decoded
  · cases Option.some.inj decoded
    simp_all [StringForm.encode,Legal,StringPlan.opcode,StringPlan.Legal]
  · split at decoded
    · cases Option.some.inj decoded
      simp_all [StringForm.encode,Legal,StringPlan.opcode,StringPlan.Legal]
    · split at decoded
      · cases Option.some.inj decoded
        simp_all [StringForm.encode,Legal,StringPlan.opcode,StringPlan.Legal]
      · split at decoded
        · rename_i selected
          cases Option.some.inj decoded
          rcases selected with ⟨rfl,rfl⟩
          simp [StringForm.encode,Legal,StringPlan.opcode,StringPlan.Legal]
        · cases mode with
          | x86 => simpa only [wordPrefix,List.nil_append] using packet .x86 bytes form decoded
          | x64 =>
            cases bytes with
            | nil => cases decoded
            | cons rex rest =>
              simp only at decoded
              split at decoded
              · rename_i selected
                have result:=packet .x64 rest form decoded
                simpa only [wordPrefix,List.cons_append,List.nil_append,selected] using result
              · cases decoded

theorem decode (mode : Mode) (bytes : List Byte) (form : StringForm.Form mode)
    (decoded : StringForm.decode mode bytes=some form) : bytes=StringForm.encode mode form ∧ Legal mode form := by
  unfold StringForm.decode at decoded
  cases selected : extraDecode mode bytes with
  | some value =>
    simp only [selected] at decoded
    exact extra mode bytes form (selected.trans decoded)
  | none =>
    simp only [selected] at decoded
    rcases Option.map_eq_some_iff.mp decoded with ⟨native,parsed,same⟩
    cases same
    exact ⟨DecodeImage.native mode bytes native parsed,trivial⟩

theorem fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (fetched : StringForm.fetch mode memory pc=some form) :
    ByteMemory.bytesAt memory pc (StringForm.encode mode form).length=StringForm.encode mode form ∧ Legal mode form := by
  unfold StringForm.fetch at fetched
  rcases Option.bind_eq_some_iff.mp fetched with ⟨count,classified,parsed⟩
  have image:=decode mode (ByteMemory.bytesAt memory pc count) form parsed
  have size:=congrArg List.length image.1
  simp only [ByteMemory.bytes_at_length] at size
  rw [←size]
  exact image

end SmcTuring.Native.StringDecodeImage
