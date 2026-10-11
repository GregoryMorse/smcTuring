module
public import SmcTuring.Native.StringDecodeImage
public import SmcTuring.Native.DwordDecodeImage
public import SmcTuring.Native.WordDecodeImage
public import SmcTuring.Native.StringPCSteps

public section
namespace SmcTuring.Native.StringStackImage
open LittleEndian

@[expose] def dwordEncode (mode : Mode) : StringDword.Form mode→List Byte
  | .string form => StringForm.encode mode form
  | .mixed form => MixedDword.encode mode form
  | .xorAccumulator d => DwordXor.encode d
@[expose] def dwordLegal (mode : Mode) : StringDword.Form mode→Prop
  | .string form => StringForm.Legal mode form
  | _ => True
@[expose] def controlEncode (mode : Mode) : StringControl.Form mode→List Byte
  | .previous form => dwordEncode mode form
  | .wideNegation d => WordNegation.encode mode d
@[expose] def controlLegal (mode : Mode) : StringControl.Form mode→Prop
  | .previous form => dwordLegal mode form
  | _ => True
@[expose] def encode (mode : Mode) : StringStack.Form mode→List Byte
  | .previous form => controlEncode mode form
  | .addSmall d v => WordAddImmediate.encode mode d v
@[expose] def Legal (mode : Mode) : StringStack.Form mode→Prop
  | .previous form => controlLegal mode form
  | _ => True

theorem mixed_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : MixedDword.Form mode)
    (fetched : MixedDword.fetch mode memory pc=some form) :
    ByteMemory.bytesAt memory pc (MixedDword.encode mode form).length=MixedDword.encode mode form := by
  unfold MixedDword.fetch at fetched
  cases selected : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) with
  | some count =>
    simp only [selected] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨arithmetic,parsed,same⟩
    rw [←same]
    exact DwordDecodeImage.arithmetic_fetch memory pc arithmetic parsed
  | none =>
    simp only [selected] at fetched
    cases mode with
    | x86 =>
      rcases Option.map_eq_some_iff.mp fetched with ⟨copy,parsed,same⟩
      rw [←same]
      exact DwordDecodeImage.copy_fetch .x86 memory pc copy parsed
    | x64 =>
      simp only at fetched
      split at fetched
      · rcases Option.bind_eq_some_iff.mp fetched with ⟨native,parsed,chosen⟩
        have image:=DecodeImage.native_fetch .x64 memory pc native parsed
        cases native with
        | memory operation d =>
          cases operation <;> simp only at chosen <;> cases chosen
          exact image
        | moffs => cases chosen
        | exchangeIndirect => cases chosen
        | callRelative => cases chosen
      · rcases Option.map_eq_some_iff.mp fetched with ⟨copy,parsed,same⟩
        rw [←same]
        exact DwordDecodeImage.copy_fetch .x64 memory pc copy parsed

theorem dword_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringDword.Form mode)
    (fetched : StringDword.fetch mode memory pc=some form) :
    ByteMemory.bytesAt memory pc (dwordEncode mode form).length=dwordEncode mode form ∧ dwordLegal mode form := by
  unfold StringDword.fetch at fetched
  cases selected : StringForm.fetch mode memory pc with
  | some value =>
    simp only [selected] at fetched
    rw [←Option.some.inj fetched]
    exact StringDecodeImage.fetch mode memory pc value selected
  | none =>
    simp only [selected] at fetched
    cases chosen : MixedDword.fetch mode memory pc with
    | some value =>
      simp only [chosen] at fetched
      rw [←Option.some.inj fetched]
      exact ⟨mixed_fetch mode memory pc value chosen,trivial⟩
    | none =>
      simp only [chosen] at fetched
      rcases Option.map_eq_some_iff.mp fetched with ⟨d,parsed,same⟩
      rw [←same]
      have image:=DwordXor.decode_image mode (ByteMemory.bytesAt memory pc 6) d parsed
      have size:=congrArg List.length image
      simp only [ByteMemory.bytes_at_length] at size
      change ByteMemory.bytesAt memory pc (DwordXor.encode d).length=DwordXor.encode d ∧ True
      rw [←size]
      exact ⟨image,trivial⟩

theorem control_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringControl.Form mode)
    (fetched : StringControl.fetch mode memory pc=some form) :
    ByteMemory.bytesAt memory pc (controlEncode mode form).length=controlEncode mode form ∧ controlLegal mode form := by
  unfold StringControl.fetch at fetched
  cases selected : StringDword.fetch mode memory pc with
  | some value =>
    simp only [selected] at fetched
    rw [←Option.some.inj fetched]
    exact dword_fetch mode memory pc value selected
  | none =>
    simp only [selected] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨d,parsed,same⟩
    rw [←same]
    exact ⟨WordDecodeImage.negation_fetch mode memory pc d parsed,trivial⟩

/-- Every actual fetched form yields its current exact byte image and legality;
neither a future image nor a later classifier result is assumed. -/
theorem fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringStack.Form mode)
    (fetched : StringStack.fetch mode memory pc=some form) :
    ByteMemory.bytesAt memory pc (encode mode form).length=encode mode form ∧ Legal mode form := by
  unfold StringStack.fetch at fetched
  cases selected : StringControl.fetch mode memory pc with
  | some value =>
    simp only [selected] at fetched
    rw [←Option.some.inj fetched]
    exact control_fetch mode memory pc value selected
  | none =>
    simp only [selected] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨pair,parsed,same⟩
    rw [←same]
    exact ⟨WordDecodeImage.addition_fetch mode memory pc pair parsed,trivial⟩

theorem string_size (mode : Mode) (form : StringForm.Form mode) :
    StringPCSteps.stringSize mode form=(StringForm.encode mode form).length := by
  cases form with
  | native form => exact (Native.instruction_length mode form).symm
  | initialize32 => rfl
  | exchangeIndex => rfl
  | subtractSmall => rfl
  | subtractFull => rfl
  | move => rfl

theorem dword_size (mode : Mode) (form : StringDword.Form mode) :
    StringPCSteps.dwordSize mode form=(dwordEncode mode form).length := by
  cases form with
  | string form => exact string_size mode form
  | mixed form => exact (MixedDword.encode_length mode form).symm
  | xorAccumulator => rfl

theorem control_size (mode : Mode) (form : StringControl.Form mode) :
    StringPCSteps.controlSize mode form=(controlEncode mode form).length := by
  cases form with
  | previous form => exact dword_size mode form
  | wideNegation d => exact (WordNegation.encode_length mode d).symm

theorem size (mode : Mode) (form : StringStack.Form mode) :
    StringPCSteps.size mode form=(encode mode form).length := by
  cases form with
  | previous form => exact control_size mode form
  | addSmall d v => exact (WordAddImmediate.encode_length mode d v).symm

end SmcTuring.Native.StringStackImage
