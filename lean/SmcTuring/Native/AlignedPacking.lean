module
public import SmcTuring.Native.SpacedCombinedImage
public import SmcTuring.Native.ReaderImage

public section

namespace SmcTuring.Native.AlignedPacking

/-- MASM ALIGN word-width followed by the generator's explicit byte padding. -/
@[expose] def alignPadding (mode : Mode) (start : Nat) : Nat :=
  (mode.wordBytes - start % mode.wordBytes) % mode.wordBytes

@[expose] def readerExtra (mode : Mode) : Nat :=
  (mode.wordBytes - (ReaderImage.prefixSize mode + moffsOperandOffset mode) % mode.wordBytes) % mode.wordBytes

@[expose] def readerStart (mode : Mode) (start : Nat) : Nat :=
  start + alignPadding mode start + readerExtra mode

@[expose] def scalarExtra (mode : Mode) : Nat := mode.wordBytes - moffsOperandOffset mode

@[expose] def scalarStart (mode : Mode) (start : Nat) : Nat :=
  start + alignPadding mode start + scalarExtra mode

@[expose] def scalarLabel (mode : Mode) (start : Nat) : Word mode :=
  Arithmetic.encodeNat mode (scalarStart mode start + moffsOperandOffset mode)

theorem alignment_small (mode : Mode) (start : Nat) : alignPadding mode start < mode.wordBytes := by
  cases mode <;> simp [alignPadding, Mode.wordBytes] <;> omega

theorem aligned_end (mode : Mode) (start : Nat) : (start + alignPadding mode start) % mode.wordBytes = 0 := by
  cases mode <;> simp only [alignPadding, Mode.wordBytes] <;> omega

theorem reader_extra_constant (mode : Mode) : readerExtra mode = (match mode with | .x86 => 2 | .x64 => 5) := by
  cases mode <;> rfl

theorem reader_field_aligned (mode : Mode) (start : Nat) :
    (readerStart mode start + ReaderImage.prefixSize mode + moffsOperandOffset mode) % mode.wordBytes = 0 := by
  have aligned := aligned_end mode start
  cases mode <;> simp only [readerStart, readerExtra, ReaderImage.prefixSize, moffsOperandOffset,
    wordPrefix, Mode.wordBytes] at * <;> omega

theorem scalar_extra_constant (mode : Mode) : scalarExtra mode = (match mode with | .x86 => 3 | .x64 => 6) := by
  cases mode <;> rfl

theorem scalar_field_aligned (mode : Mode) (start : Nat) :
    (scalarStart mode start + moffsOperandOffset mode) % mode.wordBytes = 0 := by
  have aligned := aligned_end mode start
  cases mode <;> simp only [scalarStart, scalarExtra, moffsOperandOffset, wordPrefix, Mode.wordBytes,
    List.length_cons, List.length_nil] at * <;> omega

theorem reader_label_aligned (mode : Mode) (start : Nat)
    (fits : readerStart mode start + ReaderImage.totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    (ReaderImage.label mode (readerStart mode start)).toNat % mode.wordBytes = 0 := by
  rw [ReaderImage.label_location mode (readerStart mode start) (Arithmetic.encodeNat mode 0) fits]
  exact reader_field_aligned mode start

theorem scalar_label_location (mode : Mode) (start : Nat)
    (fits : scalarStart mode start + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)) :
    (scalarLabel mode start).toNat = scalarStart mode start + moffsOperandOffset mode :=
  Arithmetic.encode_nat_toNat mode _ fits

theorem scalar_label_aligned (mode : Mode) (start : Nat)
    (fits : scalarStart mode start + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)) :
    (scalarLabel mode start).toNat % mode.wordBytes = 0 := by
  rw [scalar_label_location mode start fits]
  exact scalar_field_aligned mode start

end SmcTuring.Native.AlignedPacking
