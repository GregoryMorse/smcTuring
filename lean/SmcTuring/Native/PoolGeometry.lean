module
public import SmcTuring.Native.ImageInitialization

public section

namespace SmcTuring.Native.PoolGeometry

@[expose] def readerStride (mode : Mode) : Nat := match mode with | .x86 => 40 | .x64 => 56

theorem cursor_succ (mode : Mode) (kind : AlignedPool.Kind) (cursor index : Nat) :
    AlignedPool.cursorAt mode kind cursor (index + 1) = AlignedPool.next mode kind (AlignedPool.cursorAt mode kind cursor index) := by
  induction index generalizing cursor with
  | zero => rfl
  | succ index ih => exact ih (AlignedPool.next mode kind cursor)

theorem reader_next_start (mode : Mode) (top slot cursor : Nat) :
    AlignedPacking.readerStart mode (AlignedPool.next mode (.reader top slot) cursor) =
      AlignedPacking.readerStart mode cursor + readerStride mode := by
  have aligned := AlignedPacking.aligned_end mode cursor
  cases mode <;> simp only [AlignedPool.next, AlignedTemplates.readerEnd, AlignedPacking.readerStart,
    AlignedPacking.alignPadding, AlignedPacking.readerExtra, ReaderImage.prefixSize, moffsOperandOffset,
    wordPrefix, Mode.wordBytes, ReadCalleeImage.totalSize,
    readerStride, List.length_cons, List.length_nil] at * <;> omega

/-- The complete aligned readers advance by a fixed stride after the first
alignment; their entry positions do not depend on their target pointers. -/
theorem reader_start_affine (mode : Mode) (top slot cursor index : Nat) :
    AlignedPacking.readerStart mode (AlignedPool.cursorAt mode (.reader top slot) cursor index) =
      AlignedPacking.readerStart mode cursor + readerStride mode * index := by
  induction index generalizing cursor with
  | zero => simp only [AlignedPool.cursorAt, Nat.mul_zero, Nat.add_zero]
  | succ index ih =>
    change AlignedPacking.readerStart mode (AlignedPool.cursorAt mode (.reader top slot) (AlignedPool.next mode (.reader top slot) cursor) index) = _
    rw [ih, reader_next_start]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

theorem reader_bound (mode : Mode) (top slot cursor count index : Nat) (inside : index < count) :
    AlignedTemplates.readerEnd mode (AlignedPool.cursorAt mode (.reader top slot) cursor index) <=
      AlignedPool.cursorAt mode (.reader top slot) cursor count := by
  cases count with
  | zero => omega
  | succ last =>
    rw [cursor_succ]
    change AlignedPacking.readerStart mode (AlignedPool.cursorAt mode (.reader top slot) cursor index) + ReadCalleeImage.totalSize mode <=
      AlignedPacking.readerStart mode (AlignedPool.cursorAt mode (.reader top slot) cursor last) + ReadCalleeImage.totalSize mode
    rw [reader_start_affine, reader_start_affine]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) _

theorem scalar_end (mode : Mode) (cursor : Nat) :
    AlignedTemplates.scalarEnd mode cursor = AlignedPacking.scalarStart mode cursor + moffsOperandOffset mode + mode.wordBytes := by
  cases mode <;> simp only [AlignedTemplates.scalarEnd, instructionLength, moffsOperandOffset, wordPrefix,
    Mode.wordBytes, List.length_cons, List.length_nil, Nat.add_assoc]

theorem scalar_bound (mode : Mode) (cursor count index : Nat) (inside : index < count) :
    AlignedPacking.scalarStart mode (AlignedPool.cursorAt mode .scalar cursor index) + moffsOperandOffset mode + mode.wordBytes <=
      AlignedPool.cursorAt mode .scalar cursor count := by
  cases count with
  | zero => omega
  | succ last =>
    rw [cursor_succ]
    change _ <= AlignedTemplates.scalarEnd mode (AlignedPool.cursorAt mode .scalar cursor last)
    rw [scalar_end, MetadataGeometry.scalar_field_affine, MetadataGeometry.scalar_field_affine]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) _

end SmcTuring.Native.PoolGeometry
