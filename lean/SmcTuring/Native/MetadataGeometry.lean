module
public import SmcTuring.Native.ByteLengths

public section

namespace SmcTuring.Native.MetadataGeometry

open RoleInitialization

theorem scalar_step (mode : Mode) (cursor : Nat) :
    AlignedPool.next mode .scalar cursor = cursor + AlignedPacking.alignPadding mode cursor + mode.stride := by
  cases mode <;> simp only [AlignedPool.next, AlignedTemplates.scalarEnd, AlignedPacking.scalarStart,
    AlignedPacking.scalarExtra, instructionLength, moffsOperandOffset, wordPrefix, Mode.wordBytes, Mode.stride,
    List.length_cons, List.length_nil]

theorem scalar_step_aligned (mode : Mode) (cursor : Nat) :
    AlignedPacking.alignPadding mode (AlignedPool.next mode .scalar cursor) = 0 := by
  have aligned := AlignedPacking.aligned_end mode cursor
  rw [scalar_step]
  cases mode <;> simp only [AlignedPacking.alignPadding, Mode.wordBytes, Mode.stride] at * <;> omega

/-- Every metadata operand follows the same affine stride, even when the first
storage instruction needs alignment padding. -/
theorem scalar_field_affine (mode : Mode) (cursor index : Nat) :
    AlignedPacking.scalarStart mode (AlignedPool.cursorAt mode .scalar cursor index) + moffsOperandOffset mode =
      cursor + AlignedPacking.alignPadding mode cursor + mode.wordBytes + mode.stride * index := by
  induction index generalizing cursor with
  | zero =>
    cases mode <;> simp only [AlignedPool.cursorAt, AlignedPacking.scalarStart, AlignedPacking.scalarExtra,
      moffsOperandOffset, wordPrefix, Mode.wordBytes, Mode.stride, List.length_cons, List.length_nil]
  | succ index ih =>
    change AlignedPacking.scalarStart mode (AlignedPool.cursorAt mode .scalar (AlignedPool.next mode .scalar cursor) index) + _ = _
    rw [ih, scalar_step_aligned, scalar_step]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

theorem field_affine (mode : Mode) (layout : Layout) (role : Field) :
    fieldPosition mode layout role = layout.metadataStart + AlignedPacking.alignPadding mode layout.metadataStart +
      mode.wordBytes + mode.stride * role.index.val := scalar_field_affine mode layout.metadataStart role.index.val

theorem field_index_injective : Function.Injective Field.index := by
  intro first second same
  have lookup := congrArg (fun index : Fin 13 => fields[index.val]'(by rw [field_count]; exact index.isLt)) same
  simpa only [field_at_index] using lookup

theorem field_position_injective (mode : Mode) (layout : Layout) : Function.Injective (fieldPosition mode layout) := by
  intro first second same
  rw [field_affine, field_affine] at same
  have positive : 0 < mode.stride := by cases mode <;> decide
  apply field_index_injective
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left positive (Nat.add_left_cancel same)

/-- Once finite address capacity is checked, distinct logical metadata roles
have distinct actual encoded operand addresses. -/
theorem field_word_injective (mode : Mode) (layout : Layout)
    (fits : forall role, fieldPosition mode layout role < 2 ^ (8 * mode.wordBytes)) :
    Function.Injective (fun role => Arithmetic.encodeNat mode (fieldPosition mode layout role)) := by
  intro first second same
  apply field_position_injective mode layout
  have positions := congrArg (fun word : Word mode => word.toNat) same
  simpa only [Arithmetic.encode_nat_toNat mode _ (fits first), Arithmetic.encode_nat_toNat mode _ (fits second)] using positions

end SmcTuring.Native.MetadataGeometry
