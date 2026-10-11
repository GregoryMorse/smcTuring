module
public import SmcTuring.Appendix.ConstantShape
public import SmcTuring.Appendix.ConstantRegions

public section
namespace SmcTuring.Appendix.ConstantGeometry
open ConstantImage
open ConstantShape (Active)

instance (value : Machine32.Word) : Decidable (Active value) := by
  change Decidable (value ≠ 0 ∧ ConstantAlgebra.rest value ≠ 0)
  infer_instance

/-- Operand-independent byte size: layout requires no fixed-point assumption. -/
@[expose] def length (value : Machine32.Word) : Nat := ConstantData.span (ConstantWords.program 0 1 value)
@[expose] def data (start : Nat) (value : Machine32.Word) : Nat := start + length value + 7
@[expose] def scratch (start : Nat) (value : Machine32.Word) : Nat :=
  if Active value then start + length value - 4 else start + length value + 17
@[expose] def ops (start : Nat) (value : Machine32.Word) : List ConstantWords.Instruction :=
  ConstantWords.program (data start value) (scratch start value) value
@[expose] def dataOwner (start : Nat) (value input : Machine32.Word) : Packet :=
  .common (.common (.immediate .store (FieldRefinement.address (data start value)) input))
@[expose] def scratchOwner (start : Nat) (value seed : Machine32.Word) : Packet :=
  .common (.addImmediate (FieldRefinement.address (data start value)) seed)
@[expose] def storage (start : Nat) (value input seed : Machine32.Word) : List Packet :=
  dataOwner start value input :: (if Active value then [] else [scratchOwner start value seed])
/-- The one-byte gap is the comparison harness RET, outside the pure trace. -/
@[expose] def whole (start : Nat) (value input seed : Machine32.Word) : List Entry :=
  ConstantData.entries start (ops start value) ++
  ConstantPacking.place (start + length value + 1) (storage start value input seed)
@[expose] def extent (value : Machine32.Word) : Nat := length value + if Active value then 11 else 21

theorem ops_span (start : Nat) (value : Machine32.Word) : ConstantData.span (ops start value) = length value := by
  exact ConstantShape.program_span_independent _ _ 0 1 value

theorem storage_size (start : Nat) (value input seed : Machine32.Word) :
    ConstantPacking.size (storage start value input seed) = if Active value then 10 else 20 := by
  by_cases active : Active value
  · simp only [storage, ite_eq_left active]
    rfl
  · simp only [storage, ite_eq_right active]
    rfl

theorem linked (start : Nat) (value : Machine32.Word) : ConstantData.Linked start (ops start value) := by
  by_cases active : Active value
  · apply ConstantShape.active_linked _ _ start value active
    have size := ConstantShape.active_span 0 1 value active
    change scratch start value + 4 = start + ConstantData.span (ops start value)
    rw [ops_span]
    simp only [scratch, ite_eq_left active]
    change 10 ≤ length value at size
    omega
  · exact ConstantShape.plain_linked _ (ConstantShape.inactive_plain _ _ value active) start

theorem placed (start : Nat) (value input seed : Machine32.Word) :
    ∀ entry ∈ ConstantData.entries start (ops start value), entry ∈ whole start value input seed := by
  intro entry member
  exact List.mem_append_left _ member

theorem separated (start : Nat) (value input seed : Machine32.Word) : Separated (whole start value input seed) := by
  apply ConstantRegions.separated_append _ _ (ConstantPacking.placed_separated _ _) (ConstantPacking.placed_separated _ _)
  intro first firstMember second secondMember
  have firstBound := ConstantPacking.placed_upper _ start first firstMember
  have secondBound := ConstantPacking.placed_lower _ (start + length value + 1) second secondMember
  change first.pc + first.bytes.length ≤ start + ConstantData.span (ops start value) at firstBound
  rw [ops_span] at firstBound
  omega

theorem capacity (start : Nat) (value input seed : Machine32.Word)
    (fits : start + extent value ≤ 2 ^ 32) :
    ∀ entry ∈ whole start value input seed, entry.pc + entry.bytes.length ≤ 2 ^ 32 := by
  intro entry member
  change entry ∈ ConstantData.entries start (ops start value) ++ _ at member
  rcases List.mem_append.mp member with pure | inactive
  · have bound := ConstantPacking.placed_upper _ start entry pure
    change entry.pc + entry.bytes.length ≤ start + ConstantData.span (ops start value) at bound
    rw [ops_span] at bound
    unfold extent at fits
    split at fits <;> omega
  · have bound := ConstantPacking.placed_upper _ (start + length value + 1) entry inactive
    rw [storage_size] at bound
    unfold extent at fits
    by_cases active : Active value
    · rw [ite_eq_left active] at bound fits
      omega
    · rw [ite_eq_right active] at bound fits
      omega

theorem data_member (start : Nat) (value input seed : Machine32.Word) :
    (⟨start + length value + 1, dataOwner start value input⟩ : Entry) ∈ whole start value input seed := by
  apply List.mem_append_right
  apply List.mem_cons.mpr
  exact Or.inl rfl

theorem data_owned (start : Nat) (value input seed : Machine32.Word) : Owned (whole start value input seed) (data start value) := by
  refine ⟨⟨start + length value + 1, dataOwner start value input⟩, data_member start value input seed, ?_⟩
  change data start value ∈ [start + length value + 1 + 6]
  apply List.mem_singleton.mpr
  unfold data
  omega

theorem scratch_owned (start : Nat) (value input seed : Machine32.Word) : Owned (whole start value input seed) (scratch start value) := by
  by_cases active : Active value
  · have operand : scratch start value + 4 = start + ConstantData.span (ops start value) := by
      rw [ops_span]
      simp only [scratch, ite_eq_left active]
      have size := ConstantShape.active_span 0 1 value active
      change 10 ≤ length value at size
      omega
    rcases ConstantShape.active_owned _ _ start value active operand with ⟨owner, member, field⟩
    exact ⟨owner, placed start value input seed owner member, field⟩
  · refine ⟨⟨start + length value + 11, scratchOwner start value seed⟩, ?_, ?_⟩
    · apply List.mem_append_right
      simp only [storage, ite_eq_right active, ConstantPacking.place]
      apply List.mem_cons.mpr
      apply Or.inr
      apply List.mem_cons.mpr
      apply Or.inl
      have bytes : (ConstantByteCode.encode (dataOwner start value input).initial).length = 10 := rfl
      rw [bytes]
    · change scratch start value ∈ [start + length value + 11 + 6]
      apply List.mem_singleton.mpr
      simp only [scratch, ite_eq_right active]

theorem distinct (start : Nat) (value : Machine32.Word) : scratch start value ≠ data start value := by
  unfold scratch data
  split <;> omega

theorem code_fits (start : Nat) (value : Machine32.Word) (fits : start + extent value ≤ 2 ^ 32) :
    start + ConstantData.span (ops start value) < 2 ^ 32 := by
  rw [ops_span]
  unfold extent at fits
  split at fits <;> omega

theorem two_field_layout (start : Nat) (value input seed : Machine32.Word)
    (fits : start + extent value ≤ 2 ^ 32) :
    FieldRefinement.Layout [data start value, scratch start value] := by
  have layout := ConstantPacking.field_layout _ (separated start value input seed) (capacity start value input seed fits)
  constructor
  · intro field member
    have owned : Owned (whole start value input seed) field := by
      simp at member
      rcases member with equal | equal
      · rw [equal]; exact data_owned start value input seed
      · rw [equal]; exact scratch_owned start value input seed
    exact layout.fits field ((ConstantPacking.fields_owned _ field).mpr owned)
  · intro first firstMember second secondMember different
    have included : ∀ field ∈ [data start value, scratch start value], field ∈ ConstantPacking.fields (whole start value input seed) := by
      intro field member
      simp at member
      rcases member with equal | equal
      · rw [equal]; exact (ConstantPacking.fields_owned _ _).mpr (data_owned start value input seed)
      · rw [equal]; exact (ConstantPacking.fields_owned _ _).mpr (scratch_owned start value input seed)
    exact layout.separate first (included first firstMember) second (included second secondMember) different

end SmcTuring.Appendix.ConstantGeometry
