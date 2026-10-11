module
public import SmcTuring.Appendix.ConstantData

public section
namespace SmcTuring.Appendix.ConstantShape
open ConstantWords
open ConstantData (bytes span OwnOperand Linked)

@[expose] def Plain (ops : List Instruction) : Prop :=
  ∀ op ∈ ops, ∀ pc, OwnOperand op pc

theorem span_append (first second : List Instruction) : span (first ++ second) = span first + span second := by
  simp only [span, List.map_append, ConstantPacking.size_append]
theorem shift_span (field count : Nat) :
    span (shift field count) = if count = 0 then 0 else if count = 1 then 6 else 7 := by
  by_cases zero : count = 0
  · simp [shift, zero, span, ConstantPacking.size]
  · simp only [shift, zero, ite_false, ConstantData.span_cons]
    simp only [bytes, ConstantData.packet]
    split <;> rfl

theorem copy_span (data scratch : Nat) : span (copy data scratch) = 17 := rfl
theorem accumulate_span (data scratch : Nat) : span (accumulate data scratch) = 18 := rfl

theorem tail_span_independent (fuel data scratch otherData otherScratch : Nat) (value : Machine32.Word) :
    span (tail fuel data scratch value) = span (tail fuel otherData otherScratch value) := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    by_cases done : ConstantAlgebra.rest value = 0
    · simp only [tail, ite_eq_left done, span_append, shift_span]
      rfl
    · simp only [tail, ite_eq_right done, span_append, shift_span, accumulate_span, ih]

theorem program_span_independent (data scratch otherData otherScratch : Nat) (value : Machine32.Word) :
    span (program data scratch value) = span (program otherData otherScratch value) := by
  by_cases zero : value = 0
  · simp only [program, ite_eq_left zero]
    rfl
  · by_cases done : ConstantAlgebra.rest value = 0
    · simp only [program, ite_eq_right zero, ite_eq_left done, span_append, shift_span]
    · simp only [program, ite_eq_right zero, ite_eq_right done, span_append, shift_span, copy_span]
      rw [tail_span_independent 31 data scratch otherData otherScratch]

theorem plain_append (first second : List Instruction) (left : Plain first) (right : Plain second) :
    Plain (first ++ second) := by
  unfold Plain at left right ⊢
  intro op member pc
  rcases List.mem_append.mp member with member | member
  · exact left op member pc
  · exact right op member pc

theorem shift_plain (data count : Nat) : Plain (shift data count) := by
  unfold Plain
  intro op member pc
  by_cases zero : count = 0
  · simp [shift, zero] at member
  · simp only [shift, zero, ite_false, List.mem_singleton] at member
    subst op
    trivial

theorem copy_plain (data scratch : Nat) : Plain (copy data scratch) := by
  unfold Plain
  intro op member pc
  simp [copy] at member
  rcases member with rfl | rfl | rfl <;> trivial

theorem accumulate_plain (data scratch : Nat) : Plain (accumulate data scratch) := by
  unfold Plain
  intro op member pc
  simp [accumulate] at member
  rcases member with rfl | rfl | rfl <;> trivial

theorem plain_linked (ops : List Instruction) (plain : Plain ops) (start : Nat) : Linked start ops := by
  unfold Plain at plain
  induction ops generalizing start with
  | nil => trivial
  | cons op rest ih =>
    have tailPlain : Plain rest := by
      unfold Plain
      intro next member pc
      exact plain next (by simp [member]) pc
    exact ⟨plain op (by simp) start, ih tailPlain _⟩

theorem linked_append (first second : List Instruction) (start : Nat) :
    Linked start (first ++ second) ↔ Linked start first ∧ Linked (start + span first) second := by
  induction first generalizing start with
  | nil => simp [Linked, span, ConstantPacking.size]
  | cons op rest ih =>
    simp only [List.cons_append, Linked, ConstantData.span_cons, ih, Nat.add_assoc]
    exact and_assoc.symm

/-- The remaining bit pattern ends in the original ADD. Before it, there is
no immediate dependency requiring a location supplied by the caller. -/
theorem tail_shape (fuel data scratch : Nat) (value : Machine32.Word)
    (nonzero : value ≠ 0) (bound : value.toNat < 2 ^ fuel) :
    exists lead, tail fuel data scratch value = lead ++ [.addFrom data scratch] ∧ Plain lead := by
  induction fuel generalizing value with
  | zero =>
    have zero : value = 0 := by
      have small : value.toNat = 0 := by simpa using bound
      exact BitVec.eq_of_toNat_eq small
    exact False.elim (nonzero zero)
  | succ fuel ih =>
    rw [tail]
    by_cases done : ConstantAlgebra.rest value = 0
    · rw [ite_eq_left done]
      exact ⟨shift data (ConstantAlgebra.zeros value + 1), rfl, shift_plain _ _⟩
    · rw [ite_eq_right done]
      rcases ih (ConstantAlgebra.rest value) done (ConstantAlgebra.rest_bound value fuel bound) with ⟨lead, shape, plain⟩
      refine ⟨shift data (ConstantAlgebra.zeros value + 1) ++ accumulate data scratch ++ lead, ?_, ?_⟩
      · rw [shape, List.append_assoc, List.append_assoc]
      · exact plain_append _ _ (plain_append _ _ (shift_plain _ _) (accumulate_plain _ _)) plain

@[expose] def Active (value : Machine32.Word) : Prop := value ≠ 0 ∧ ConstantAlgebra.rest value ≠ 0

theorem program_shape (data scratch : Nat) (value : Machine32.Word) (active : Active value) :
    exists lead, program data scratch value = lead ++ [.addFrom data scratch] ∧ Plain lead := by
  have bound : (ConstantAlgebra.rest value).toNat < 2 ^ 31 :=
    ConstantAlgebra.rest_bound value 31 value.isLt
  rcases tail_shape 31 data scratch _ active.2 bound with ⟨lead, shape, plain⟩
  refine ⟨shift data (ConstantAlgebra.zeros value) ++ copy data scratch ++ lead, ?_, ?_⟩
  · simp only [program, ite_eq_right active.1, ite_eq_right active.2, shape, List.append_assoc]
  · exact plain_append _ _ (plain_append _ _ (shift_plain _ _) (copy_plain _ _)) plain

theorem inactive_plain (data scratch : Nat) (value : Machine32.Word) (inactive : ¬Active value) :
    Plain (program data scratch value) := by
  by_cases zero : value = 0
  · simp only [program, ite_eq_left zero]
    unfold Plain
    intro op member pc
    simp only [List.mem_singleton] at member
    subst op
    trivial
  · have done : ConstantAlgebra.rest value = 0 := by
      by_contra notDone
      exact inactive ⟨zero, notDone⟩
    simpa only [program, ite_eq_right zero, ite_eq_left done, List.append_nil] using shift_plain data (ConstantAlgebra.zeros value)

theorem active_span (data scratch : Nat) (value : Machine32.Word) (active : Active value) :
    10 ≤ span (program data scratch value) := by
  rcases program_shape data scratch value active with ⟨lead, shape, _⟩
  rw [shape, span_append]
  change 10 ≤ span lead + 10
  omega

theorem active_linked (data scratch start : Nat) (value : Machine32.Word) (active : Active value)
    (operand : scratch + 4 = start + span (program data scratch value)) :
    Linked start (program data scratch value) := by
  rcases program_shape data scratch value active with ⟨lead, shape, plain⟩
  rw [shape, span_append] at operand
  have lastBytes : span [.addFrom data scratch] = 10 := rfl
  rw [lastBytes] at operand
  rw [shape, linked_append]
  refine ⟨plain_linked lead plain start, ?_⟩
  change scratch = start + span lead + 6 ∧ True
  exact ⟨by omega, trivial⟩

theorem active_owned (data scratch start : Nat) (value : Machine32.Word) (active : Active value)
    (operand : scratch + 4 = start + span (program data scratch value)) :
    ConstantImage.Owned (ConstantData.entries start (program data scratch value)) scratch := by
  rcases program_shape data scratch value active with ⟨lead, shape, _⟩
  rw [shape, span_append] at operand
  have lastBytes : span [.addFrom data scratch] = 10 := rfl
  rw [lastBytes] at operand
  have own : scratch = start + span lead + 6 := by omega
  rw [shape]
  unfold ConstantData.entries
  rw [List.map_append, ConstantPacking.place_append]
  refine ⟨⟨start + span lead, ConstantData.packet (.addFrom data scratch)⟩, ?_, ?_⟩
  · apply List.mem_append_right
    apply List.mem_cons.mpr
    exact Or.inl rfl
  · change scratch ∈ [start + span lead + 6]
    exact List.mem_singleton.mpr own

end SmcTuring.Appendix.ConstantShape
