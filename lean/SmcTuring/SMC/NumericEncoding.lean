module
public import SmcTuring.SMC.Primitives
public import SmcTuring.Dolan.FourRegisters

public section

namespace SmcTuring.SMC

open Dolan

structure Layout where
  base : Int
  stride : Int
  reserved : Nat
  base_nonnegative : 0 ≤ base
  stride_positive : 0 < stride
  enough_reserved : 4 ≤ reserved

@[expose] def fieldAddress (layout : Layout) (index : Nat) : Int :=
  layout.base + layout.stride * (index : Int)

@[expose] def heapBase (layout : Layout) : Int := fieldAddress layout layout.reserved

@[expose] def registerIndex : Four.Register → Nat
  | .ring => 0
  | .a => 1
  | .b => 2
  | .c => 3

@[expose] def registerField (layout : Layout) (r : Four.Register) : Int :=
  fieldAddress layout (registerIndex r)

@[expose] def heapField (layout : Layout) (p : Nat × Bool) : Int :=
  fieldAddress layout (layout.reserved + 2 * p.1 + (if p.2 then 1 else 0))

@[expose] def codeField (layout : Layout) (p : Int) : Prop := ∃ index : Nat, p = fieldAddress layout index

@[expose] def encodeWord (layout : Layout) : Mov.Word → Int
  | .address cell => heapField layout (cell, false)
  | .offset choice => if choice then layout.stride else 0

theorem register_is_code (layout : Layout) (r : Four.Register) : codeField layout (registerField layout r) :=
  ⟨registerIndex r, rfl⟩

theorem heap_is_code (layout : Layout) (p : Nat × Bool) : codeField layout (heapField layout p) :=
  ⟨layout.reserved + 2 * p.1 + (if p.2 then 1 else 0), rfl⟩

theorem data_field_separate (layout : Layout) (field address : Int)
    (outside : ¬ codeField layout field) (data : codeField layout address) : address ≠ field := by
  intro equal
  exact outside (equal ▸ data)

theorem field_address_injective (layout : Layout) : Function.Injective (fieldAddress layout) := by
  intro a b equal
  have product : layout.stride * (a : Int) = layout.stride * (b : Int) := by
    simp only [fieldAddress] at equal
    omega
  have ints := Int.eq_of_mul_eq_mul_left (by have := layout.stride_positive; omega) product
  omega

theorem heap_field_injective (layout : Layout) : Function.Injective (heapField layout) := by
  intro a b equal
  have indices := field_address_injective layout equal
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  cases x <;> cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] at indices ⊢ <;>
    apply Prod.ext <;> simp_all <;> omega

theorem register_field_injective (layout : Layout) : Function.Injective (registerField layout) := by
  intro first second equal
  have indices := field_address_injective layout equal
  cases first <;> cases second <;> simp_all [registerField, registerIndex]

theorem indexed_address_correct (layout : Layout) (cell : Nat) (choice : Bool) :
    encodeWord layout (.address cell) + encodeWord layout (.offset choice) = heapField layout (cell, choice) := by
  cases choice <;>
    simp [encodeWord, heapField, fieldAddress, Int.mul_add, Int.add_assoc]

theorem heap_field_after_base (layout : Layout) (p : Nat × Bool) : heapBase layout ≤ heapField layout p := by
  have increase : 0 ≤ layout.stride * (2 * (p.1 : Int) + ((if p.2 then 1 else 0 : Nat) : Int)) := by
    apply Int.mul_nonneg (by have := layout.stride_positive; omega)
    cases p.2 <;> simp <;> omega
  simpa [heapBase, heapField, fieldAddress, Int.mul_add, Int.add_assoc] using
    Int.le_add_of_nonneg_right increase (a := heapBase layout)

theorem flags_below_heap (layout : Layout) (a b : Bool) :
    encodeWord layout (.offset a) + encodeWord layout (.offset b) < heapBase layout := by
  have reserved : (4 : Int) ≤ (layout.reserved : Int) := by have := layout.enough_reserved; omega
  have positive := layout.stride_positive
  have nonnegative := layout.base_nonnegative
  have product := Int.mul_le_mul_of_nonneg_left reserved (Int.le_of_lt layout.stride_positive)
  cases a <;> cases b <;>
    simp only [encodeWord, Bool.false_eq_true, ↓reduceIte, heapBase, fieldAddress] <;> omega

theorem flag_below_heap (layout : Layout) (choice : Bool) : encodeWord layout (.offset choice) < heapBase layout := by
  simpa only [encodeWord, Bool.false_eq_true, ↓reduceIte, Int.add_zero] using
    flags_below_heap layout choice false

theorem encode_word_below_heap_iff (layout : Layout) (word : Mov.Word) :
    encodeWord layout word < heapBase layout ↔ ∃ choice, word = .offset choice := by
  cases word with
  | address cell =>
    have high : ¬ encodeWord layout (.address cell) < heapBase layout := by
      change ¬ heapField layout (cell, false) < heapBase layout
      have := heap_field_after_base layout (cell, false)
      omega
    simp [high]
  | offset choice =>
    exact ⟨fun _ => ⟨choice, rfl⟩, fun _ => flag_below_heap layout choice⟩

theorem encode_word_after_heap_iff (layout : Layout) (word : Mov.Word) :
    heapBase layout ≤ encodeWord layout word ↔ ∃ cell, word = .address cell := by
  cases word with
  | address cell => exact ⟨fun _ => ⟨cell, rfl⟩, fun _ => heap_field_after_base layout (cell, false)⟩
  | offset choice =>
    have low := flag_below_heap layout choice
    have high : ¬ heapBase layout ≤ encodeWord layout (.offset choice) := by omega
    simp [high]

theorem mov_address_none_iff (layout : Layout) (source : Mov.State) (base offset : Mov.Register) :
    Mov.address source base offset = none ↔
      encodeWord layout (source.registers base) < heapBase layout ∨
      heapBase layout ≤ encodeWord layout (source.registers offset) := by
  rw [encode_word_below_heap_iff, encode_word_after_heap_iff]
  cases baseValue : source.registers base <;> cases offsetValue : source.registers offset <;>
    simp [Mov.address, baseValue, offsetValue]

theorem encode_word_injective (layout : Layout) : Function.Injective (encodeWord layout) := by
  intro first second equal
  cases first with
  | address cell =>
    cases second with
    | address other =>
      have pair : (cell, false) = (other, false) := heap_field_injective layout equal
      have cells := congrArg Prod.fst pair
      exact congrArg Mov.Word.address cells
    | offset choice =>
      have high := heap_field_after_base layout (cell, false)
      have low := flag_below_heap layout choice
      change heapField layout (cell, false) = encodeWord layout (.offset choice) at equal
      omega
  | offset choice =>
    cases second with
    | address cell =>
      have high := heap_field_after_base layout (cell, false)
      have low := flag_below_heap layout choice
      change encodeWord layout (.offset choice) = heapField layout (cell, false) at equal
      omega
    | offset other =>
      have positive := layout.stride_positive
      cases choice <;> cases other <;> simp_all [encodeWord]

theorem register_heap_separate (layout : Layout) (r : Four.Register) (p : Nat × Bool) :
    registerField layout r ≠ heapField layout p := by
  intro equal
  have indices := field_address_injective layout equal
  have reserved := layout.enough_reserved
  cases r <;> cases p.2 <;> simp [registerIndex] at indices <;> omega

@[expose] def NumericRep (layout : Layout) (source : Four.State) (target : State) : Prop :=
  (∀ r, target.memory (registerField layout r) = encodeWord layout (source.registers r)) ∧
  (∀ p, target.memory (heapField layout p) = encodeWord layout (source.memory p))

/-- A write into a metadata field, disjoint from every source register and
heap field, preserves the represented source state. -/
theorem metadata_write_frame (layout : Layout) (source : Four.State) (target : State) (field value : Int)
    (rep : NumericRep layout source target)
    (registers : ∀ r, registerField layout r ≠ field) (heap : ∀ p, heapField layout p ≠ field) :
    NumericRep layout source { target with memory := write target.memory field value } := by
  constructor
  · intro r
    simpa [write, registers r] using rep.1 r
  · intro p
    simpa [write, heap p] using rep.2 p

theorem register_write_rep (layout : Layout) (source : Four.State) (target : State) (r : Four.Register)
    (word : Mov.Word) (rep : NumericRep layout source target) :
    NumericRep layout { source with registers := write source.registers r word }
      { target with memory := write target.memory (registerField layout r) (encodeWord layout word) } := by
  constructor
  · intro q
    by_cases same : q = r
    · subst q
      simp [write]
    · have separate : registerField layout q ≠ registerField layout r := fun equal =>
        same (register_field_injective layout equal)
      simpa [write, same, separate] using rep.1 q
  · intro p
    simpa [write, Ne.symm (register_heap_separate layout r p)] using rep.2 p

theorem heap_write_rep (layout : Layout) (source : Four.State) (target : State) (p : Nat × Bool)
    (word : Mov.Word) (rep : NumericRep layout source target) :
    NumericRep layout { source with memory := write source.memory p word }
      { target with memory := write target.memory (heapField layout p) (encodeWord layout word) } := by
  constructor
  · intro r
    simpa [write, register_heap_separate layout r p] using rep.1 r
  · intro q
    by_cases same : q = p
    · subst q
      simp [write]
    · have separate : heapField layout q ≠ heapField layout p := fun equal => same (heap_field_injective layout equal)
      simpa [write, same, separate] using rep.2 q

end SmcTuring.SMC
