module
public import SmcTuring.SMC.NumericEncoding

public section

namespace SmcTuring.SMC.Virtual

open Dolan

/-- The checked 64-MOV logical kernel can be lowered directly. Its thirteen
registers become code words, so they are not thirteen hardware registers.
The separate checked four-register Dolan compiler remains available. -/
structure Layout where
  data : SMC.Layout
  enoughRegisters : 13 ≤ data.reserved

@[expose] def registerField (layout : Layout) (r : Mov.Register) : Int :=
  fieldAddress layout.data (Four.slot r).val

theorem register_is_code (layout : Layout) (r : Mov.Register) : codeField layout.data (registerField layout r) :=
  ⟨(Four.slot r).val, rfl⟩

theorem register_field_injective (layout : Layout) : Function.Injective (registerField layout) := by
  intro first second equal
  have indices := field_address_injective layout.data equal
  exact Four.slot_injective (Fin.ext indices)

theorem register_heap_separate (layout : Layout) (r : Mov.Register) (p : Nat × Bool) :
    registerField layout r ≠ heapField layout.data p := by
  intro equal
  have indices := field_address_injective layout.data equal
  have reserved := layout.enoughRegisters
  have bounded := (Four.slot r).isLt
  cases p.2 <;> omega

@[expose] def Rep (layout : Layout) (source : Mov.State) (target : State) : Prop :=
  (∀ r, target.memory (registerField layout r) = encodeWord layout.data (source.registers r)) ∧
  (∀ p, target.memory (heapField layout.data p) = encodeWord layout.data (source.memory p))

theorem metadata_write_frame (layout : Layout) (source : Mov.State) (target : State) (field value : Int)
    (rep : Rep layout source target)
    (registers : ∀ r, registerField layout r ≠ field) (heap : ∀ p, heapField layout.data p ≠ field) :
    Rep layout source { target with memory := write target.memory field value } := by
  constructor
  · intro r
    simpa [write, registers r] using rep.1 r
  · intro p
    simpa [write, heap p] using rep.2 p

theorem register_write_rep (layout : Layout) (source : Mov.State) (target : State) (r : Mov.Register)
    (word : Mov.Word) (rep : Rep layout source target) :
    Rep layout { source with registers := write source.registers r word }
      { target with memory := write target.memory (registerField layout r) (encodeWord layout.data word) } := by
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

theorem heap_write_rep (layout : Layout) (source : Mov.State) (target : State) (p : Nat × Bool)
    (word : Mov.Word) (rep : Rep layout source target) :
    Rep layout { source with memory := write source.memory p word }
      { target with memory := write target.memory (heapField layout.data p) (encodeWord layout.data word) } := by
  constructor
  · intro r
    simpa [write, register_heap_separate layout r p] using rep.1 r
  · intro q
    by_cases same : q = p
    · subst q
      simp [write]
    · have separate : heapField layout.data q ≠ heapField layout.data p := fun equal =>
        same (heap_field_injective layout.data equal)
      simpa [write, same, separate] using rep.2 q

end SmcTuring.SMC.Virtual
