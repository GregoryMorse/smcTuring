module
public import SmcTuring.Appendix.DivisionDataCorrect

public section
namespace SmcTuring.Appendix.DivisionGuard
open Machine32 (Word State)
open DivisionWords

/-- The four guard slots are the printed counter/delta/mask/CALL operand.
Unused multiplication roles only give an injective existing guard interface. -/
@[expose] def binding : MultiplyWords.Slot → Slot
  | .x => .x | .y => .y | .result => .result | .factor => .low
  | .multiplier => .counter | .total => .high | .delta => .delta
  | .mask => .guardMask | .displacement => .displacement
  | .bit => .quotientBit | .addMask => .mask | .addend => .restore

@[expose] def guardFields (fields : Fields) : MultiplyWords.Fields := fun slot => fields (binding slot)

theorem binding_injective : Function.Injective binding := by
  intro first second same
  cases first <;> cases second <;> simp_all [binding]

theorem guard_separate (fields : Fields) (separate : Separate fields) :
    MultiplyWords.Separate (guardFields fields) := separate.comp binding_injective

@[expose] def program (fields : Fields) (delta : Word) : List Instruction :=
  (MultiplyWords.guard (guardFields fields) delta).map Instruction.simple

@[expose] def written : List Slot := [.counter, .delta, .guardMask, .displacement]

theorem frame (fields : Fields) (delta : Word) (state : State) (field : Nat)
    (outside : ∀ slot ∈ written, field ≠ fields slot) :
    (run (program fields delta) state).memory field = state.memory field := by
  apply run_frame
  simp_all [program, written, MultiplyWords.guard, guardFields, binding,
    destination, MultiplyWords.destination, Machine32.destination]

@[expose] def value (fields : Fields) (delta : Word) (state : State) : Slot → Word
  | .delta => delta
  | .guardMask => if state.memory (fields .counter) = 0 then delta else 0
  | .displacement => state.memory (fields .displacement) ^^^
      (if state.memory (fields .counter) = 0 then delta else 0)
  | slot => state.memory (fields slot)

theorem field (fields : Fields) (delta : Word) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (program fields delta) state).memory (fields slot) = value fields delta state slot := by
  have counter := MultiplyWords.guard_field (guardFields fields) delta state
    (guard_separate fields separate) .multiplier
  have deltaField := MultiplyWords.guard_field (guardFields fields) delta state
    (guard_separate fields separate) .delta
  have maskField := MultiplyWords.guard_field (guardFields fields) delta state
    (guard_separate fields separate) .mask
  have callField := MultiplyWords.guard_field (guardFields fields) delta state
    (guard_separate fields separate) .displacement
  simp only [guardFields, binding, MultiplyWords.guardValue] at counter deltaField maskField callField
  cases slot with
  | counter => rw [program, embedded_run]; exact counter
  | delta => rw [program, embedded_run]; exact deltaField
  | guardMask => rw [program, embedded_run]; exact maskField
  | displacement => rw [program, embedded_run]; exact callField
  | _ => apply frame; simp [written, field_eq fields separate]

theorem accumulator (fields : Fields) (delta : Word) (state : State) :
    (run (program fields delta) state).accumulator = state.accumulator := by
  rw [program, embedded_run]
  exact MultiplyWords.guard_accumulator _ _ _

theorem carry (fields : Fields) (delta : Word) (state : State) :
    (run (program fields delta) state).carry = false := by
  rw [program, embedded_run]
  exact MultiplyWords.guard_carry _ _ _

theorem displacement (fields : Fields) (delta : Word) (state : State)
    (separate : Separate fields) (initial : state.memory (fields .displacement) = 0) :
    (run (program fields delta) state).memory (fields .displacement) =
      if state.memory (fields .counter) = 0 then delta else 0 := by
  rw [field fields delta state separate .displacement]
  simp [value, initial]

theorem pure (fields : Fields) (delta : Word) (state : State) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ written, codeField (fields slot)) :
    PureRun codeField (program fields delta) state := by
  apply pure_of_destinations
  simp_all [program, written, MultiplyWords.guard, guardFields, binding,
    destination, MultiplyWords.destination, Machine32.destination]

theorem invariant (fields : Fields) (delta dividend divisor : Word) (state : State) (k : Nat)
    (separate : Separate fields)
    (current : DivisionIteration.Invariant fields dividend divisor k state) :
    DivisionIteration.Invariant fields dividend divisor k (run (program fields delta) state) := by
  rcases current with ⟨first, second, low, high, counter⟩
  simp only [DivisionIteration.Invariant, field fields delta state separate, value]
  exact ⟨first, second, low, high, counter⟩

theorem length (fields : Fields) (delta : Word) : (program fields delta).length = 8 := rfl

end SmcTuring.Appendix.DivisionGuard
