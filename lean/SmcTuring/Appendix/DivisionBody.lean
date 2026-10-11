module
public import SmcTuring.Appendix.DivisionWords
public import SmcTuring.Appendix.DivisionWordAlgebra

public section
namespace SmcTuring.Appendix.DivisionBody
open Machine32 (Word State put)
open DivisionWords DivisionWordAlgebra

/-- A direct projection of every changed field in the literal 23-instruction
body. The two divisor immediates are kept independent in this raw effect. -/
@[expose] def value (fields : Fields) (state : State) : Slot → Word
  | .oldLow | .oldLow2 => state.memory (fields .low)
  | .low => (state.memory (fields .low) <<< 1) +
      (if underflow (state.memory (fields .low)) (state.memory (fields .high))
        (state.memory (fields .divisor2)) then 0 else 1)
  | .high => trial (state.memory (fields .low)) (state.memory (fields .high)) -
      state.memory (fields .divisor2) +
      (state.memory (fields .divisor) &&& BranchAlgebra.mask (underflow (state.memory (fields .low))
        (state.memory (fields .high)) (state.memory (fields .divisor2))))
  | .counter => state.memory (fields .counter) - 1
  | .restore => state.memory (fields .divisor) &&&
      BranchAlgebra.mask (underflow (state.memory (fields .low))
        (state.memory (fields .high)) (state.memory (fields .divisor2)))
  | .mask => BranchAlgebra.mask (underflow (state.memory (fields .low))
      (state.memory (fields .high)) (state.memory (fields .divisor2)))
  | .maskComplement => ~~~ BranchAlgebra.mask (underflow (state.memory (fields .low))
      (state.memory (fields .high)) (state.memory (fields .divisor2)))
  | .quotientBit => if underflow (state.memory (fields .low))
      (state.memory (fields .high)) (state.memory (fields .divisor2)) then 0 else 1
  | slot => state.memory (fields slot)

theorem body_field (fields : Fields) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (body fields) state).memory (fields slot) = value fields state slot := by
  cases slot <;> simp only [body, value, run, execute, selected,
    MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
    reduceCtorEq, ite_false, ite_true, BitVec.sub_add_cancel,
    doubling_borrow, BranchAlgebra.sbb_mask, quotient_bit,
    trial, incomingBit, underflow]
  all_goals rfl

theorem body_accumulator (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).accumulator = state.accumulator := by
  simp [body, run, execute, selected, MultiplyWords.execute, Machine32.execute,
    put, write, field_eq fields separate]

theorem body_carry (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).carry = false := by
  simp only [body, run, execute, selected, MultiplyWords.execute, Machine32.execute,
    put, write, field_eq fields separate, reduceCtorEq, ite_false, ite_true,
    BitVec.sub_add_cancel, doubling_borrow,
    BranchAlgebra.sbb_mask, quotient_bit, low_add_carry]

@[expose] def written : List Slot :=
  [.low, .oldLow, .oldLow2, .high, .counter, .restore, .mask, .maskComplement, .quotientBit]

theorem body_frame (fields : Fields) (state : State) (field : Nat)
    (outside : ∀ slot ∈ written, field ≠ fields slot) :
    (run (body fields) state).memory field = state.memory field := by
  apply run_frame
  simp_all [body, written, destination, selected, MultiplyWords.destination, Machine32.destination]

theorem body_pure (fields : Fields) (state : State) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ written, codeField (fields slot)) :
    PureRun codeField (body fields) state := by
  apply pure_of_destinations
  simp_all [body, written, destination, selected, MultiplyWords.destination, Machine32.destination]

theorem body_low (fields : Fields) (state : State) (separate : Separate fields)
    (divisorAgrees : state.memory (fields .divisor2) = state.memory (fields .divisor)) :
    (run (body fields) state).memory (fields .low) =
      nextLow (state.memory (fields .low)) (state.memory (fields .high))
        (state.memory (fields .divisor)) := by
  rw [body_field fields state separate .low]
  simp [value, nextLow, divisorAgrees]

theorem body_high (fields : Fields) (state : State) (separate : Separate fields)
    (divisorAgrees : state.memory (fields .divisor2) = state.memory (fields .divisor)) :
    (run (body fields) state).memory (fields .high) =
      nextHigh (state.memory (fields .low)) (state.memory (fields .high))
        (state.memory (fields .divisor)) := by
  rw [body_field fields state separate .high]
  simp only [value, divisorAgrees]
  rw [BitVec.and_comm, underflow, subtract_restore]
  simp only [nextHigh, underflow, decide_eq_true_eq]

theorem body_counter (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).memory (fields .counter) = state.memory (fields .counter) - 1 := by
  rw [body_field fields state separate .counter]
  rfl

theorem body_divisor (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).memory (fields .divisor) = state.memory (fields .divisor) ∧
    (run (body fields) state).memory (fields .divisor2) = state.memory (fields .divisor2) := by
  constructor
  · rw [body_field fields state separate .divisor]; rfl
  · rw [body_field fields state separate .divisor2]; rfl


/-- Actual high-word execution implements the restoring arithmetic step.
The trial-width bound is the mathematical prefix invariant's bound, not an
assumed future fetch or execution effect. -/
theorem restoring_remainder (fields : Fields) (state : State) (separate : Separate fields)
    (divisorAgrees : state.memory (fields .divisor2) = state.memory (fields .divisor))
    (fits : 2 * (state.memory (fields .high)).toNat +
      (if (state.memory (fields .low)).msb then 1 else 0 : Nat) < 4294967296)
    (prefixValue quotient : Nat) :
    ((run (body fields) state).memory (fields .high)).toNat =
      (DivisionAlgebra.step
        ⟨prefixValue, quotient, (state.memory (fields .high)).toNat⟩
        (if (state.memory (fields .low)).msb then 1 else 0)
        (state.memory (fields .divisor)).toNat).remainder := by
  rw [body_high fields state separate divisorAgrees,
    next_high_toNat _ _ _ fits]
  by_cases small : 2 * (state.memory (fields .high)).toNat +
      (if (state.memory (fields .low)).msb then 1 else 0 : Nat) <
        (state.memory (fields .divisor)).toNat
  all_goals simp [DivisionAlgebra.step, small]

end SmcTuring.Appendix.DivisionBody
