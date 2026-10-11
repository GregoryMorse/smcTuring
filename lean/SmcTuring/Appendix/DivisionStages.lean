module
public import SmcTuring.Appendix.DivisionPrefixes
public import SmcTuring.Appendix.DivisionBody

public section
namespace SmcTuring.Appendix.DivisionStages
open Machine32 (Word State put)
open DivisionWords DivisionPrefixes DivisionSignedAlgebra

@[expose] def initialValue (fields : Fields) (mod signed : Bool) (state : State) : Slot → Word
  | .low => if signed then magnitude (state.memory (fields .x)) else state.memory (fields .x)
  | .divisor | .divisor2 => if signed then magnitude (state.memory (fields .y)) else state.memory (fields .y)
  | .high => 0
  | .counter => 32
  | .signX => if signed then signValue fields mod state .signX else state.memory (fields .signX)
  | .signY => if signed then signValue fields mod state .signY else state.memory (fields .signY)
  | .resultSign => if signed then signValue fields mod state .resultSign else state.memory (fields .resultSign)
  | .xMask => if signed then BranchAlgebra.mask (state.memory (fields .x)).msb else state.memory (fields .xMask)
  | .yMask => if signed then BranchAlgebra.mask (state.memory (fields .y)).msb else state.memory (fields .yMask)
  | .xDouble => if signed then (state.memory (fields .x) <<< 1) &&& BranchAlgebra.mask (state.memory (fields .x)).msb
      else state.memory (fields .xDouble)
  | .yDouble => if signed then (state.memory (fields .y) <<< 1) &&& BranchAlgebra.mask (state.memory (fields .y)).msb
      else state.memory (fields .yDouble)
  | slot => state.memory (fields slot)

theorem signed_initial_shape (fields : Fields) (mod : Bool) :
    initializeData fields mod true =
      ((signPrefix fields mod ++ normalizeProgram fields false ++
        normalizeProgram fields true ++ copy fields .divisor2 .divisor) ++
        [selected (.store (fields .high) 0), selected (.store (fields .counter) 32),
         .simple (.selfStore (fields .counter))]) := by
  cases mod <;> rfl

theorem initial_field (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (initializeData fields mod signed) state).memory (fields slot) =
      initialValue fields mod signed state slot := by
  cases signed with
  | false =>
      cases mod <;> cases slot <;> simp [initializeData, initialValue, copy,
        MultiplyWords.copyProgram, run, execute, selected, MultiplyWords.execute,
        Machine32.execute, put, write, field_eq fields separate]
  | true =>
      have normal (divisor : Bool) (current : State) (observed : Slot) :=
        normalize_field fields divisor current separate observed
      have signs (current : State) (observed : Slot) :=
        sign_field fields mod current separate observed
      have copied (current : State) := copy_effect fields .divisor .divisor2 current separate (by decide)
      rw [signed_initial_shape]
      cases slot <;>
        simp [run_append, copied, normal, signs, initialValue, normalizeValue, signValue,
          run, execute, selected, MultiplyWords.execute, Machine32.execute,
          put, write, field_eq fields separate]

theorem initial_accumulator (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (initializeData fields mod signed) state).accumulator = state.accumulator := by
  cases signed with
  | false =>
      cases mod <;> simp [initializeData, copy, MultiplyWords.copyProgram,
        run, execute, selected, MultiplyWords.execute, Machine32.execute,
        put, write, field_eq fields separate]
  | true =>
      have normal (divisor : Bool) (current : State) := normalize_accumulator fields divisor current separate
      have signs (current : State) := sign_accumulator fields mod current separate
      have copied (current : State) := copy_effect fields .divisor .divisor2 current separate (by decide)
      rw [signed_initial_shape]
      simp [run_append, normal, signs, copied, run, execute, selected,
        MultiplyWords.execute, Machine32.execute, put]

theorem initial_carry (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (initializeData fields mod signed) state).carry =
      if signed then false else state.carry := by
  cases signed with
  | false =>
      cases mod <;> simp [initializeData, copy, MultiplyWords.copyProgram,
        run, execute, selected, MultiplyWords.execute, Machine32.execute, put]
  | true =>
      have normal (divisor : Bool) (current : State) := normalize_carry fields divisor current separate
      have copied (current : State) := copy_effect fields .divisor .divisor2 current separate (by decide)
      rw [signed_initial_shape]
      simp [run_append, normal, copied, run, execute, selected,
        MultiplyWords.execute, Machine32.execute, put]

theorem initial_length (fields : Fields) (mod signed : Bool) :
    (initializeData fields mod signed).length = if signed then (if mod then 37 else 42) else 10 := by
  cases signed <;> cases mod <;> rfl

/-- The result-selecting MOV/SELF pair reads the same low/high fields as the
published branch; the optional six-instruction signed suffix is literal. -/
@[expose] def selectedResult (fields : Fields) (mod : Bool) (state : State) : Word :=
  state.memory (fields (if mod then .high else .low))

@[expose] def finishValue (fields : Fields) (mod signed : Bool) (state : State) : Slot → Word
  | .displacement => 0
  | .result => if signed then selectedResult fields mod state -
      ((selectedResult fields mod state <<< 1) &&& state.memory (fields .resultSign))
      else selectedResult fields mod state
  | .outputDouble => if signed then (selectedResult fields mod state <<< 1) &&&
      state.memory (fields .resultSign) else state.memory (fields .outputDouble)
  | slot => state.memory (fields slot)

theorem finish_field (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (finishData fields mod signed) state).memory (fields slot) =
      finishValue fields mod signed state slot := by
  cases mod <;> cases signed <;> cases slot <;>
    simp [finishData, finishValue, selectedResult, run, execute, selected,
      MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate]

theorem finish_accumulator (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (finishData fields mod signed) state).accumulator = state.accumulator := by
  cases mod <;> cases signed <;>
    simp [finishData, run, execute, selected, MultiplyWords.execute,
      Machine32.execute, put, write, field_eq fields separate]

theorem finish_carry (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (finishData fields mod signed) state).carry =
      if signed then decide ((selectedResult fields mod state).toNat <
        ((selectedResult fields mod state <<< 1) &&& state.memory (fields .resultSign)).toNat)
      else state.carry := by
  cases mod <;> cases signed <;>
    simp only [finishData, selectedResult, run, execute, selected,
      MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
      Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, List.cons_append, List.nil_append]

theorem finish_signed_result (fields : Fields) (mod : Bool) (state : State)
    (separate : Separate fields) (sign : Bool)
    (signMask : state.memory (fields .resultSign) = BranchAlgebra.mask sign) :
    (run (finishData fields mod true) state).memory (fields .result) =
      if sign then -selectedResult fields mod state else selectedResult fields mod state := by
  rw [finish_field fields mod true state separate .result]
  simp only [finishValue, ite_true, signMask]
  rw [BitVec.and_comm]
  exact apply_sign sign (selectedResult fields mod state)

theorem finish_length (fields : Fields) (mod signed : Bool) :
    (finishData fields mod signed).length = if signed then 9 else 3 := by
  cases mod <;> cases signed <;> rfl


@[expose] def initialWritten (mod signed : Bool) : List Slot :=
  [.x, .y, .low, .divisor, .divisor2, .high, .counter] ++
  (if signed then [.signX, .resultSign, .xMask, .xDouble, .yMask, .yDouble] ++
    (if mod then [] else [.signY]) else [])

theorem initial_frame (fields : Fields) (mod signed : Bool) (state : State) (field : Nat)
    (outside : ∀ slot ∈ initialWritten mod signed, field ≠ fields slot) :
    (run (initializeData fields mod signed) state).memory field = state.memory field := by
  apply run_frame
  cases mod <;> cases signed <;>
    simp_all [initializeData, signPrefix, DivisionWords.sample, normalize, copy,
      MultiplyWords.copyProgram, initialWritten, destination, selected,
      MultiplyWords.destination, Machine32.destination]

theorem initial_pure (fields : Fields) (mod signed : Bool) (state : State) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ initialWritten mod signed, codeField (fields slot)) :
    PureRun codeField (initializeData fields mod signed) state := by
  apply pure_of_destinations
  cases mod <;> cases signed <;>
    simp_all [initializeData, signPrefix, DivisionWords.sample, normalize, copy,
      MultiplyWords.copyProgram, initialWritten, destination, selected,
      MultiplyWords.destination, Machine32.destination]

theorem initial_inputs (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    let current := run (initializeData fields mod signed) state
    current.memory (fields .x) = state.memory (fields .x) ∧
    current.memory (fields .y) = state.memory (fields .y) ∧
    current.memory (fields .high) = 0 ∧
    current.memory (fields .counter) = 32 ∧
    current.memory (fields .divisor2) = current.memory (fields .divisor) := by
  simp [initial_field fields mod signed state separate, initialValue]

@[expose] def finishWritten (mod signed : Bool) : List Slot :=
  [.displacement, .result, if mod then .low else .high] ++
    (if signed then [.outputDouble] else [])

theorem finish_frame (fields : Fields) (mod signed : Bool) (state : State) (field : Nat)
    (outside : ∀ slot ∈ finishWritten mod signed, field ≠ fields slot) :
    (run (finishData fields mod signed) state).memory field = state.memory field := by
  apply run_frame
  cases mod <;> cases signed <;>
    simp_all [finishData, finishWritten, destination, selected,
      MultiplyWords.destination, Machine32.destination]

theorem finish_pure (fields : Fields) (mod signed : Bool) (state : State) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ finishWritten mod signed, codeField (fields slot)) :
    PureRun codeField (finishData fields mod signed) state := by
  apply pure_of_destinations
  cases mod <;> cases signed <;>
    simp_all [finishData, finishWritten, destination, selected,
      MultiplyWords.destination, Machine32.destination]

theorem finish_signed_carry (fields : Fields) (mod : Bool) (state : State)
    (separate : Separate fields) (sign : Bool)
    (signMask : state.memory (fields .resultSign) = BranchAlgebra.mask sign) :
    (run (finishData fields mod true) state).carry =
      (sign && decide (0 < (selectedResult fields mod state).toNat ∧
        (selectedResult fields mod state).toNat < 2147483648)) := by
  rw [finish_carry fields mod true state separate]
  simp only [ite_true, signMask]
  exact DivisionWordAlgebra.signed_result_carry sign _

end SmcTuring.Appendix.DivisionStages

