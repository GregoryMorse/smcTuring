module
public import SmcTuring.Appendix.DivisionIteration

public section
namespace SmcTuring.Appendix.DivisionDataCorrect
open Machine32 (Word State)
open DivisionWords DivisionStages DivisionIteration
open DivisionSignedAlgebra

@[expose] def argument (signed : Bool) (word : Word) : Word :=
  if signed then magnitude word else word

@[expose] def program (fields : Fields) (mod signed : Bool) : List Instruction :=
  initializeData fields mod signed ++ repeatedBody fields 32 ++ finishData fields mod signed

@[expose] def loopState (fields : Fields) (mod signed : Bool) (state : State) : State :=
  iterate fields 32 (run (initializeData fields mod signed) state)

theorem initialized (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    Ready fields (argument signed (state.memory (fields .x)))
      (argument signed (state.memory (fields .y)))
      (run (initializeData fields mod signed) state) := by
  simp [Ready, initial_field fields mod signed state separate, initialValue, argument]

theorem divisor_nonzero (signed : Bool) (word : Word) (nonzero : word ≠ 0) :
    argument signed word ≠ 0 := by
  cases signed with
  | false => exact nonzero
  | true =>
      have positive := magnitude_nonzero word nonzero
      intro zero
      simp [argument] at zero
      rw [zero] at positive
      simp at positive

theorem loop_result (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (nonzero : state.memory (fields .y) ≠ 0) :
    selectedResult fields mod (loopState fields mod signed state) =
      BitVec.ofNat 32
        (if mod then (argument signed (state.memory (fields .x))).toNat %
          (argument signed (state.memory (fields .y))).toNat
        else (argument signed (state.memory (fields .x))).toNat /
          (argument signed (state.memory (fields .y))).toNat) := by
  have denominator := divisor_nonzero signed (state.memory (fields .y)) nonzero
  have facts := correct fields _ _ _ separate denominator (initialized fields mod signed state separate)
  apply BitVec.eq_of_toNat_eq
  cases mod with
  | false =>
      change ((loopState fields false signed state).memory (fields .low)).toNat = _
      simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (DivisionAlgebra.quotient_fits
        (argument signed (state.memory (fields .x))) (argument signed (state.memory (fields .y))))]
      exact facts.1
  | true =>
      change ((loopState fields true signed state).memory (fields .high)).toNat = _
      have bound : (argument signed (state.memory (fields .x))).toNat %
          (argument signed (state.memory (fields .y))).toNat < 4294967296 := by
        have := Nat.mod_le (argument signed (state.memory (fields .x))).toNat
          (argument signed (state.memory (fields .y))).toNat
        have fits : (argument signed (state.memory (fields .x))).toNat < 4294967296 :=
          (argument signed (state.memory (fields .x))).isLt
        omega
      simp only [ite_true, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt bound]
      exact facts.2.1

theorem loop_sign (fields : Fields) (mod : Bool) (state : State) (separate : Separate fields) :
    (loopState fields mod true state).memory (fields .resultSign) =
      BranchAlgebra.mask (negative mod (state.memory (fields .x)) (state.memory (fields .y))) := by
  rw [loopState, frame fields _ 32 (fields .resultSign)]
  · rw [initial_field fields mod true state separate .resultSign]
    rfl
  · intro slot member
    have different : Slot.resultSign ≠ slot := by
      cases slot <;> simp_all [DivisionBody.written]
    exact separate.ne different

theorem program_execution (fields : Fields) (mod signed : Bool) (state : State) :
    run (program fields mod signed) state =
      run (finishData fields mod signed) (loopState fields mod signed state) := by
  rw [program, run_append, run_append, repeated_execution]
  rfl

theorem result_pattern (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (nonzero : state.memory (fields .y) ≠ 0) :
    (run (program fields mod signed) state).memory (fields .result) =
      if signed then result mod (state.memory (fields .x)) (state.memory (fields .y))
      else if mod then (state.memory (fields .x)) % (state.memory (fields .y))
        else (state.memory (fields .x)) / (state.memory (fields .y)) := by
  rw [program_execution, finish_field fields mod signed _ separate .result]
  cases signed with
  | false =>
      simp only [finishValue, Bool.false_eq_true, ite_false,
        loop_result fields mod false state separate nonzero, argument]
      cases mod
      · apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_udiv, DivisionAlgebra.quotient_fits, Nat.mod_eq_of_lt]
      · apply BitVec.eq_of_toNat_eq
        change ((state.memory (fields .x)).toNat % (state.memory (fields .y)).toNat) %
          4294967296 = (state.memory (fields .x)).toNat % (state.memory (fields .y)).toNat
        have small := (state.memory (fields .x)).isLt
        have bound := Nat.mod_le (state.memory (fields .x)).toNat (state.memory (fields .y)).toNat
        exact Nat.mod_eq_of_lt (by omega)
  | true =>
      simp only [finishValue, ite_true, loop_sign fields mod state separate,
        loop_result fields mod true state separate nonzero, argument, magnitudeResult, result, applySign]
      rw [BitVec.and_comm]

theorem signed_quotient (fields : Fields) (state : State) (separate : Separate fields)
    (nonzero : state.memory (fields .y) ≠ 0)
    (noOverflow : ¬(state.memory (fields .x) = (2147483648 : Word) ∧
      state.memory (fields .y) = (-1 : Word))) :
    ((run (program fields false true) state).memory (fields .result)).toInt =
      (state.memory (fields .x)).toInt.tdiv (state.memory (fields .y)).toInt := by
  rw [result_pattern fields false true state separate nonzero]
  exact quotient_toInt _ _ nonzero noOverflow

theorem signed_remainder (fields : Fields) (state : State) (separate : Separate fields)
    (nonzero : state.memory (fields .y) ≠ 0) :
    ((run (program fields true true) state).memory (fields .result)).toInt =
      (state.memory (fields .x)).toInt.tmod (state.memory (fields .y)).toInt := by
  rw [result_pattern fields true true state separate nonzero]
  exact remainder_toInt _ _ nonzero

theorem program_accumulator (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (program fields mod signed) state).accumulator = state.accumulator := by
  rw [program_execution, finish_accumulator fields mod signed _ separate,
    loopState, accumulator fields _ 32 separate, initial_accumulator fields mod signed state separate]

theorem pure_append (codeField : Nat → Prop) (first second : List Instruction) (state : State) :
    PureRun codeField (first ++ second) state ↔
      PureRun codeField first state ∧ PureRun codeField second (run first state) := by
  induction first generalizing state with
  | nil => simp [PureRun, run]
  | cons instruction rest ih => simp [PureRun, run, ih, and_assoc]

theorem program_pure (fields : Fields) (mod signed : Bool) (state : State) (codeField : Nat → Prop)
    (owned : ∀ slot, codeField (fields slot)) :
    PureRun codeField (program fields mod signed) state := by
  have static (ops : List Instruction) (current : State)
      (pure : PureRun codeField ops current) :
      ∀ instruction ∈ ops, codeField (destination instruction) := by
    induction ops generalizing current with
    | nil => simp
    | cons instruction rest ih =>
        intro op member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact pure.1
        · exact ih _ pure.2 op member
  have first := static (initializeData fields mod signed) state
    (initial_pure fields mod signed state codeField (fun slot _ => owned slot))
  have oneBody := static (body fields) state
    (DivisionBody.body_pure fields state codeField (fun slot _ => owned slot))
  have middle (count : Nat) : ∀ instruction ∈ repeatedBody fields count,
      codeField (destination instruction) := by
    induction count with
    | zero => simp [repeatedBody]
    | succ count ih =>
        intro instruction member
        simp only [repeatedBody, List.mem_append] at member
        rcases member with previous | current
        · exact ih instruction previous
        · exact oneBody instruction current
  have last := static (finishData fields mod signed) state
    (finish_pure fields mod signed state codeField (fun slot _ => owned slot))
  apply pure_of_destinations
  intro instruction member
  simp only [program, List.mem_append] at member
  rcases member with (firstMember | middleMember) | lastMember
  · exact first instruction firstMember
  · exact middle 32 instruction middleMember
  · exact last instruction lastMember

theorem program_length (fields : Fields) (mod signed : Bool) :
    (program fields mod signed).length =
      (if signed then (if mod then 37 else 42) else 10) + 736 + (if signed then 9 else 3) := by
  simp [program, initial_length, repeated_length, finish_length, Nat.add_assoc]


theorem loop_preserved (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (slot : Slot) (outside : slot ∉ DivisionBody.written) :
    (loopState fields mod signed state).memory (fields slot) =
      (run (initializeData fields mod signed) state).memory (fields slot) := by
  rw [loopState]
  apply frame
  intro other member
  exact separate.ne (fun equality => outside (equality ▸ member))

theorem program_inputs (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (program fields mod signed) state).memory (fields .x) = state.memory (fields .x) ∧
    (run (program fields mod signed) state).memory (fields .y) = state.memory (fields .y) := by
  constructor
  · rw [program_execution, finish_field fields mod signed _ separate .x]
    simp only [finishValue]
    rw [loop_preserved fields mod signed state separate .x (by decide),
      initial_field fields mod signed state separate .x]
    rfl
  · rw [program_execution, finish_field fields mod signed _ separate .y]
    simp only [finishValue]
    rw [loop_preserved fields mod signed state separate .y (by decide),
      initial_field fields mod signed state separate .y]
    rfl

theorem program_frame (fields : Fields) (mod signed : Bool) (state : State) (field : Nat)
    (outside : ∀ slot, field ≠ fields slot) :
    (run (program fields mod signed) state).memory field = state.memory field := by
  rw [program_execution, finish_frame fields mod signed _ field (fun slot _ => outside slot),
    loopState, frame fields _ 32 field (fun slot _ => outside slot),
    initial_frame fields mod signed state field (fun slot _ => outside slot)]

theorem displacement_reset (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) :
    (run (program fields mod signed) state).memory (fields .displacement) = 0 := by
  rw [program_execution, finish_field fields mod signed _ separate .displacement]
  rfl

theorem program_carry (fields : Fields) (mod signed : Bool) (state : State)
    (separate : Separate fields) (nonzero : state.memory (fields .y) ≠ 0) :
    (run (program fields mod signed) state).carry =
      if signed then
        (negative mod (state.memory (fields .x)) (state.memory (fields .y)) &&
          decide (0 < (BitVec.ofNat 32
            (magnitudeResult mod (state.memory (fields .x)) (state.memory (fields .y)))).toNat ∧
            (BitVec.ofNat 32
            (magnitudeResult mod (state.memory (fields .x)) (state.memory (fields .y)))).toNat < 2147483648))
      else false := by
  rw [program_execution]
  cases signed with
  | false =>
      rw [finish_carry fields mod false _ separate]
      simp only [Bool.false_eq_true, ite_false]
      change (run (body fields) (iterate fields 31
        (run (initializeData fields mod false) state))).carry = false
      exact DivisionBody.body_carry fields _ separate
  | true =>
      rw [finish_signed_carry fields mod _ separate _ (loop_sign fields mod state separate),
        loop_result fields mod true state separate nonzero]
      rfl

end SmcTuring.Appendix.DivisionDataCorrect

