module
public import SmcTuring.Appendix.DivisionWords
public import SmcTuring.Appendix.DivisionWordAlgebra

public section
namespace SmcTuring.Appendix.DivisionPrefixes
open Machine32 (Word State put)
open DivisionWords
open DivisionSignedAlgebra

theorem sample_field (fields : Fields) (source target observed : Slot) (state : State)
    (separate : Separate fields) (different : target ≠ source) :
    (run (DivisionWords.sample fields source target) state).memory (fields observed) =
      if observed = target then DivisionSignedAlgebra.sample (state.memory (fields source))
      else state.memory (fields observed) := by
  by_cases hit : observed = target
  · subst observed
    simp [DivisionWords.sample, run, execute, selected, MultiplyWords.execute,
      Machine32.execute, put, write, field_eq fields separate, different,
      Ne.symm different, DivisionSignedAlgebra.sample]
  · by_cases input : observed = source
    · subst observed
      simp [DivisionWords.sample, run, execute, selected, MultiplyWords.execute,
        Machine32.execute, put, write, field_eq fields separate, different,
        Ne.symm different]
    · simp [DivisionWords.sample, run, execute, selected, MultiplyWords.execute,
        Machine32.execute, put, write, field_eq fields separate, different,
        Ne.symm different, hit, input]

theorem sample_accumulator (fields : Fields) (source target : Slot) (state : State)
    (separate : Separate fields) (different : target ≠ source) :
    (run (DivisionWords.sample fields source target) state).accumulator = state.accumulator := by
  simp [DivisionWords.sample, run, execute, selected, MultiplyWords.execute,
    Machine32.execute, put, write, field_eq fields separate, different, Ne.symm different]

theorem sample_carry (fields : Fields) (source target : Slot) (state : State) :
    (run (DivisionWords.sample fields source target) state).carry = false := by
  simp [DivisionWords.sample, run, execute, selected, MultiplyWords.execute, Machine32.execute, put]

@[expose] def signValue (fields : Fields) (mod : Bool) (state : State) : Slot → Word
  | .signX => if mod then BranchAlgebra.mask (state.memory (fields .x)).msb
      else DivisionSignedAlgebra.sample (state.memory (fields .x))
  | .signY => if mod then state.memory (fields .signY)
      else BranchAlgebra.mask (negative mod (state.memory (fields .x)) (state.memory (fields .y)))
  | .resultSign => BranchAlgebra.mask
      (negative mod (state.memory (fields .x)) (state.memory (fields .y)))
  | slot => state.memory (fields slot)

theorem sign_field (fields : Fields) (mod : Bool) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (signPrefix fields mod) state).memory (fields slot) = signValue fields mod state slot := by
  have sx := sample_sign (state.memory (fields .x))
  have sy := sample_sign (state.memory (fields .y))
  unfold DivisionSignedAlgebra.sample at sx sy
  cases mod <;> cases slot <;>
    cases hx : (state.memory (fields .x)).msb <;>
    cases hy : (state.memory (fields .y)).msb <;>
    simp [signPrefix, signValue, DivisionWords.sample, run, execute, selected,
      MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
      sx, sy, hx, hy, negative, BranchAlgebra.mask, DivisionSignedAlgebra.sample]
  all_goals decide

theorem sign_accumulator (fields : Fields) (mod : Bool) (state : State)
    (separate : Separate fields) :
    (run (signPrefix fields mod) state).accumulator = state.accumulator := by
  cases mod <;> simp [signPrefix, DivisionWords.sample, run, execute, selected,
    MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate]

theorem sign_carry (fields : Fields) (mod : Bool) (state : State)
    (separate : Separate fields) :
    (run (signPrefix fields mod) state).carry =
      negative mod (state.memory (fields .x)) (state.memory (fields .y)) := by
  have sx := sample_sign (state.memory (fields .x))
  have sy := sample_sign (state.memory (fields .y))
  unfold DivisionSignedAlgebra.sample at sx sy
  cases mod <;> cases hx : (state.memory (fields .x)).msb <;>
    cases hy : (state.memory (fields .y)).msb <;>
    simp [signPrefix, DivisionWords.sample, run, execute, selected,
      MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
      sx, sy, hx, hy, negative]
  all_goals decide

@[expose] def normalizeProgram (fields : Fields) (divisor : Bool) : List Instruction :=
  if divisor then normalize fields .y .divisor .yMask .yDouble
  else normalize fields .x .low .xMask .xDouble

@[expose] def normalizeValue (fields : Fields) (divisor : Bool) (state : State) (slot : Slot) : Word :=
  let word := state.memory (fields (if divisor then .y else .x))
  if slot = (if divisor then .divisor else .low) then magnitude word
  else if slot = (if divisor then .yMask else .xMask) then BranchAlgebra.mask word.msb
  else if slot = (if divisor then .yDouble else .xDouble) then
    (word <<< 1) &&& BranchAlgebra.mask word.msb
  else state.memory (fields slot)

theorem masked_normalization (word : Word) :
    word - ((word <<< 1) &&& BranchAlgebra.mask word.msb) = magnitude word := by
  rw [BitVec.and_comm]
  exact absolute_normalization word

theorem normalize_field (fields : Fields) (divisor : Bool) (state : State)
    (separate : Separate fields) (slot : Slot) :
    (run (normalizeProgram fields divisor) state).memory (fields slot) =
      normalizeValue fields divisor state slot := by
  cases divisor <;> cases slot <;>
    simp only [normalizeProgram, normalizeValue, normalize, run, execute, selected,
      MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
      Bool.false_eq_true, ite_false, ite_true, reduceCtorEq, BitVec.sub_add_cancel,
      normalize_mask, masked_normalization]

theorem normalize_accumulator (fields : Fields) (divisor : Bool) (state : State)
    (separate : Separate fields) :
    (run (normalizeProgram fields divisor) state).accumulator = state.accumulator := by
  cases divisor <;> simp [normalizeProgram, normalize, run, execute, selected,
    MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate]

theorem normalize_carry (fields : Fields) (divisor : Bool) (state : State)
    (separate : Separate fields) :
    (run (normalizeProgram fields divisor) state).carry = false := by
  cases divisor <;> simp only [normalizeProgram, normalize, run, execute, selected,
    MultiplyWords.execute, Machine32.execute, put, write, field_eq fields separate,
    Bool.false_eq_true, ite_false, ite_true, reduceCtorEq, BitVec.sub_add_cancel,
    normalize_mask, DivisionWordAlgebra.masked_double_no_borrow]

theorem sign_length (fields : Fields) (mod : Bool) : (signPrefix fields mod).length =
    if mod then 7 else 12 := by cases mod <;> rfl

theorem normalize_length (fields : Fields) (divisor : Bool) :
    (normalizeProgram fields divisor).length = 12 := by cases divisor <;> rfl

end SmcTuring.Appendix.DivisionPrefixes
