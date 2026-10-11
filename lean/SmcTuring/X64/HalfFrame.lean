module
public import SmcTuring.Appendix.Machine32
public import SmcTuring.X64.HalfWords

public section

namespace SmcTuring.X64.HalfFrame

open Appendix.Machine32

/-- The four binary forms used by the printed corresponding-half pattern.
Only low accumulator, CF and complete logical operand words are observed. -/
inductive BinaryOp where
  | move | xor | and | or
  deriving DecidableEq, Repr

@[expose] def BinaryOp.value : BinaryOp → Word → Word → Word
  | .move, _, source => source
  | .xor, target, source => target ^^^ source
  | .and, target, source => target &&& source
  | .or, target, source => target ||| source

@[expose] def BinaryOp.carry : BinaryOp → Bool → Bool
  | .move, incoming => incoming
  | .xor, _ | .and, _ | .or, _ => false

@[expose] def BinaryOp.whole : BinaryOp → BitVec 64 → BitVec 64 → BitVec 64
  | .move, _, source => source
  | .xor, target, source => target ^^^ source
  | .and, target, source => target &&& source
  | .or, target, source => target ||| source

inductive Instruction where
  | exchange (field : Nat)
  | useAcc (op : BinaryOp) (field : Nat)
  | complement (field : Nat)
  deriving DecidableEq, Repr

@[expose] def destination : Instruction → Nat
  | .exchange field | .useAcc _ field | .complement field => field

@[expose] def execute : Instruction → State → State
  | .exchange field, state => Appendix.Machine32.execute (.exchange field) state
  | .useAcc op field, state =>
      put state field (op.value (state.memory field) state.accumulator) (op.carry state.carry)
  | .complement field, state => Appendix.Machine32.execute (.complement field) state

@[expose] def run : List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)

@[expose] def footprint (instruction : Instruction) : List Nat := [destination instruction]
@[expose] def PureRun (codeField : Nat → Prop) : List Instruction → State → Prop
  | [], _ => True
  | instruction :: rest, state =>
      codeField (destination instruction) ∧ PureRun codeField rest (execute instruction state)

/-- Literal USEWORD32(DATAOP(op, target, acmltr32), source).
The operation reads the actual exchanged accumulator, not a supplied result. -/
@[expose] def useWord (op : BinaryOp) (target source : Nat) : List Instruction :=
  [.exchange source, .useAcc op target, .exchange source]

theorem every_instruction_writes (instruction : Instruction) : footprint instruction ≠ [] := by
  simp [footprint]

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem pure_append (codeField : Nat → Prop) (first second : List Instruction) (state : State) :
    PureRun codeField (first ++ second) state ↔
      PureRun codeField first state ∧ PureRun codeField second (run first state) := by
  induction first generalizing state with
  | nil => simp [PureRun, run]
  | cons instruction rest ih => simp [PureRun, run, ih, and_assoc]

theorem restored_exchange (memory : Nat → Word) (target source : Nat) (accumulator value : Word)
    (separate : target ≠ source) :
    write (write (write memory source accumulator) target value) source (memory source) =
      write memory target value := by
  rw [writes_commute (write memory source accumulator) target source value (memory source) separate,
    write_overwrite, write_back]

theorem carry_idempotent (op : BinaryOp) (carry : Bool) : op.carry (op.carry carry) = op.carry carry := by
  cases op <;> rfl

theorem use_effect (op : BinaryOp) (target source : Nat) (state : State)
    (separate : target ≠ source) :
    run (useWord op target source) state =
      put state target (op.value (state.memory target) (state.memory source)) (op.carry state.carry) := by
  simp [useWord, run, execute, Appendix.Machine32.execute, put, separate, Ne.symm separate,
    restored_exchange]

theorem use_accumulator (op : BinaryOp) (target source : Nat) (state : State)
    (separate : target ≠ source) :
    (run (useWord op target source) state).accumulator = state.accumulator := by
  rw [use_effect op target source state separate]
  rfl

theorem use_source (op : BinaryOp) (target source : Nat) (state : State)
    (separate : target ≠ source) :
    (run (useWord op target source) state).memory source = state.memory source := by
  rw [use_effect op target source state separate]
  exact read_write_other _ _ _ _ (Ne.symm separate)

theorem use_target (op : BinaryOp) (target source : Nat) (state : State)
    (separate : target ≠ source) :
    (run (useWord op target source) state).memory target =
      op.value (state.memory target) (state.memory source) := by
  rw [use_effect op target source state separate]
  exact read_write_same _ _ _

theorem use_carry (op : BinaryOp) (target source : Nat) (state : State)
    (separate : target ≠ source) :
    (run (useWord op target source) state).carry = op.carry state.carry := by
  rw [use_effect op target source state separate]
  rfl

theorem use_frame (op : BinaryOp) (target source field : Nat) (state : State)
    (separate : target ≠ source) (outside : field ≠ target) :
    (run (useWord op target source) state).memory field = state.memory field := by
  rw [use_effect op target source state separate]
  exact read_write_other _ _ _ _ outside

theorem use_length (op : BinaryOp) (target source : Nat) : (useWord op target source).length = 3 := rfl

theorem use_pure (codeField : Nat → Prop) (op : BinaryOp) (target source : Nat) (state : State)
    (targetOwned : codeField target) (sourceOwned : codeField source) :
    PureRun codeField (useWord op target source) state := by
  simp [PureRun, useWord, destination, targetOwned, sourceOwned]

structure Fields where
  targetLow : Nat
  targetHigh : Nat
  sourceLow : Nat
  sourceHigh : Nat

/-- Static logical separation. A native placement must additionally give full
nonoverlapping byte ranges at the corresponding printed offsets. -/
structure Separate (fields : Fields) : Prop where
  targets : fields.targetLow ≠ fields.targetHigh
  lowLow : fields.targetLow ≠ fields.sourceLow
  lowHigh : fields.targetLow ≠ fields.sourceHigh
  highLow : fields.targetHigh ≠ fields.sourceLow
  highHigh : fields.targetHigh ≠ fields.sourceHigh
  sources : fields.sourceLow ≠ fields.sourceHigh

@[expose] def targetWord (fields : Fields) (state : State) : BitVec 64 :=
  HalfWords.pack (state.memory fields.targetLow) (state.memory fields.targetHigh)
@[expose] def sourceWord (fields : Fields) (state : State) : BitVec 64 :=
  HalfWords.pack (state.memory fields.sourceLow) (state.memory fields.sourceHigh)
@[expose] def splitProgram (op : BinaryOp) (fields : Fields) : List Instruction :=
  useWord op fields.targetLow fields.sourceLow ++ useWord op fields.targetHigh fields.sourceHigh
@[expose] def splitMemory (op : BinaryOp) (fields : Fields) (memory : Nat → Word) : Nat → Word :=
  write (write memory fields.targetLow (op.value (memory fields.targetLow) (memory fields.sourceLow)))
    fields.targetHigh (op.value (memory fields.targetHigh) (memory fields.sourceHigh))

theorem split_effect (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    run (splitProgram op fields) state =
      { state with memory := splitMemory op fields state.memory, carry := op.carry state.carry } := by
  rw [splitProgram, run_append, use_effect op fields.targetLow fields.sourceLow state separate.lowLow,
    use_effect op fields.targetHigh fields.sourceHigh _ separate.highHigh]
  simp [put, splitMemory, Ne.symm separate.targets, Ne.symm separate.lowHigh, carry_idempotent]

theorem split_accumulator (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    (run (splitProgram op fields) state).accumulator = state.accumulator := by
  rw [split_effect op fields state separate]

theorem split_sources (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    (run (splitProgram op fields) state).memory fields.sourceLow = state.memory fields.sourceLow ∧
    (run (splitProgram op fields) state).memory fields.sourceHigh = state.memory fields.sourceHigh := by
  rw [split_effect op fields state separate]
  simp [splitMemory, Ne.symm separate.lowLow, Ne.symm separate.highLow,
    Ne.symm separate.lowHigh, Ne.symm separate.highHigh]

theorem split_carry (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    (run (splitProgram op fields) state).carry = op.carry state.carry := by
  rw [split_effect op fields state separate]

theorem split_frame (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields)
    (field : Nat) (outsideLow : field ≠ fields.targetLow) (outsideHigh : field ≠ fields.targetHigh) :
    (run (splitProgram op fields) state).memory field = state.memory field := by
  rw [split_effect op fields state separate]
  simp [splitMemory, outsideLow, outsideHigh]

theorem split_length (op : BinaryOp) (fields : Fields) : (splitProgram op fields).length = 6 := rfl

theorem split_pure (codeField : Nat → Prop) (op : BinaryOp) (fields : Fields) (state : State)
    (owned : ∀ field ∈ [fields.targetLow, fields.targetHigh, fields.sourceLow, fields.sourceHigh], codeField field) :
    PureRun codeField (splitProgram op fields) state := by
  rw [splitProgram, pure_append]
  exact ⟨use_pure codeField op _ _ state (owned _ (by simp)) (owned _ (by simp)),
    use_pure codeField op _ _ _ (owned _ (by simp)) (owned _ (by simp))⟩

theorem split_value (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    targetWord fields (run (splitProgram op fields) state) =
      HalfWords.splitBinary op.value (targetWord fields state) (sourceWord fields state) := by
  rw [split_effect op fields state separate]
  simp [targetWord, sourceWord, splitMemory, separate.targets, HalfWords.splitBinary,
    HalfWords.low_pack, HalfWords.high_pack]

theorem split_correct (op : BinaryOp) (fields : Fields) (state : State) (separate : Separate fields) :
    targetWord fields (run (splitProgram op fields) state) =
      op.whole (targetWord fields state) (sourceWord fields state) := by
  rw [split_value op fields state separate]
  cases op with
  | move => exact HalfWords.split_mov _ _
  | xor => exact HalfWords.split_xor _ _
  | and => exact HalfWords.split_and _ _
  | or => exact HalfWords.split_or _ _

/-- The printed unary OP64 NOT form: one complete write to each target half. -/
@[expose] def complementProgram (fields : Fields) : List Instruction :=
  [.complement fields.targetLow, .complement fields.targetHigh]
@[expose] def complementMemory (fields : Fields) (memory : Nat → Word) : Nat → Word :=
  write (write memory fields.targetLow (~~~ memory fields.targetLow))
    fields.targetHigh (~~~ memory fields.targetHigh)

theorem complement_effect (fields : Fields) (state : State) (separate : fields.targetLow ≠ fields.targetHigh) :
    run (complementProgram fields) state = { state with memory := complementMemory fields state.memory } := by
  simp [complementProgram, run, execute, Appendix.Machine32.execute, put, complementMemory, Ne.symm separate]

theorem complement_correct (fields : Fields) (state : State) (separate : fields.targetLow ≠ fields.targetHigh) :
    targetWord fields (run (complementProgram fields) state) = ~~~ targetWord fields state := by
  rw [complement_effect fields state separate]
  have value := HalfWords.split_not (targetWord fields state)
  simpa [targetWord, complementMemory, separate, HalfWords.splitNot, HalfWords.low_pack,
    HalfWords.high_pack] using value

theorem complement_frame (fields : Fields) (state : State) (separate : fields.targetLow ≠ fields.targetHigh)
    (field : Nat) (outsideLow : field ≠ fields.targetLow) (outsideHigh : field ≠ fields.targetHigh) :
    (run (complementProgram fields) state).memory field = state.memory field := by
  rw [complement_effect fields state separate]
  simp [complementMemory, outsideLow, outsideHigh]

theorem complement_registers (fields : Fields) (state : State) (separate : fields.targetLow ≠ fields.targetHigh) :
    (run (complementProgram fields) state).accumulator = state.accumulator ∧
      (run (complementProgram fields) state).carry = state.carry := by
  rw [complement_effect fields state separate]
  exact ⟨rfl, rfl⟩

theorem complement_pure (codeField : Nat → Prop) (fields : Fields) (state : State)
    (lowOwned : codeField fields.targetLow) (highOwned : codeField fields.targetHigh) :
    PureRun codeField (complementProgram fields) state := by
  simp [PureRun, complementProgram, destination, lowOwned, highOwned]

theorem complement_length (fields : Fields) : (complementProgram fields).length = 2 := rfl

end SmcTuring.X64.HalfFrame
