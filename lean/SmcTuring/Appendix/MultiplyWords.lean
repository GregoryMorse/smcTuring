module
public import SmcTuring.Appendix.MultiplyAlgebra
public import SmcTuring.X64.HalfFrame

public section

namespace SmcTuring.Appendix.MultiplyWords

open Machine32 MultiplyAlgebra

@[simp] theorem full_and (word : Word) : BitVec.ofNat 32 4294967295 &&& word = word := by
  change BitVec.allOnes 32 &&& word = word
  exact BitVec.allOnes_and

@[simp] theorem and_full (word : Word) : word &&& BitVec.ofNat 32 4294967295 = word := by
  change word &&& BitVec.allOnes 32 = word
  exact BitVec.and_allOnes

inductive Slot where
  | x | y | result | factor | multiplier | total | delta | mask | displacement | bit | addMask | addend
  deriving DecidableEq, Repr

abbrev Fields := Slot -> Nat
abbrev Separate (fields : Fields) := Function.Injective fields

theorem field_eq (fields : Fields) (separate : Separate fields) (first second : Slot) :
    fields first = fields second ↔ first = second := separate.eq_iff

/-- Selected word effects of the printed multiplication blocks. Mutable
immediates are read from the actual current field memory. Byte fetch is separate. -/
inductive Instruction where
  | selected (instruction : Machine32.Instruction)
  | storeAcc (field : Nat)
  | andAcc (field : Nat)
  | selfStore (field : Nat)
  | copyFrom (field source : Nat)
  | addFrom (field source : Nat)
  | shiftLeft (field : Nat)
  | shiftRight (field : Nat)
  deriving DecidableEq, Repr

@[expose] def destination : Instruction -> Nat
  | .selected instruction => Machine32.destination instruction
  | .storeAcc field | .andAcc field | .selfStore field | .copyFrom field _
  | .addFrom field _ | .shiftLeft field | .shiftRight field => field

@[expose] def execute : Instruction -> State -> State
  | .selected instruction, state => Machine32.execute instruction state
  | .storeAcc field, state => put state field state.accumulator state.carry
  | .andAcc field, state => put state field (state.memory field &&& state.accumulator) false
  | .selfStore field, state => put state field (state.memory field) state.carry
  | .copyFrom field source, state => put state field (state.memory source) state.carry
  | .addFrom field source, state => put state field (state.memory field + state.memory source)
      ((state.memory field).uaddOverflow (state.memory source))
  | .shiftLeft field, state => put state field (state.memory field <<< 1) (state.memory field).msb
  | .shiftRight field, state => put state field (state.memory field >>> 1) ((state.memory field).getLsbD 0)

@[expose] def run : List Instruction -> State -> State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)

@[expose] def footprint (instruction : Instruction) : List Nat := [destination instruction]
@[expose] def PureRun (codeField : Nat -> Prop) : List Instruction -> State -> Prop
  | [], _ => True
  | instruction :: rest, state => codeField (destination instruction) ∧ PureRun codeField rest (execute instruction state)

@[expose] def copyProgram (target source : Nat) : List Instruction :=
  [.selected (.exchange source), .storeAcc target, .selected (.exchange source)]

@[expose] def initialProgram (fields : Fields) : List Instruction :=
  [.selected (.store (fields .total) 0)] ++
    copyProgram (fields .factor) (fields .x) ++ copyProgram (fields .multiplier) (fields .y)

/-- Listing 11's zero test and actual two-field mask/displacement patch.
M07 repairs only the delta store's field address and relocation expression. -/
@[expose] def guard (fields : Fields) (delta : Word) : List Instruction :=
  [.selected (.store (fields .mask) 0), .selected (.negate (fields .multiplier)),
   .selected (.sbbZero (fields .mask)), .selected (.negate (fields .multiplier)),
   .selected (.complement (fields .mask)), .selected (.store (fields .delta) delta),
   .selected (.andField (fields .mask) (fields .delta)),
   .selected (.xorField (fields .displacement) (fields .mask))]

/-- The literal seventeen data instructions between the two continuations.
SELF stores write their own current immediate, even when its value is unchanged. -/
@[expose] def body (fields : Fields) : List Instruction :=
  [.selected (.store (fields .bit) 1), .selected (.exchange (fields .multiplier)),
   .andAcc (fields .bit), .selected (.exchange (fields .multiplier)),
   .selected (.exchange (fields .factor)), .storeAcc (fields .addend),
   .selected (.exchange (fields .factor)), .selected (.store (fields .addMask) 0),
   .selfStore (fields .bit), .selected (.negate (fields .bit)), .selected (.sbbZero (fields .addMask)),
   .selected (.andField (fields .addend) (fields .addMask)), .addFrom (fields .total) (fields .addend),
   .selfStore (fields .factor), .shiftLeft (fields .factor),
   .selfStore (fields .multiplier), .shiftRight (fields .multiplier)]

@[expose] def finish (fields : Fields) : List Instruction :=
  [.selected (.store (fields .displacement) 0), .copyFrom (fields .result) (fields .total)]

theorem every_instruction_writes (instruction : Instruction) : footprint instruction ≠ [] := by simp [footprint]

theorem execute_frame (instruction : Instruction) (state : State) (field : Nat)
    (outside : field ≠ destination instruction) : (execute instruction state).memory field = state.memory field := by
  cases instruction with
  | selected instruction => exact Machine32.execute_memory_frame instruction state field outside
  | _ => simp_all [execute, put, destination, write]

theorem run_frame (program : List Instruction) (state : State) (field : Nat)
    (outside : ∀ instruction ∈ program, field ≠ destination instruction) :
    (run program state).memory field = state.memory field := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (fun op member => outside op (by simp [member])), execute_frame instruction state field (outside instruction (by simp))]

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem pure_of_destinations (codeField : Nat -> Prop) (program : List Instruction) (state : State)
    (owned : ∀ instruction ∈ program, codeField (destination instruction)) : PureRun codeField program state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
      exact ⟨owned instruction (by simp), ih _ (fun op member => owned op (by simp [member]))⟩

theorem copy_effect (target source : Nat) (state : State) (separate : target ≠ source) :
    run (copyProgram target source) state = put state target (state.memory source) state.carry := by
  simp [copyProgram, run, execute, Machine32.execute, put, separate, Ne.symm separate,
    X64.HalfFrame.restored_exchange]

theorem initialize_field (fields : Fields) (state : State) (separate : Separate fields) (slot : Slot) :
    (run (initialProgram fields) state).memory (fields slot) =
      match slot with
      | .factor => state.memory (fields .x)
      | .multiplier => state.memory (fields .y)
      | .total => 0
      | _ => state.memory (fields slot) := by
  cases slot <;> simp [initialProgram, copyProgram, run, execute, Machine32.execute, put, write, field_eq fields separate]

theorem initialize_accumulator (fields : Fields) (state : State) (separate : Separate fields) :
    (run (initialProgram fields) state).accumulator = state.accumulator := by
  simp [initialProgram, copyProgram, run, execute, Machine32.execute, put, write, field_eq fields separate]

theorem initialize_carry (fields : Fields) (state : State) : (run (initialProgram fields) state).carry = state.carry := by
  simp [initialProgram, copyProgram, run, execute, Machine32.execute, put]

@[expose] def guardValue (fields : Fields) (delta : Word) (state : State) : Slot -> Word
  | .delta => delta
  | .mask => if state.memory (fields .multiplier) = 0 then delta else 0
  | .displacement => state.memory (fields .displacement) ^^^ (if state.memory (fields .multiplier) = 0 then delta else 0)
  | slot => state.memory (fields slot)

theorem guard_field (fields : Fields) (delta : Word) (state : State) (separate : Separate fields) (slot : Slot) :
    (run (guard fields delta) state).memory (fields slot) = guardValue fields delta state slot := by
  by_cases zero : state.memory (fields .multiplier) = BitVec.ofNat 32 0
  · cases slot <;> simp [guard, guardValue, run, execute, Machine32.execute, put, write, field_eq fields separate, zero]
  · cases slot <;> simp [guard, guardValue, run, execute, Machine32.execute, put, write, field_eq fields separate, zero]

theorem guard_accumulator (fields : Fields) (delta : Word) (state : State) :
    (run (guard fields delta) state).accumulator = state.accumulator := by
  simp [guard, run, execute, Machine32.execute, put]

theorem guard_carry (fields : Fields) (delta : Word) (state : State) :
    (run (guard fields delta) state).carry = false := by
  simp [guard, run, execute, Machine32.execute, put]

theorem guard_displacement (fields : Fields) (delta : Word) (state : State) (separate : Separate fields)
    (initial : state.memory (fields .displacement) = 0) :
    (run (guard fields delta) state).memory (fields .displacement) =
      if state.memory (fields .multiplier) = 0 then delta else 0 := by
  rw [guard_field fields delta state separate .displacement]
  simp [guardValue, initial]

theorem guard_target (fields : Fields) (next target : Word) (state : State) (separate : Separate fields)
    (initial : state.memory (fields .displacement) = 0) :
    next + (run (guard fields (target - next)) state).memory (fields .displacement) =
      if state.memory (fields .multiplier) = 0 then target else next := by
  rw [guard_displacement fields (target - next) state separate initial]
  by_cases zero : state.memory (fields .multiplier) = BitVec.ofNat 32 0
  · simp [zero]
  · simp [zero]

@[expose] def bodyValue (fields : Fields) (state : State) : Slot -> Word
  | .factor => state.memory (fields .factor) <<< 1
  | .multiplier => state.memory (fields .multiplier) >>> 1
  | .total => state.memory (fields .total) + chosen (state.memory (fields .factor)) (state.memory (fields .multiplier))
  | .bit => -lowBit (state.memory (fields .multiplier))
  | .addMask => if lowBit (state.memory (fields .multiplier)) = 0 then 0 else -1
  | .addend => chosen (state.memory (fields .factor)) (state.memory (fields .multiplier))
  | slot => state.memory (fields slot)

theorem body_field (fields : Fields) (state : State) (separate : Separate fields) (slot : Slot) :
    (run (body fields) state).memory (fields slot) = bodyValue fields state slot := by
  rcases low_bit_cases (state.memory (fields .multiplier)) with zero | one
  · change BitVec.ofNat 32 1 &&& state.memory (fields .multiplier) = BitVec.ofNat 32 0 at zero
    cases slot <;> simp [body, bodyValue, chosen, lowBit, run, execute, Machine32.execute, put, write,
      field_eq fields separate, zero]
  · change BitVec.ofNat 32 1 &&& state.memory (fields .multiplier) = BitVec.ofNat 32 1 at one
    cases slot <;> simp [body, bodyValue, chosen, lowBit, run, execute, Machine32.execute, put, write,
      field_eq fields separate, one]

theorem body_accumulator (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).accumulator = state.accumulator := by
  simp [body, run, execute, Machine32.execute, put, write, field_eq fields separate]

theorem body_carry (fields : Fields) (state : State) (separate : Separate fields) :
    (run (body fields) state).carry = (state.memory (fields .multiplier)).getLsbD 0 := by
  simp [body, run, execute, Machine32.execute, put, write, field_eq fields separate]

theorem body_frame (fields : Fields) (state : State) (field : Nat)
    (outside : ∀ slot ∈ [Slot.factor, .multiplier, .total, .bit, .addMask, .addend], field ≠ fields slot) :
    (run (body fields) state).memory field = state.memory field := by
  apply run_frame
  simp_all [body, destination, Machine32.destination]

theorem finish_field (fields : Fields) (state : State) (separate : Separate fields) (slot : Slot) :
    (run (finish fields) state).memory (fields slot) =
      match slot with
      | .result => state.memory (fields .total)
      | .displacement => 0
      | _ => state.memory (fields slot) := by
  cases slot <;> simp [finish, run, execute, Machine32.execute, put, write, field_eq fields separate]

theorem finish_registers (fields : Fields) (state : State) :
    (run (finish fields) state).accumulator = state.accumulator ∧ (run (finish fields) state).carry = state.carry := by
  simp [finish, run, execute, Machine32.execute, put]

theorem initialize_pure (codeField : Nat -> Prop) (fields : Fields) (state : State)
    (owned : ∀ slot, codeField (fields slot)) : PureRun codeField (initialProgram fields) state := by
  simp [initialProgram, copyProgram, PureRun, destination, Machine32.destination, owned]

theorem guard_pure (codeField : Nat -> Prop) (fields : Fields) (delta : Word) (state : State)
    (owned : ∀ slot, codeField (fields slot)) : PureRun codeField (guard fields delta) state := by
  simp [guard, PureRun, destination, Machine32.destination, owned]

theorem body_pure (codeField : Nat -> Prop) (fields : Fields) (state : State)
    (owned : ∀ slot, codeField (fields slot)) : PureRun codeField (body fields) state := by
  simp [body, PureRun, destination, Machine32.destination, owned]

theorem finish_pure (codeField : Nat -> Prop) (fields : Fields) (state : State)
    (owned : ∀ slot, codeField (fields slot)) : PureRun codeField (finish fields) state := by
  simp [finish, PureRun, destination, Machine32.destination, owned]

theorem block_lengths (fields : Fields) (delta : Word) :
    (initialProgram fields).length = 7 ∧ (guard fields delta).length = 8 ∧
    (body fields).length = 17 ∧ (finish fields).length = 2 := by
  simp [initialProgram, copyProgram, guard, body, finish]

end SmcTuring.Appendix.MultiplyWords
