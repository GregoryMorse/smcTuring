module
public import SmcTuring.Memory
public import SmcTuring.Native.Arithmetic

public section

namespace SmcTuring.Appendix.Machine32

abbrev Word := BitVec 32

/-- Selected 32-bit effects of the printed appendix's memory-writing operations.
Field coordinates are logical words; byte layout and hardware fetch are separate.
Only the accumulator and CF are observed by this prefix. -/
structure State where
  accumulator : Word
  carry : Bool
  memory : Nat → Word

inductive Instruction where
  | store (field : Nat) (value : Word)
  | exchange (field : Nat)
  | xorConstant (field : Nat) (value : Word)
  | subtractAcc (field : Nat)
  | addAcc (field : Nat)
  | negate (field : Nat)
  | sbbZero (field : Nat)
  | complement (field : Nat)
  | andField (field source : Nat)
  | xorField (field source : Nat)
  deriving DecidableEq, Repr

@[expose] def destination : Instruction → Nat
  | .store field _ | .exchange field | .xorConstant field _
  | .subtractAcc field | .addAcc field | .negate field | .sbbZero field
  | .complement field | .andField field _ | .xorField field _ => field

@[expose] def put (state : State) (field : Nat) (value : Word) (carry : Bool) : State :=
  { state with memory := write state.memory field value, carry := carry }

/-- NEG has CF exactly when its original operand is nonzero. NOT and XCHG
preserve CF; memory XOR/AND clear it. A zero-mask SBB has the expected borrow. -/
@[expose] def execute (instruction : Instruction) (state : State) : State :=
  match instruction with
  | .store field value => put state field value state.carry
  | .exchange field =>
    { state with accumulator := state.memory field, memory := write state.memory field state.accumulator }
  | .xorConstant field value => put state field (state.memory field ^^^ value) false
  | .subtractAcc field => put state field (state.memory field - state.accumulator)
      (decide ((state.memory field).toNat < state.accumulator.toNat))
  | .addAcc field => put state field (state.memory field + state.accumulator)
      ((state.memory field).uaddOverflow state.accumulator)
  | .negate field => put state field (-state.memory field) (decide (state.memory field ≠ 0))
  | .sbbZero field => put state field
      (state.memory field - (if state.carry then 1 else 0))
      (decide ((state.memory field).toNat < (if state.carry then 1 else 0 : Nat)))
  | .complement field => put state field (~~~ state.memory field) state.carry
  | .andField field source => put state field (state.memory field &&& state.memory source) false
  | .xorField field source => put state field (state.memory field ^^^ state.memory source) false

@[expose] def run : List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)

@[expose] def footprint (instruction : Instruction) : List Nat := [destination instruction]
@[expose] def PureRun (codeField : Nat → Prop) : List Instruction → State → Prop
  | [], _ => True
  | instruction :: rest, state =>
      codeField (destination instruction) ∧ PureRun codeField rest (execute instruction state)

theorem every_instruction_writes (instruction : Instruction) : footprint instruction ≠ [] := by
  simp [footprint]

theorem execute_memory_frame (instruction : Instruction) (state : State) (field : Nat)
    (separate : field ≠ destination instruction) :
    (execute instruction state).memory field = state.memory field := by
  cases instruction <;> simp_all [execute, put, destination, write]

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem run_memory_frame (program : List Instruction) (state : State) (field : Nat)
    (separate : ∀ instruction ∈ program, field ≠ destination instruction) :
    (run program state).memory field = state.memory field := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [run, ih _ (fun op member => separate op (by simp [member])),
      execute_memory_frame instruction state field (separate instruction (by simp))]

theorem pure_of_destinations (codeField : Nat → Prop) (program : List Instruction) (state : State)
    (owned : ∀ instruction ∈ program, codeField (destination instruction)) :
    PureRun codeField program state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
    exact ⟨owned instruction (by simp), ih _ (fun op member => owned op (by simp [member]))⟩

end SmcTuring.Appendix.Machine32
