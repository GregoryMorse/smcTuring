module
public import SmcTuring.Appendix.ConstantAlgebra
public import SmcTuring.X64.HalfFrame

public section

namespace SmcTuring.Appendix.ConstantWords

open Machine32

/-- Selected literal word effects. ADD-FROM consumes the current immediate
    of the final ADD owner, written by the preceding three-operation macros. -/
inductive Instruction where
  | selected (instruction : Machine32.Instruction)
  | storeAcc (field : Nat)
  | shiftLeft (field count : Nat)
  | addFrom (field source : Nat)
  deriving DecidableEq, Repr

@[expose] def destination : Instruction -> Nat
  | .selected op => Machine32.destination op
  | .storeAcc field | .shiftLeft field _ | .addFrom field _ => field

/-- Emitted SHL counts are proved to lie in 1..31; zero shifts are omitted. -/
@[expose] def execute : Instruction -> State -> State
  | .selected op, state => Machine32.execute op state
  | .storeAcc field, state => put state field state.accumulator state.carry
  | .shiftLeft field count, state => put state field (state.memory field <<< count)
      ((state.memory field).getLsbD (32 - count))
  | .addFrom field source, state => put state field (state.memory field + state.memory source)
      ((state.memory field).uaddOverflow (state.memory source))

@[expose] def run : List Instruction -> State -> State
  | [], state => state
  | op :: rest, state => run rest (execute op state)

@[expose] def shift (field count : Nat) : List Instruction :=
  if count = 0 then [] else [.shiftLeft field count]

@[expose] def copy (data scratch : Nat) : List Instruction :=
  [.selected (.exchange data), .storeAcc scratch, .selected (.exchange data)]

@[expose] def accumulate (data scratch : Nat) : List Instruction :=
  [.selected (.exchange data), .selected (.addAcc scratch), .selected (.exchange data)]

@[expose] def tail : Nat -> Nat -> Nat -> Word -> List Instruction
  | 0, _, _, _ => []
  | fuel + 1, data, scratch, value =>
      shift data (ConstantAlgebra.zeros value + 1) ++
      if ConstantAlgebra.rest value = 0 then [.addFrom data scratch]
      else accumulate data scratch ++ tail fuel data scratch (ConstantAlgebra.rest value)

/-- The published emitter with M08's local gap correction and zero case. All
    decisions inspect the constant at compile time; no runtime branch is added. -/
@[expose] def program (data scratch : Nat) (value : Word) : List Instruction :=
  if value = 0 then [.selected (.store data 0)]
  else shift data (ConstantAlgebra.zeros value) ++
    if ConstantAlgebra.rest value = 0 then []
    else copy data scratch ++ tail 31 data scratch (ConstantAlgebra.rest value)

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons op rest ih => simpa [run] using ih (execute op state)

theorem execute_frame (op : Instruction) (state : State) (field : Nat)
    (outside : field ≠ destination op) : (execute op state).memory field = state.memory field := by
  cases op with
  | selected op => exact Machine32.execute_memory_frame op state field outside
  | _ => simp_all [execute, put, destination, write]

theorem shift_data (data count : Nat) (state : State) :
    (run (shift data count) state).memory data = state.memory data <<< count := by
  by_cases zero : count = 0
  · simp [shift, zero, run]
  · simp [shift, zero, run, execute, put, write]

theorem shift_frame (data count field : Nat) (state : State) (outside : field ≠ data) :
    (run (shift data count) state).memory field = state.memory field := by
  by_cases zero : count = 0 <;> simp [shift, zero, run, execute, put, write, outside]

theorem shift_accumulator (data count : Nat) (state : State) :
    (run (shift data count) state).accumulator = state.accumulator := by
  by_cases zero : count = 0 <;> simp [shift, zero, run, execute, put]

theorem copy_effect (data scratch : Nat) (state : State) (separate : scratch ≠ data) :
    run (copy data scratch) state = put state scratch (state.memory data) state.carry := by
  simp [copy, run, execute, Machine32.execute, put, separate, Ne.symm separate,
    X64.HalfFrame.restored_exchange]

theorem accumulate_effect (data scratch : Nat) (state : State) (separate : scratch ≠ data) :
    run (accumulate data scratch) state = put state scratch (state.memory scratch + state.memory data)
      ((state.memory scratch).uaddOverflow (state.memory data)) := by
  simp [accumulate, run, execute, Machine32.execute, put, separate, Ne.symm separate,
    X64.HalfFrame.restored_exchange]

theorem tail_data (fuel data scratch : Nat) (value : Word) (state : State)
    (separate : scratch ≠ data) (nonzero : value ≠ 0) (bound : value.toNat < 2 ^ fuel) :
    (run (tail fuel data scratch value) state).memory data =
      ConstantAlgebra.tail fuel (state.memory data) value (state.memory scratch) := by
  induction fuel generalizing value state with
  | zero =>
      have small : value.toNat < 1 := by simpa using bound
      have zero : value = 0 := by
        apply BitVec.eq_of_toNat_eq
        change value.toNat = 0
        omega
      exact (nonzero zero).elim
  | succ fuel ih =>
      rw [tail, run_append]
      by_cases terminal : ConstantAlgebra.rest value = 0
      · simp [terminal, run, execute, put, write, shift_data, shift_frame, separate,
          ConstantAlgebra.tail, BitVec.add_comm]
      · rw [ite_eq_right terminal, run_append, accumulate_effect _ _ _ separate,
          ih _ _ terminal (ConstantAlgebra.rest_bound value fuel bound)]
        rw [ConstantAlgebra.tail, ite_eq_right terminal]
        simp [put, write, Ne.symm separate, shift_data, shift_frame, separate]

/-- A complete emitted word trace, with the final ADD using its actual patched
    operand. No product or scratch initialization is supplied as a premise. -/
theorem correct (data scratch : Nat) (value : Word) (state : State) (separate : scratch ≠ data) :
    (run (program data scratch value) state).memory data = state.memory data * value := by
  by_cases zero : value = 0
  · simp [program, zero, run, execute, Machine32.execute, put, write]
  · rw [program, ite_eq_right zero, run_append]
    by_cases terminal : ConstantAlgebra.rest value = 0
    · rw [ite_eq_left terminal, run, shift_data]
      simpa [terminal] using ConstantAlgebra.first_invariant (state.memory data) value zero
    · rw [ite_eq_right terminal, run_append, copy_effect _ _ _ separate,
          tail_data _ _ _ _ _ separate terminal (ConstantAlgebra.rest_bound value 31 value.isLt)]
      simp only [put, write, Ne.symm separate, ↓reduceIte, shift_data]
      rw [ConstantAlgebra.tail_correct _ _ _ _ terminal (ConstantAlgebra.rest_bound value 31 value.isLt)]
      exact ConstantAlgebra.first_invariant (state.memory data) value zero

@[expose] def Legal (op : Instruction) : Prop := match op with
  | .shiftLeft _ count => 0 < count ∧ count < 32
  | _ => True

theorem shift_legal (data count : Nat) (bound : count < 32) :
    ∀ op ∈ shift data count, Legal op := by
  intro op member
  by_cases zero : count = 0
  · simp [shift, zero] at member
  · simp [shift, zero] at member
    subst op
    simp [Legal]
    omega

theorem tail_legal (fuel data scratch : Nat) (value : Word) (nonzero : value ≠ 0)
    (bound : value.toNat < 2 ^ fuel) (fuelBound : fuel ≤ 31) :
    ∀ op ∈ tail fuel data scratch value, Legal op := by
  induction fuel generalizing value with
  | zero => simp [tail]
  | succ fuel ih =>
      have count := ConstantAlgebra.gap_count_lt value nonzero (fuel + 1) bound
      intro op member
      simp only [tail, List.mem_append] at member
      rcases member with first | last
      · exact shift_legal _ _ (by omega) op first
      · by_cases terminal : ConstantAlgebra.rest value = 0
        · simp [terminal] at last
          subst op
          trivial
        · simp only [terminal, ↓reduceIte, List.mem_append] at last
          rcases last with head | rest
          · simp [accumulate] at head
            rcases head with rfl | rfl | rfl <;> trivial
          · exact ih _ terminal (ConstantAlgebra.rest_bound value fuel bound) (by omega) op rest

theorem program_legal (data scratch : Nat) (value : Word) :
    ∀ op ∈ program data scratch value, Legal op := by
  intro op member
  by_cases zero : value = 0
  · simp [program, zero] at member
    subst op
    trivial
  · rw [program, ite_eq_right zero] at member
    rcases List.mem_append.mp member with head | rest
    · exact shift_legal _ _ (ConstantAlgebra.zeros_lt value zero) op head
    · by_cases terminal : ConstantAlgebra.rest value = 0
      · simp [terminal] at rest
      · simp only [terminal, ↓reduceIte, List.mem_append] at rest
        rcases rest with head | rest
        · simp [copy] at head
          rcases head with rfl | rfl | rfl <;> trivial
        · exact tail_legal _ _ _ _ terminal (ConstantAlgebra.rest_bound value 31 value.isLt) (by decide) op rest

theorem tail_owned (fuel data scratch : Nat) (value : Word) :
    ∀ op ∈ tail fuel data scratch value, destination op = data ∨ destination op = scratch := by
  induction fuel generalizing value with
  | zero => simp [tail]
  | succ fuel ih =>
      intro op member
      simp only [tail, shift, Nat.succ_ne_zero,
        ↓reduceIte, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | rest
      · exact Or.inl rfl
      · split at rest
        · simp only [List.mem_singleton] at rest
          subst op
          exact Or.inl rfl
        · rcases List.mem_append.mp rest with head | rest
          · simp [accumulate] at head
            rcases head with rfl | rfl | rfl <;> simp [destination, Machine32.destination]
          · exact ih _ op rest

theorem program_owned (data scratch : Nat) (value : Word) :
    ∀ op ∈ program data scratch value, destination op = data ∨ destination op = scratch := by
  intro op member
  simp only [program] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst op
    exact Or.inl rfl
  · rcases List.mem_append.mp member with head | rest
    · simp only [shift] at head
      split at head
      · simp at head
      · simp only [List.mem_singleton] at head
        subst op
        exact Or.inl rfl
    · split at rest
      · simp at rest
      · rcases List.mem_append.mp rest with head | rest
        · simp [copy] at head
          rcases head with rfl | rfl | rfl <;> simp [destination, Machine32.destination]
        · exact tail_owned _ _ _ _ op rest

theorem run_frame (ops : List Instruction) (state : State) (field : Nat)
    (outside : ∀ op ∈ ops, field ≠ destination op) :
    (run ops state).memory field = state.memory field := by
  induction ops generalizing state with
  | nil => rfl
  | cons op rest ih =>
      rw [run, ih _ (fun i member => outside i (by simp [member])),
        execute_frame op state field (outside op (by simp))]

theorem frame (data scratch field : Nat) (value : Word) (state : State)
    (outsideData : field ≠ data) (outsideScratch : field ≠ scratch) :
    (run (program data scratch value) state).memory field = state.memory field := by
  apply run_frame
  intro op member
  rcases program_owned data scratch value op member with owned | owned <;> simp_all

theorem tail_accumulator (fuel data scratch : Nat) (value : Word) (state : State)
    (separate : scratch ≠ data) :
    (run (tail fuel data scratch value) state).accumulator = state.accumulator := by
  induction fuel generalizing value state with
  | zero => rfl
  | succ fuel ih =>
      rw [tail, run_append]
      by_cases terminal : ConstantAlgebra.rest value = 0
      · simp [terminal, run, execute, put, shift_accumulator]
      · rw [ite_eq_right terminal, run_append, accumulate_effect _ _ _ separate, ih _ _]
        simp [put, shift_accumulator]

theorem accumulator (data scratch : Nat) (value : Word) (state : State) (separate : scratch ≠ data) :
    (run (program data scratch value) state).accumulator = state.accumulator := by
  by_cases zero : value = 0
  · simp [program, zero, run, execute, Machine32.execute, put]
  · rw [program, ite_eq_right zero, run_append]
    by_cases terminal : ConstantAlgebra.rest value = 0
    · simp [terminal, run, shift_accumulator]
    · rw [ite_eq_right terminal, run_append, copy_effect _ _ _ separate, tail_accumulator _ _ _ _ _ separate]
      simp [put, shift_accumulator]

@[expose] def PureRun (codeField : Nat -> Prop) : List Instruction -> State -> Prop
  | [], _ => True
  | op :: rest, state => Legal op ∧ codeField (destination op) ∧ PureRun codeField rest (execute op state)

theorem pure_of_owned_legal (ops : List Instruction) (state : State) (codeField : Nat -> Prop)
    (legal : ∀ op ∈ ops, Legal op) (owned : ∀ op ∈ ops, codeField (destination op)) :
    PureRun codeField ops state := by
  induction ops generalizing state with
  | nil => trivial
  | cons op rest ih =>
      exact ⟨legal op (by simp), owned op (by simp),
        ih _ (fun i member => legal i (by simp [member])) (fun i member => owned i (by simp [member]))⟩

theorem pure (data scratch : Nat) (value : Word) (state : State) (codeField : Nat -> Prop)
    (dataOwned : codeField data) (scratchOwned : codeField scratch) :
    PureRun codeField (program data scratch value) state := by
  apply pure_of_owned_legal _ _ _ (program_legal data scratch value)
  intro op member
  rcases program_owned data scratch value op member with owned | owned <;> simp_all

theorem tail_length (fuel data scratch : Nat) (value : Word) :
    (tail fuel data scratch value).length ≤ 4 * fuel := by
  induction fuel generalizing value with
  | zero => simp [tail]
  | succ fuel ih =>
      have shifted : (shift data (ConstantAlgebra.zeros value + 1)).length = 1 := by
        simp [shift]
      rw [tail, List.length_append, shifted]
      split
      · simp
        omega
      · have h := ih (ConstantAlgebra.rest value)
        simp only [List.length_append, accumulate, List.length_cons, List.length_nil]
        omega

theorem program_length (data scratch : Nat) (value : Word) :
    (program data scratch value).length ≤ 128 := by
  have shifted : (shift data (ConstantAlgebra.zeros value)).length ≤ 1 := by
    simp only [shift]
    split <;> simp
  rw [program]
  split
  · simp
  · rw [List.length_append]
    split
    · simp
      omega
    · have h := tail_length 31 data scratch (ConstantAlgebra.rest value)
      simp only [List.length_append, copy, List.length_cons, List.length_nil]
      omega

/-- Positive repair contract for the complete compiled word trace, with arbitrary
    original scratch and backing words. Native byte/ISA realization is separate. -/
theorem contract (data scratch : Nat) (value : Word) (state : State) (codeField : Nat -> Prop)
    (separate : scratch ≠ data) (dataOwned : codeField data) (scratchOwned : codeField scratch) :
    (run (program data scratch value) state).memory data = state.memory data * value ∧
    (run (program data scratch value) state).accumulator = state.accumulator ∧
    PureRun codeField (program data scratch value) state ∧
    (program data scratch value).length ≤ 128 ∧
    ∀ field, field ≠ data -> field ≠ scratch ->
      (run (program data scratch value) state).memory field = state.memory field := by
  exact ⟨correct _ _ _ _ separate, accumulator _ _ _ _ separate,
    pure _ _ _ _ _ dataOwned scratchOwned, program_length _ _ _,
    fun field outsideData outsideScratch => frame _ _ _ _ _ outsideData outsideScratch⟩

end SmcTuring.Appendix.ConstantWords
