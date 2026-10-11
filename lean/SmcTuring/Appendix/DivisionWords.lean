module
public import SmcTuring.Appendix.DivisionSignedAlgebra
public import SmcTuring.Appendix.MultiplyWords

public section
namespace SmcTuring.Appendix.DivisionWords
open Machine32

inductive Slot where
  | x | y | result
  | signX | signY | resultSign | xMask | xDouble | yMask | yDouble | outputDouble
  | counter | delta | guardMask | displacement
  | low | oldLow | oldLow2 | high | divisor | divisor2 | restore | mask | maskComplement | quotientBit
  deriving DecidableEq, Repr

abbrev Fields := Slot → Nat
abbrev Separate (fields : Fields) := Function.Injective fields

theorem field_eq (fields : Fields) (separate : Separate fields) (first second : Slot) :
    fields first = fields second ↔ first = second := separate.eq_iff

/-- Each additional instruction writes a full current operand word.
The embedding reuses the already checked XCHG/MOV/Boolean/shift-one effects.
SHR 31 samples old bit 30 in CF; DEC preserves incoming CF. -/
inductive Instruction where
  | simple (instruction : MultiplyWords.Instruction)
  | subtractFrom (field source : Nat)
  | subtractConstant (field : Nat) (value : Word)
  | addConstant (field : Nat) (value : Word)
  | right31 (field : Nat)
  | adcZero (field : Nat)
  | decrement (field : Nat)
  deriving DecidableEq, Repr

@[expose] def destination : Instruction → Nat
  | .simple instruction => MultiplyWords.destination instruction
  | .subtractFrom field _ | .subtractConstant field _ | .addConstant field _
  | .right31 field | .adcZero field | .decrement field => field

@[expose] def execute : Instruction → State → State
  | .simple instruction, state => MultiplyWords.execute instruction state
  | .subtractFrom field source, state => put state field
      (state.memory field - state.memory source)
      (decide ((state.memory field).toNat < (state.memory source).toNat))
  | .subtractConstant field value, state => put state field
      (state.memory field - value) (decide ((state.memory field).toNat < value.toNat))
  | .addConstant field value, state => put state field
      (state.memory field + value) ((state.memory field).uaddOverflow value)
  | .right31 field, state => put state field (state.memory field >>> 31)
      ((state.memory field).getLsbD 30)
  | .adcZero field, state => put state field
      (state.memory field + (if state.carry then 1 else 0))
      ((state.memory field).uaddOverflow (if state.carry then 1 else 0))
  | .decrement field, state => put state field (state.memory field - 1) state.carry

@[expose] def run : List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)

@[expose] def PureRun (codeField : Nat → Prop) : List Instruction → State → Prop
  | [], _ => True
  | instruction :: rest, state =>
      codeField (destination instruction) ∧ PureRun codeField rest (execute instruction state)

@[expose] def selected (instruction : Machine32.Instruction) : Instruction :=
  .simple (.selected instruction)

@[expose] def sample (fields : Fields) (source target : Slot) : List Instruction :=
  [selected (.store (fields target) BranchAlgebra.signBit),
   selected (.exchange (fields source)), .simple (.andAcc (fields target)),
   selected (.exchange (fields source))]

/-- Twelve instructions from the printed signed normalization, with the
destination, mask and double slots instantiated separately for x and y. -/
@[expose] def normalize (fields : Fields) (source target maskSlot double : Slot) : List Instruction :=
  [selected (.exchange (fields source)), .simple (.storeAcc (fields target)),
   .simple (.storeAcc (fields double)), .simple (.shiftLeft (fields double)),
   selected (.exchange (fields source)), selected (.store (fields maskSlot) 0),
   .subtractConstant (fields target) BranchAlgebra.signBit,
   selected (.sbbZero (fields maskSlot)),
   .addConstant (fields target) BranchAlgebra.signBit,
   selected (.complement (fields maskSlot)),
   selected (.andField (fields double) (fields maskSlot)),
   .subtractFrom (fields target) (fields double)]

/-- The original quotient/remainder-dependent sign prefix. Mutable XOR/MOV
immediates are read from their actual fields. No conditional scope is repaired. -/
@[expose] def signPrefix (fields : Fields) (mod : Bool) : List Instruction :=
  sample fields .x .signX ++
    (if mod then [] else sample fields .y .signY ++
      [selected (.xorField (fields .signY) (fields .signX))]) ++
    [.right31 (fields (if mod then .signX else .signY)),
     selected (.negate (fields (if mod then .signX else .signY))),
     .simple (.copyFrom (fields .resultSign) (fields (if mod then .signX else .signY)))]

@[expose] def copy (fields : Fields) (target source : Slot) : List Instruction :=
  (MultiplyWords.copyProgram (fields target) (fields source)).map Instruction.simple

@[expose] def initializeData (fields : Fields) (mod signed : Bool) : List Instruction :=
  (if signed then
    signPrefix fields mod ++ normalize fields .x .low .xMask .xDouble ++
      normalize fields .y .divisor .yMask .yDouble ++ copy fields .divisor2 .divisor
   else copy fields .low .x ++
      [selected (.exchange (fields .y)), .simple (.storeAcc (fields .divisor)),
       .simple (.storeAcc (fields .divisor2)), selected (.exchange (fields .y))]) ++
    [selected (.store (fields .high) 0), selected (.store (fields .counter) 32),
     .simple (.selfStore (fields .counter))]

/-- The printed 23 instructions between body and backedge continuations. -/
@[expose] def body (fields : Fields) : List Instruction :=
  [selected (.exchange (fields .low)), .simple (.storeAcc (fields .oldLow)),
   .simple (.storeAcc (fields .oldLow2)), selected (.exchange (fields .low)),
   .simple (.shiftLeft (fields .low)), .simple (.shiftLeft (fields .high)),
   selected (.store (fields .quotientBit) 1),
   .subtractFrom (fields .low) (fields .oldLow), .adcZero (fields .high),
   .simple (.addFrom (fields .low) (fields .oldLow2)),
   .simple (.copyFrom (fields .restore) (fields .divisor)),
   selected (.store (fields .mask) 0),
   .subtractFrom (fields .high) (fields .divisor2),
   selected (.sbbZero (fields .mask)),
   selected (.andField (fields .restore) (fields .mask)),
   selected (.exchange (fields .mask)), .simple (.storeAcc (fields .maskComplement)),
   selected (.exchange (fields .mask)), selected (.complement (fields .maskComplement)),
   selected (.andField (fields .quotientBit) (fields .maskComplement)),
   .simple (.addFrom (fields .high) (fields .restore)),
   .simple (.addFrom (fields .low) (fields .quotientBit)),
   .decrement (fields .counter)]

@[expose] def finishData (fields : Fields) (mod signed : Bool) : List Instruction :=
  [selected (.store (fields .displacement) 0)] ++
  (if mod then [.simple (.selfStore (fields .low)),
     .simple (.copyFrom (fields .result) (fields .high))]
   else [.simple (.copyFrom (fields .result) (fields .low)),
     .simple (.selfStore (fields .high))]) ++
  (if signed then
    [selected (.exchange (fields .result)), .simple (.storeAcc (fields .outputDouble)),
     .simple (.shiftLeft (fields .outputDouble)), selected (.exchange (fields .result)),
     selected (.andField (fields .outputDouble) (fields .resultSign)),
     .subtractFrom (fields .result) (fields .outputDouble)]
   else [])

theorem every_instruction_writes (instruction : Instruction) : [destination instruction] ≠ [] := by simp

theorem execute_frame (instruction : Instruction) (state : State) (field : Nat)
    (outside : field ≠ destination instruction) :
    (execute instruction state).memory field = state.memory field := by
  cases instruction with
  | simple instruction => exact MultiplyWords.execute_frame instruction state field outside
  | _ => simp_all [execute, put, destination, write]

theorem run_frame (program : List Instruction) (state : State) (field : Nat)
    (outside : ∀ instruction ∈ program, field ≠ destination instruction) :
    (run program state).memory field = state.memory field := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (fun op member => outside op (by simp [member])),
        execute_frame _ _ _ (outside instruction (by simp))]

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem embedded_run (program : List MultiplyWords.Instruction) (state : State) :
    run (program.map Instruction.simple) state = MultiplyWords.run program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run, execute, MultiplyWords.run] using ih (MultiplyWords.execute instruction state)

theorem copy_effect (fields : Fields) (source target : Slot) (state : State)
    (separate : Separate fields) (different : target ≠ source) :
    run (copy fields target source) state =
      put state (fields target) (state.memory (fields source)) state.carry := by
  rw [copy, embedded_run]
  exact MultiplyWords.copy_effect _ _ _ (separate.ne different)

theorem pure_of_destinations (codeField : Nat → Prop) (program : List Instruction) (state : State)
    (owned : ∀ instruction ∈ program, codeField (destination instruction)) :
    PureRun codeField program state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
      exact ⟨owned instruction (by simp), ih _ (fun op member => owned op (by simp [member]))⟩

theorem body_length (fields : Fields) : (body fields).length = 23 := rfl

end SmcTuring.Appendix.DivisionWords
