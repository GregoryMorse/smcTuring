module
public import SmcTuring.Appendix.MultiplyByteExecution
public import SmcTuring.Appendix.MultiplyControl
public import SmcTuring.Appendix.FieldRefinement

public section
namespace SmcTuring.Appendix.MultiplyRefinement

open MultiplyByteCode
abbrev State := MultiplyByteExecution.State
abbrev Instruction := MultiplyWords.Instruction
open FieldRefinement (address readField)
abbrev Layout := FieldRefinement.Layout
abbrev Agreement := FieldRefinement.Agreement

@[expose] def dependencies : Instruction → List Nat
  | .selected instruction => FieldRefinement.dependencies instruction
  | .copyFrom field source | .addFrom field source => [field, source]
  | instruction => [MultiplyWords.destination instruction]

/-- Effect translation reads mutable operands from the current byte state.
The literal image proof must identify these reads with each own immediate. -/
@[expose] def translate (instruction : Instruction) (native : State) : Form :=
  match instruction with
  | .selected instruction => .common (FieldRefinement.translate instruction native)
  | .storeAcc field => .common (.storeAcc (address field))
  | .andAcc field => .andAcc (address field)
  | .selfStore field => .common (.immediate .store (address field) (readField native field))
  | .copyFrom field source => .common (.immediate .store (address field) (readField native source))
  | .addFrom field source => .addImmediate (address field) (readField native source)
  | .shiftLeft field => .shiftLeft (address field)
  | .shiftRight field => .shiftRight (address field)

theorem destination_dependency (instruction : Instruction) :
    MultiplyWords.destination instruction ∈ dependencies instruction := by
  cases instruction with
  | selected instruction => exact FieldRefinement.destination_dependency instruction
  | _ => simp [dependencies, MultiplyWords.destination]

theorem translate_destination (instruction : Instruction) (native : State) :
    MultiplyByteExecution.destination (translate instruction native) native =
      address (MultiplyWords.destination instruction) := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_destination instruction native
  | _ => rfl

theorem translate_value (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    MultiplyByteExecution.value (translate instruction native) native =
      (MultiplyWords.execute instruction source).memory (MultiplyWords.destination instruction) := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_value instruction source native accumulator carry reads
  | _ => simp_all [dependencies, translate, MultiplyByteExecution.value, ByteExecution.value,
      MultiplyByteExecution.prior, FieldRefinement.readField, MultiplyWords.execute,
      MultiplyWords.destination, Machine32.put, write]

theorem translate_accumulator (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    MultiplyByteExecution.accumulator (translate instruction native) native =
      (MultiplyWords.execute instruction source).accumulator := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_accumulator instruction source native accumulator reads
  | _ => exact accumulator

theorem translate_carry (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    MultiplyByteExecution.carry (translate instruction native) native =
      (MultiplyWords.execute instruction source).carry := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_carry instruction source native accumulator carry reads
  | _ => simp_all [dependencies, translate, MultiplyByteExecution.carry, ByteExecution.carry,
      MultiplyByteExecution.prior, FieldRefinement.readField, MultiplyWords.destination, MultiplyWords.execute, Machine32.put]

theorem translate_stack (instruction : Instruction) (native : State) :
    (MultiplyByteExecution.execute (translate instruction native) native).stack = native.stack := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_stack instruction native
  | _ => rfl

theorem translate_length (instruction : Instruction) (native : State) :
    instructionLength (translate instruction native) = MultiplyControl.dataLength instruction := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | _ => rfl

theorem execute_pc (instruction : Instruction) (native : State) :
    (MultiplyByteExecution.execute (translate instruction native) native).pc =
      BitVec.add native.pc (BitVec.ofNat 32 (MultiplyControl.dataLength instruction)) := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | _ => rfl

theorem execute_read_destination (instruction : Instruction) (native : State) :
    readField (MultiplyByteExecution.execute (translate instruction native) native)
      (MultiplyWords.destination instruction) = MultiplyByteExecution.value (translate instruction native) native := by
  unfold FieldRefinement.readField ByteExecution.prior
  rw [←translate_destination instruction native]
  exact MultiplyByteExecution.written_word _ _

theorem execute_read_frame {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (native : State) (observed : Nat)
    (writtenIn : MultiplyWords.destination instruction ∈ fields) (observedIn : observed ∈ fields)
    (distinct : observed ≠ MultiplyWords.destination instruction) :
    readField (MultiplyByteExecution.execute (translate instruction native) native) observed = readField native observed := by
  unfold FieldRefinement.readField ByteExecution.prior
  apply MultiplyByteExecution.load_frame
  intro index
  rw [translate_destination]
  exact FieldRefinement.layout_outside layout _ _ writtenIn observedIn (Ne.symm distinct) index

/-- Static finite DWORD separation and initial agreement suffice. The actual
byte store gives every represented new word; no result or branch is assumed. -/
theorem simulate {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (MultiplyWords.execute instruction source)
      (MultiplyByteExecution.execute (translate instruction native) native) := by
  have reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field :=
    fun field member => agreement.words field (included field member)
  refine ⟨?_, ?_, ?_⟩
  · rw [MultiplyByteExecution.execute_accumulator]
    exact translate_accumulator _ _ _ agreement.accumulator reads
  · rw [MultiplyByteExecution.execute_carry]
    exact translate_carry _ _ _ agreement.accumulator agreement.carry reads
  · intro field member
    by_cases equal : field = MultiplyWords.destination instruction
    · subst field
      rw [execute_read_destination]
      exact translate_value _ _ _ agreement.accumulator agreement.carry reads
    · rw [execute_read_frame layout instruction native field
        (included _ (destination_dependency instruction)) member equal,
        MultiplyWords.execute_frame instruction source field equal]
      exact agreement.words field member

@[expose] def run : List Instruction → State → State
  | [], native => native
  | instruction :: rest, native => run rest (MultiplyByteExecution.execute (translate instruction native) native)

@[expose] def forms : List Instruction → State → List Form
  | [], _ => []
  | instruction :: rest, native => translate instruction native ::
      forms rest (MultiplyByteExecution.execute (translate instruction native) native)

theorem forms_length (program : List Instruction) (native : State) :
    (forms program native).length = program.length := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, List.length_cons, ih]

theorem forms_run (program : List Instruction) (native : State) :
    MultiplyByteExecution.run (forms program native) native = run program native := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, MultiplyByteExecution.run, run, ih]

theorem simulate_run {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ instruction ∈ program, ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (MultiplyWords.run program source) (run program native) := by
  induction program generalizing source native with
  | nil => exact agreement
  | cons instruction rest ih =>
    exact ih _ _ (simulate layout instruction source native agreement (included instruction (by simp)))
      (fun next member => included next (by simp [member]))

theorem run_stack (program : List Instruction) (native : State) :
    (run program native).stack = native.stack := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => rw [run, ih, translate_stack]

theorem run_frame (program : List Instruction) (native : State) (position : Nat)
    (outside : ∀ instruction ∈ program,
      ¬Native.ByteMemory.Inside (address (MultiplyWords.destination instruction)).toNat 4 position) :
    (run program native).memory position = native.memory position := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (fun op member => outside op (by simp [member]))]
      apply MultiplyByteExecution.execute_frame
      rw [translate_destination]
      exact outside instruction (by simp)

theorem owned_run (owned : Word → Prop) (program : List Instruction) (native : State)
    (ownership : ∀ instruction ∈ program, owned (address (MultiplyWords.destination instruction))) :
    MultiplyByteExecution.OwnedRun owned (forms program native) native := by
  induction program generalizing native with
  | nil => trivial
  | cons instruction rest ih =>
      refine ⟨?_, ih _ (fun op member => ownership op (by simp [member]))⟩
      rw [translate_destination]
      exact ownership instruction (by simp)

end SmcTuring.Appendix.MultiplyRefinement
