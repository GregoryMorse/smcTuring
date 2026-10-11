module
public import SmcTuring.Appendix.DivisionByteExecution
public import SmcTuring.Appendix.MultiplyRefinement
public import SmcTuring.Appendix.DivisionControl
public import SmcTuring.Appendix.FieldRefinement

public section
namespace SmcTuring.Appendix.DivisionRefinement

open DivisionByteCode
abbrev State := DivisionByteExecution.State
abbrev Instruction := DivisionWords.Instruction
open FieldRefinement (address readField)
abbrev Layout := FieldRefinement.Layout
abbrev Agreement := FieldRefinement.Agreement

@[expose] def dependencies : Instruction → List Nat
  | .simple instruction => MultiplyRefinement.dependencies instruction
  | .subtractFrom field source => [field, source]
  | instruction => [DivisionWords.destination instruction]

/-- Reads in an effect translation are from current bytes. The subsequent
literal image proof identifies each dynamic value with its own immediate. -/
@[expose] def translate (instruction : Instruction) (native : State) : Form :=
  match instruction with
  | .simple instruction => .common (MultiplyRefinement.translate instruction native)
  | .subtractFrom field source => .subtractImmediate (address field) (readField native source)
  | .subtractConstant field value => .subtractImmediate (address field) value
  | .addConstant field value => .common (.addImmediate (address field) value)
  | .right31 field => .right31 (address field)
  | .adcZero field => .adcZero (address field)
  | .decrement field => .decrement (address field)

theorem destination_dependency (instruction : Instruction) :
    DivisionWords.destination instruction ∈ dependencies instruction := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.destination_dependency instruction
  | _ => simp [dependencies, DivisionWords.destination]

theorem translate_destination (instruction : Instruction) (native : State) :
    DivisionByteExecution.destination (translate instruction native) native =
      address (DivisionWords.destination instruction) := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_destination instruction native
  | _ => rfl

theorem translate_value (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    DivisionByteExecution.value (translate instruction native) native =
      (DivisionWords.execute instruction source).memory (DivisionWords.destination instruction) := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_value instruction source native accumulator carry reads
  | _ => simp_all [dependencies, translate, DivisionByteExecution.value, MultiplyByteExecution.value,
      DivisionByteExecution.prior, MultiplyByteExecution.prior, ByteExecution.prior, FieldRefinement.readField, DivisionWords.execute,
      DivisionWords.destination, Machine32.put, write]

theorem translate_accumulator (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    DivisionByteExecution.accumulator (translate instruction native) native =
      (DivisionWords.execute instruction source).accumulator := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_accumulator instruction source native accumulator reads
  | _ => exact accumulator

theorem translate_carry (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    DivisionByteExecution.carry (translate instruction native) native =
      (DivisionWords.execute instruction source).carry := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_carry instruction source native accumulator carry reads
  | _ => simp_all [dependencies, translate, DivisionByteExecution.carry, MultiplyByteExecution.carry,
      DivisionByteExecution.prior, MultiplyByteExecution.prior, ByteExecution.prior, FieldRefinement.readField, DivisionWords.destination, DivisionWords.execute, Machine32.put]

theorem translate_stack (instruction : Instruction) (native : State) :
    (DivisionByteExecution.execute (translate instruction native) native).stack = native.stack := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_stack instruction native
  | _ => rfl

theorem translate_length (instruction : Instruction) (native : State) :
    instructionLength (translate instruction native) = DivisionControl.dataLength instruction := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.translate_length instruction native
  | _ => rfl

theorem execute_pc (instruction : Instruction) (native : State) :
    (DivisionByteExecution.execute (translate instruction native) native).pc =
      BitVec.add native.pc (BitVec.ofNat 32 (DivisionControl.dataLength instruction)) := by
  cases instruction with
  | simple instruction => exact MultiplyRefinement.execute_pc instruction native
  | _ => rfl

theorem execute_read_destination (instruction : Instruction) (native : State) :
    readField (DivisionByteExecution.execute (translate instruction native) native)
      (DivisionWords.destination instruction) = DivisionByteExecution.value (translate instruction native) native := by
  unfold FieldRefinement.readField ByteExecution.prior
  rw [←translate_destination instruction native]
  exact DivisionByteExecution.written_word _ _

theorem execute_read_frame {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (native : State) (observed : Nat)
    (writtenIn : DivisionWords.destination instruction ∈ fields) (observedIn : observed ∈ fields)
    (distinct : observed ≠ DivisionWords.destination instruction) :
    readField (DivisionByteExecution.execute (translate instruction native) native) observed = readField native observed := by
  unfold FieldRefinement.readField ByteExecution.prior
  apply DivisionByteExecution.load_frame
  intro index
  rw [translate_destination]
  exact FieldRefinement.layout_outside layout _ _ writtenIn observedIn (Ne.symm distinct) index

/-- Static finite DWORD separation and initial agreement suffice. The actual
byte store gives every represented new word; no result or branch is assumed. -/
theorem simulate {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (DivisionWords.execute instruction source)
      (DivisionByteExecution.execute (translate instruction native) native) := by
  have reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field :=
    fun field member => agreement.words field (included field member)
  refine ⟨?_, ?_, ?_⟩
  · rw [DivisionByteExecution.execute_accumulator]
    exact translate_accumulator _ _ _ agreement.accumulator reads
  · rw [DivisionByteExecution.execute_carry]
    exact translate_carry _ _ _ agreement.accumulator agreement.carry reads
  · intro field member
    by_cases equal : field = DivisionWords.destination instruction
    · subst field
      rw [execute_read_destination]
      exact translate_value _ _ _ agreement.accumulator agreement.carry reads
    · rw [execute_read_frame layout instruction native field
        (included _ (destination_dependency instruction)) member equal,
        DivisionWords.execute_frame instruction source field equal]
      exact agreement.words field member

@[expose] def run : List Instruction → State → State
  | [], native => native
  | instruction :: rest, native => run rest (DivisionByteExecution.execute (translate instruction native) native)

@[expose] def forms : List Instruction → State → List Form
  | [], _ => []
  | instruction :: rest, native => translate instruction native ::
      forms rest (DivisionByteExecution.execute (translate instruction native) native)

theorem forms_length (program : List Instruction) (native : State) :
    (forms program native).length = program.length := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, List.length_cons, ih]

theorem forms_run (program : List Instruction) (native : State) :
    DivisionByteExecution.run (forms program native) native = run program native := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, DivisionByteExecution.run, run, ih]

theorem simulate_run {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ instruction ∈ program, ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (DivisionWords.run program source) (run program native) := by
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
      ¬Native.ByteMemory.Inside (address (DivisionWords.destination instruction)).toNat 4 position) :
    (run program native).memory position = native.memory position := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (fun op member => outside op (by simp [member]))]
      apply DivisionByteExecution.execute_frame
      rw [translate_destination]
      exact outside instruction (by simp)

theorem owned_run (owned : Word → Prop) (program : List Instruction) (native : State)
    (ownership : ∀ instruction ∈ program, owned (address (DivisionWords.destination instruction))) :
    DivisionByteExecution.OwnedRun owned (forms program native) native := by
  induction program generalizing native with
  | nil => trivial
  | cons instruction rest ih =>
      refine ⟨?_, ih _ (fun op member => ownership op (by simp [member]))⟩
      rw [translate_destination]
      exact ownership instruction (by simp)

end SmcTuring.Appendix.DivisionRefinement
