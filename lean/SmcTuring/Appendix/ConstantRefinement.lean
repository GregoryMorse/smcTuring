module
public import SmcTuring.Appendix.ConstantByteExecution
public import SmcTuring.Appendix.ConstantWords
public import SmcTuring.Appendix.MultiplyControl
public import SmcTuring.Appendix.FieldRefinement

public section
namespace SmcTuring.Appendix.ConstantRefinement

open ConstantByteCode
abbrev State := ConstantByteExecution.State
abbrev Instruction := ConstantWords.Instruction
open FieldRefinement (address readField)
abbrev Layout := FieldRefinement.Layout
abbrev Agreement := FieldRefinement.Agreement

/-- Total compiler helper; its finite wrap is removed by the proved Legal count
    premise. Invalid word instructions are not claimed to refine x86 SHL. -/
@[expose] def countOf (count : Nat) : Count := ⟨(count - 1) % 31, Nat.mod_lt _ (by decide)⟩

theorem count_value (count : Nat) (legal : 0 < count ∧ count < 32) :
    (countOf count).val + 1 = count := by
  simp only [countOf, Nat.mod_eq_of_lt (by omega : count - 1 < 31)]
  omega

@[expose] def dependencies : Instruction -> List Nat
  | .selected op => FieldRefinement.dependencies op
  | .addFrom field source => [field, source]
  | op => [ConstantWords.destination op]

/-- This effect translation reads the ADD's current scratch field; an original
    image proof must identify it with the instruction's own immediate at +6. -/
@[expose] def translate (instruction : Instruction) (native : State) : Form :=
  match instruction with
  | .selected op => .common (.common (FieldRefinement.translate op native))
  | .storeAcc field => .common (.common (.storeAcc (address field)))
  | .shiftLeft field count =>
      if count = 1 then .common (.shiftLeft (address field))
      else .shiftImmediate (address field) (countOf count)
  | .addFrom field source => .common (.addImmediate (address field) (readField native source))

@[expose] def dataLength : Instruction -> Nat
  | .selected op => MultiplyControl.dataLength (.selected op)
  | .storeAcc _ => 5
  | .shiftLeft _ count => if count = 1 then 6 else 7
  | .addFrom _ _ => 10

theorem destination_dependency (instruction : Instruction) :
    ConstantWords.destination instruction ∈ dependencies instruction := by
  cases instruction with
  | selected instruction => exact FieldRefinement.destination_dependency instruction
  | _ => simp [dependencies, ConstantWords.destination]

theorem translate_destination (instruction : Instruction) (native : State) :
    ConstantByteExecution.destination (translate instruction native) native =
      address (ConstantWords.destination instruction) := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_destination instruction native
  | shiftLeft field count => simp only [translate]; split <;> rfl
  | _ => rfl

theorem translate_value (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field)
    (legal : ConstantWords.Legal instruction) :
    ConstantByteExecution.value (translate instruction native) native =
      (ConstantWords.execute instruction source).memory (ConstantWords.destination instruction) := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_value instruction source native accumulator carry reads
  | shiftLeft field count =>
      have counts : 0 < count ∧ count < 32 := legal
      have read := reads field (by simp [dependencies, ConstantWords.destination])
      simp only [translate]
      split
      · rename_i one
        simp [ConstantByteExecution.value, MultiplyByteExecution.value, 
          FieldRefinement.readField, ConstantWords.execute, ConstantWords.destination,
          Machine32.put, write, one] at *
        exact congrArg (fun word : Machine32.Word => word <<< 1) read
      · simp [ConstantByteExecution.value, count_value count counts, 
          FieldRefinement.readField, ConstantWords.execute, ConstantWords.destination,
          Machine32.put, write] at *
        exact congrArg (fun word : Machine32.Word => word <<< count) read
  | _ => simp_all [dependencies, translate, ConstantByteExecution.value, MultiplyByteExecution.value,
      ByteExecution.value, FieldRefinement.readField, ConstantWords.execute,
      ConstantWords.destination, Machine32.put, write]

theorem translate_accumulator (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    ConstantByteExecution.accumulator (translate instruction native) native =
      (ConstantWords.execute instruction source).accumulator := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_accumulator instruction source native accumulator reads
  | shiftLeft field count => simp only [translate]; split <;> exact accumulator
  | _ => exact accumulator

theorem translate_carry (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field)
    (legal : ConstantWords.Legal instruction) :
    ConstantByteExecution.carry (translate instruction native) native =
      (ConstantWords.execute instruction source).carry := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_carry instruction source native accumulator carry reads
  | shiftLeft field count =>
      have counts : 0 < count ∧ count < 32 := legal
      have read := reads field (by simp [dependencies, ConstantWords.destination])
      simp only [translate]
      split
      · rename_i one
        simp [ConstantByteExecution.carry, MultiplyByteExecution.carry, 
          FieldRefinement.readField, ConstantWords.execute, Machine32.put, one, BitVec.msb_eq_getLsbD_last] at *
        exact congrArg (fun word : Machine32.Word => word.getLsbD 31) read
      · simp [ConstantByteExecution.carry, count_value count counts, 
          FieldRefinement.readField, ConstantWords.execute, Machine32.put] at *
        exact congrArg (fun word : Machine32.Word => word.getLsbD (32 - count)) read
  | _ => simp_all [dependencies, translate, ConstantByteExecution.carry, MultiplyByteExecution.carry,
      ByteExecution.carry, FieldRefinement.readField,
      ConstantWords.destination, ConstantWords.execute, Machine32.put]

theorem translate_stack (instruction : Instruction) (native : State) :
    (ConstantByteExecution.execute (translate instruction native) native).stack = native.stack := by
  cases instruction with
  | selected instruction => exact FieldRefinement.translate_stack instruction native
  | shiftLeft field count => simp only [translate]; split <;> rfl
  | _ => rfl

theorem translate_length (instruction : Instruction) (native : State) :
    instructionLength (translate instruction native) = dataLength instruction := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | shiftLeft field count => simp only [translate, dataLength]; split <;> rfl
  | _ => rfl

theorem execute_pc (instruction : Instruction) (native : State) :
    (ConstantByteExecution.execute (translate instruction native) native).pc =
      BitVec.add native.pc (BitVec.ofNat 32 (dataLength instruction)) := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | shiftLeft field count => simp only [translate, dataLength]; split <;> rfl
  | _ => rfl

theorem execute_read_destination (instruction : Instruction) (native : State) :
    readField (ConstantByteExecution.execute (translate instruction native) native)
      (ConstantWords.destination instruction) = ConstantByteExecution.value (translate instruction native) native := by
  unfold FieldRefinement.readField ByteExecution.prior
  rw [←translate_destination instruction native]
  exact ConstantByteExecution.written_word _ _

theorem execute_read_frame {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (native : State) (observed : Nat)
    (writtenIn : ConstantWords.destination instruction ∈ fields) (observedIn : observed ∈ fields)
    (distinct : observed ≠ ConstantWords.destination instruction) :
    readField (ConstantByteExecution.execute (translate instruction native) native) observed = readField native observed := by
  unfold FieldRefinement.readField ByteExecution.prior
  apply ConstantByteExecution.load_frame
  intro index
  rw [translate_destination]
  exact FieldRefinement.layout_outside layout _ _ writtenIn observedIn (Ne.symm distinct) index

/-- Static finite DWORD separation and initial agreement suffice. The actual
byte store gives every represented new word; no result or branch is assumed. -/
theorem simulate {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ field ∈ dependencies instruction, field ∈ fields)
    (legal : ConstantWords.Legal instruction) :
    Agreement fields (ConstantWords.execute instruction source)
      (ConstantByteExecution.execute (translate instruction native) native) := by
  have reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field :=
    fun field member => agreement.words field (included field member)
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstantByteExecution.execute_accumulator]
    exact translate_accumulator _ _ _ agreement.accumulator reads
  · rw [ConstantByteExecution.execute_carry]
    exact translate_carry _ _ _ agreement.accumulator agreement.carry reads legal
  · intro field member
    by_cases equal : field = ConstantWords.destination instruction
    · subst field
      rw [execute_read_destination]
      exact translate_value _ _ _ agreement.accumulator agreement.carry reads legal
    · rw [execute_read_frame layout instruction native field
        (included _ (destination_dependency instruction)) member equal,
        ConstantWords.execute_frame instruction source field equal]
      exact agreement.words field member

@[expose] def run : List Instruction → State → State
  | [], native => native
  | instruction :: rest, native => run rest (ConstantByteExecution.execute (translate instruction native) native)

@[expose] def forms : List Instruction → State → List Form
  | [], _ => []
  | instruction :: rest, native => translate instruction native ::
      forms rest (ConstantByteExecution.execute (translate instruction native) native)

theorem forms_length (program : List Instruction) (native : State) :
    (forms program native).length = program.length := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, List.length_cons, ih]

theorem forms_run (program : List Instruction) (native : State) :
    ConstantByteExecution.run (forms program native) native = run program native := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, ConstantByteExecution.run, run, ih]

theorem simulate_run {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ instruction ∈ program, ∀ field ∈ dependencies instruction, field ∈ fields)
    (legal : ∀ instruction ∈ program, ConstantWords.Legal instruction) :
    Agreement fields (ConstantWords.run program source) (run program native) := by
  induction program generalizing source native with
  | nil => exact agreement
  | cons instruction rest ih =>
    exact ih _ _ (simulate layout instruction source native agreement (included instruction (by simp)) (legal instruction (by simp)))
      (fun next member => included next (by simp [member])) (fun next member => legal next (by simp [member]))

theorem run_stack (program : List Instruction) (native : State) :
    (run program native).stack = native.stack := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => rw [run, ih, translate_stack]

theorem run_frame (program : List Instruction) (native : State) (position : Nat)
    (outside : ∀ instruction ∈ program,
      ¬Native.ByteMemory.Inside (address (ConstantWords.destination instruction)).toNat 4 position) :
    (run program native).memory position = native.memory position := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih =>
      rw [run, ih _ (fun op member => outside op (by simp [member]))]
      apply ConstantByteExecution.execute_frame
      rw [translate_destination]
      exact outside instruction (by simp)

theorem owned_run (owned : Word → Prop) (program : List Instruction) (native : State)
    (ownership : ∀ instruction ∈ program, owned (address (ConstantWords.destination instruction))) :
    ConstantByteExecution.OwnedRun owned (forms program native) native := by
  induction program generalizing native with
  | nil => trivial
  | cons instruction rest ih =>
      refine ⟨?_, ih _ (fun op member => ownership op (by simp [member]))⟩
      rw [translate_destination]
      exact ownership instruction (by simp)

end SmcTuring.Appendix.ConstantRefinement
