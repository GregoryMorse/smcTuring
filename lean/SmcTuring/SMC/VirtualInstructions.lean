module
public import SmcTuring.SMC.CallContracts

public section

namespace SmcTuring.SMC.Virtual

open Dolan

/-- The immediate operation is eleven fetched SMC instructions, including the
code-backed CALLs. Its constant is supplied by a storage operand, not MOV-immediate
into the hardware accumulator. -/
theorem immediate_image_correct (layout : Layout) (wordBytes : Int) (image : Image)
    (source : Mov.State) (target : State) (r : Mov.Register) (value : Mov.Word)
    (label routine constant returnField : Int) (rep : Rep layout source target)
    (ready : ReadCallReady wordBytes image label routine constant returnField target)
    (loaded : target.memory (target.memory label) = encodeWord layout.data value)
    (outside : ¬ codeField layout.data returnField)
    (destinationCode : image.codeField (registerField layout r))
    (following : image.headers (target.pc + 3) =
      some (.store (.fixed (registerField layout r)), target.pc + 4)) :
    ∃ finish, runImage wordBytes image 11 target = some finish ∧
      Rep layout { source with registers := write source.registers r value } finish ∧
      Mov.execute (.immediate r value) source = some { source with registers := write source.registers r value } ∧
      PureSteps wordBytes image 11 target := by
  have separate := data_field_separate layout.data _ _ outside (register_is_code layout r)
  have executed := ready.copy wordBytes image label routine constant returnField (registerField layout r) target
    separate destinationCode following
  exact ⟨_, executed.1,
    read_copy_register_rep layout source target label routine returnField r value rep loaded outside,
    rfl, executed.2⟩

/-- A valid indexed address can be read through the one shared dynamic operand.
Register aliasing is unrestricted: the value is obtained before updating the
destination code word. Address calculation and the guards precede this block. -/
theorem load_image_correct (layout : Layout) (wordBytes : Int) (image : Image)
    (source : Mov.State) (target : State) (r base offset : Mov.Register) (p : Nat × Bool)
    (label routine constant returnField : Int) (rep : Rep layout source target)
    (valid : Mov.address source base offset = some p)
    (pointer : target.memory label = heapField layout.data p)
    (ready : ReadCallReady wordBytes image label routine constant returnField target)
    (outside : ¬ codeField layout.data returnField)
    (destinationCode : image.codeField (registerField layout r))
    (following : image.headers (target.pc + 3) =
      some (.store (.fixed (registerField layout r)), target.pc + 4)) :
    ∃ finish, runImage wordBytes image 11 target = some finish ∧
      Rep layout { source with registers := write source.registers r (source.memory p) } finish ∧
      Mov.execute (.load r base offset) source =
        some { source with registers := write source.registers r (source.memory p) } ∧
      PureSteps wordBytes image 11 target := by
  have loaded : target.memory (target.memory label) = encodeWord layout.data (source.memory p) := by
    rw [pointer]
    exact rep.2 p
  rcases immediate_image_correct layout wordBytes image source target r (source.memory p)
    label routine constant returnField rep ready loaded outside destinationCode following with
    ⟨finish, completed, represented, _, pure⟩
  exact ⟨finish, completed, represented, by simp [Mov.execute, valid], pure⟩

/-- Once the source value has been read, the store enters the same physical
MOFFS instruction used to restore a dynamic read. No duplicate operand exists. -/
theorem store_image_correct (layout : Layout) (wordBytes : Int) (image : Image)
    (source : Mov.State) (target : State) (base offset r : Mov.Register) (p : Nat × Bool)
    (label routine constant returnField : Int) (rep : Rep layout source target)
    (valid : Mov.address source base offset = some p)
    (pointer : target.memory label = heapField layout.data p)
    (accumulator : target.acc = encodeWord layout.data (source.registers r))
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image target.pc (stackResetProgram constant))
    (entryCall : image.headers (target.pc + 2) = some (.call (.fixed (routine + 3)), target.pc + 3))
    (top : target.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (outside : ¬ codeField layout.data returnField) (constantOutside : ¬ codeField layout.data constant)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (targetCode : image.codeField (heapField layout.data p)) :
    ∃ finish, runImage wordBytes image 7 target = some finish ∧
      Rep layout { source with memory := write source.memory p (source.registers r) } finish ∧
      Mov.execute (.store base offset r) source =
        some { source with memory := write source.memory p (source.registers r) } ∧
      PureSteps wordBytes image 7 target := by
  have targetSeparate : target.memory label ≠ returnField := by
    rw [pointer]
    exact data_field_separate layout.data _ _ outside (heap_is_code layout.data p)
  have targetConstant : target.memory label ≠ constant := by
    rw [pointer]
    exact data_field_separate layout.data _ _ constantOutside (heap_is_code layout.data p)
  have executed := store_routine_correct wordBytes image label routine constant returnField target placed entryReset
    entryCall top constantSeparate labelSeparate targetSeparate targetConstant constantCode returnCode
    (by simpa only [pointer] using targetCode)
  exact ⟨_, executed.1,
    store_invocation_rep layout source target label routine returnField p (source.registers r)
      rep pointer accumulator outside,
    by simp [Mov.execute, valid], executed.2⟩

theorem mov_address_two_tests (data : SMC.Layout) (source : Mov.State) (base offset : Mov.Register) :
    Mov.address source base offset = none ↔
      heapBase data ≤ encodeWord data (source.registers offset) ∨
      encodeWord data (source.registers base) + encodeWord data (source.registers offset) < heapBase data := by
  cases hb : source.registers base with
  | address cell =>
    cases ho : source.registers offset with
    | address other =>
      have high : heapBase data ≤ encodeWord data (.address other) :=
        (encode_word_after_heap_iff data (.address other)).mpr ⟨other, rfl⟩
      simp [Mov.address, hb, ho, high]
    | offset choice =>
      have low := heap_field_after_base data (cell, choice)
      have invalid : ¬ heapField data (cell, choice) < heapBase data := by omega
      have offLow : ¬ heapBase data ≤ encodeWord data (.offset choice) := by
        have strict := (encode_word_below_heap_iff data (.offset choice)).mpr ⟨choice, rfl⟩
        omega
      simp [Mov.address, hb, ho, indexed_address_correct, invalid, offLow]
  | offset first =>
    cases ho : source.registers offset with
    | address other =>
      have high : heapBase data ≤ encodeWord data (.address other) :=
        (encode_word_after_heap_iff data (.address other)).mpr ⟨other, rfl⟩
      simp [Mov.address, hb, ho, high]
    | offset second =>
      have low := flags_below_heap data first second
      simp [Mov.address, hb, ho, low]

end SmcTuring.SMC.Virtual
