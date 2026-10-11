module
public import SmcTuring.SMC.ConcreteAddress

public section

namespace SmcTuring.SMC.Concrete

open Dolan

theorem source_register_nonnegative (r : Mov.Register) : 0 ≤ sourceRegister r := by
  simp only [sourceRegister]
  omega

theorem source_register_code (r : Mov.Register) : image.codeField (sourceRegister r) :=
  data_is_code _ (source_register_nonnegative r)

theorem read_op_data_static (reader : Nat) (operation : Operation) (s : State)
    (ready : Static s) (nonnegative : 0 ≤ operation.field) : Static (readOpResult reader operation s) := by
  apply read_op_static_frame reader operation s ready
  intro index _ equal
  simp only [metaField] at equal
  omega

theorem immediate_loaded (value : Bool) (s : State) (ready : Static s) :
    s.memory (s.memory (readerLabel (if value then 20 else 19))) = encodeWord dataLayout.data (.offset value) := by
  cases value
  · have pointer := static_reader_label s 19 ready (by decide)
    have datum := ready 36 (by decide)
    simpa [metadataValue, offsetZeroField, encodeWord, dataLayout, readerLabel] using
      show s.memory (s.memory (readerLabel 19)) = metadataValue 36 from by
        rw [pointer]
        simpa [metadataValue, offsetZeroField] using datum
  · have pointer := static_reader_label s 20 ready (by decide)
    have datum := ready 37 (by decide)
    simpa [metadataValue, offsetOneField, encodeWord, dataLayout, readerLabel] using
      show s.memory (s.memory (readerLabel 20)) = metadataValue 37 from by
        rw [pointer]
        simpa [metadataValue, offsetOneField] using datum

theorem read_op_assign_register_rep (source : Mov.State) (s : State) (reader : Nat) (r : Mov.Register) (word : Mov.Word)
    (rep : Virtual.Rep dataLayout source s)
    (loaded : s.memory (s.memory (readerLabel reader)) = encodeWord dataLayout.data word) :
    Virtual.Rep dataLayout { source with registers := write source.registers r word }
      (readOpResult reader (.assign (sourceRegister r)) s) := by
  have updated := Virtual.register_write_rep dataLayout source
    (readInvocationResult (readerLabel reader) (readerPC reader) returnField s) r word
    (read_source_frame source s reader rep)
  simpa [Virtual.Rep, readOpResult, Operation.header, decode, Address.eval, execute, readInvocationResult,
    source_register_field, loaded] using updated

theorem read_op_dynamic_correct (s : State) (reader : Nat) (operation : Operation) (ready : Static s) (bounded : reader < 23)
    (site : LinearAt image s.pc (readOp reader operation.header)) (code : image.codeField operation.field)
    (targetCode : image.codeField (s.memory (readerLabel reader)))
    (targetSeparate : s.memory (readerLabel reader) ≠ returnField) : Executes 11 s (readOpResult reader operation s) := by
  have caller : LinearAt image s.pc (callProgram (.fixed (readerPC reader))) :=
    ⟨site.1, site.2.1, site.2.2.1, trivial⟩
  have readyCall := call_ready s reader ready bounded caller targetCode targetSeparate
  have following : image.headers (s.pc + 3) = some (operation.header, s.pc + 4) := by
    simpa [Int.add_assoc] using site.2.2.2.1
  exact read_then_instruction 1 image (readerLabel reader) (readerPC reader) topField returnField s
    readyCall.placed readyCall.entryReset readyCall.entryCall readyCall.top readyCall.constantSeparate
    readyCall.labelSeparate readyCall.targetSeparate readyCall.constantCode readyCall.returnCode readyCall.labelCode
    readyCall.targetCode operation.header (s.pc + 4) following (operation_writes operation _ code)

structure CompiledInstructionSpec (next : Mov.State) (start finish : State) (count width : Nat) : Prop where
  executed : Executes count start finish
  static : Static finish
  represented : Virtual.Rep dataLayout next finish
  pc : finish.pc = start.pc + (width : Int)

@[expose] def immediateResult (r : Mov.Register) (value : Bool) (s : State) : State :=
  readOpResult (if value then 20 else 19) (.assign (sourceRegister r)) s

theorem immediate_success (source : Mov.State) (r : Mov.Register) (value : Bool) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileInstruction (.immediate r (.offset value)))) :
    CompiledInstructionSpec { source with registers := write source.registers r (.offset value) }
      s (immediateResult r value s) 11 4 := by
  have executed := read_op_correct s (if value then 20 else 19) (.assign (sourceRegister r)) ready
    (by cases value <;> decide) site (source_register_code r)
  exact ⟨executed, read_op_data_static _ _ s ready (source_register_nonnegative r),
    read_op_assign_register_rep source s _ r (.offset value) rep (immediate_loaded value s ready), read_op_pc _ _ s⟩

@[expose] def loadResult (r base offset : Mov.Register) (s : State) : State :=
  readOpResult 22 (.assign (sourceRegister r)) (addressResult base offset s)

theorem load_success (source : Mov.State) (r base offset : Mov.Register) (p : Nat × Bool) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileInstruction (.load r base offset)))
    (valid : Mov.address source base offset = some p) :
    CompiledInstructionSpec { source with registers := write source.registers r (source.memory p) }
      s (loadResult r base offset s) 233 26 := by
  have sites := (linear_at_append image s.pc (addressProgram base offset)
    (readOp 22 (.store (.fixed (sourceRegister r))))).mp site
  have prepared := address_success source base offset p s ready rep sites.1 valid
  let middle := addressResult base offset s
  have tailSite : LinearAt image middle.pc (readOp 22 (.store (.fixed (sourceRegister r)))) := by
    rw [prepared.pc]
    simpa [address_program_length] using sites.2
  have targetCode : image.codeField (middle.memory (readerLabel 22)) := by
    change image.codeField ((addressResult base offset s).memory pointerLabel)
    rw [prepared.pointer]
    apply data_is_code
    have afterBase := heap_field_after_base dataLayout.data p
    have base : heapBase dataLayout.data = 13 := rfl
    omega
  have targetSeparate : middle.memory (readerLabel 22) ≠ returnField := by
    change (addressResult base offset s).memory pointerLabel ≠ returnField
    rw [prepared.pointer]
    exact data_field_separate _ _ _ (metadata_outside_data 26) (heap_is_code dataLayout.data p)
  have loaded : middle.memory (middle.memory (readerLabel 22)) = encodeWord dataLayout.data (source.memory p) := by
    change (addressResult base offset s).memory ((addressResult base offset s).memory pointerLabel) =
      encodeWord dataLayout.data (source.memory p)
    rw [prepared.pointer]
    exact prepared.represented.2 p
  have tailExecuted := read_op_dynamic_correct middle 22 (.assign (sourceRegister r)) prepared.static (by decide)
    tailSite (source_register_code r) targetCode targetSeparate
  refine ⟨prepared.executed.trans tailExecuted,
    read_op_data_static _ _ middle prepared.static (source_register_nonnegative r),
    read_op_assign_register_rep source middle 22 r (source.memory p) prepared.represented loaded, ?_⟩
  simp [loadResult, read_op_pc, prepared.pc, Int.add_assoc]

end SmcTuring.SMC.Concrete
