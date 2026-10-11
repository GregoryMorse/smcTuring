module
public import SmcTuring.SMC.ConcreteInstructionTails

public section

namespace SmcTuring.SMC.Concrete

open Dolan

theorem store_invocation_static (s : State) (ready : Static s) (nonnegative : 0 ≤ s.memory pointerLabel) :
    Static (storeInvocationResult pointerLabel (readerPC 22) returnField s) := by
  have dataWritten := static_data_write s (s.memory pointerLabel) s.acc ready nonnegative
  have returnWritten := static_dynamic_write { s with memory := write s.memory (s.memory pointerLabel) s.acc }
    26 (readerPC 22 + 7) dataWritten (by decide)
  simpa only [Static, storeInvocationResult, returnField] using returnWritten

@[expose] def storeValueResult (base offset srcReg : Mov.Register) (s : State) : State :=
  readInvocationResult (readerLabel (Four.slot srcReg).val) (readerPC (Four.slot srcReg).val) returnField
    (addressResult base offset s)

@[expose] def storeResult (base offset srcReg : Mov.Register) (s : State) : State :=
  storeInvocationResult pointerLabel (readerPC 22) returnField (storeValueResult base offset srcReg s)

theorem store_success (source : Mov.State) (base offset srcReg : Mov.Register) (p : Nat × Bool) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileInstruction (.store base offset srcReg)))
    (valid : Mov.address source base offset = some p) :
    CompiledInstructionSpec { source with memory := write source.memory p (source.registers srcReg) }
      s (storeResult base offset srcReg s) 239 28 := by
  have sites := (linear_at_append image s.pc (addressProgram base offset)
    (callProgram (.fixed (readerPC (Four.slot srcReg).val)) ++ callProgram (.fixed (readerPC 22 + 3)))).mp site
  have prepared := address_success source base offset p s ready rep sites.1 valid
  let middle := addressResult base offset s
  let loaded := storeValueResult base offset srcReg s
  have tailSite : LinearAt image middle.pc
      (callProgram (.fixed (readerPC (Four.slot srcReg).val)) ++ callProgram (.fixed (readerPC 22 + 3))) := by
    rw [prepared.pc]
    simpa [address_program_length] using sites.2
  have tailSites := (linear_at_append image middle.pc (callProgram (.fixed (readerPC (Four.slot srcReg).val)))
    (callProgram (.fixed (readerPC 22 + 3)))).mp tailSite
  have valueRun := static_read_image middle (Four.slot srcReg).val prepared.static
    (by have := (Four.slot srcReg).isLt; omega) tailSites.1
  have valueExecuted : Executes 10 middle loaded := ⟨valueRun.1, valueRun.2.1⟩
  have valueStatic : Static loaded := valueRun.2.2
  have valueRep : Virtual.Rep dataLayout source loaded := read_source_frame source middle _ prepared.represented
  have valuePC : loaded.pc = middle.pc + 3 := rfl
  have pointer : loaded.memory pointerLabel = heapField dataLayout.data p := by
    change write middle.memory returnField (readerPC (Four.slot srcReg).val + 7) pointerLabel = heapField dataLayout.data p
    rw [read_write_other _ _ _ _ (by decide : pointerLabel ≠ returnField)]
    exact prepared.pointer
  have accumulator : loaded.acc = encodeWord dataLayout.data (source.registers srcReg) :=
    register_reader_value source middle srcReg prepared.static prepared.represented
  have targetNonnegative : 0 ≤ loaded.memory pointerLabel := by
    rw [pointer]
    exact data_nonnegative _ (heap_is_code dataLayout.data p)
  have storeSite : LinearAt image loaded.pc (callProgram (.fixed (readerPC 22 + 3))) := by
    rw [valuePC]
    simpa [call_program_length] using tailSites.2
  have lastExecuted : Executes 7 loaded (storeResult base offset srcReg s) := by
    apply store_routine_correct 1 image pointerLabel (readerPC 22) topField returnField loaded
    · exact reader_placement 22 (by decide)
    · exact ⟨storeSite.1, storeSite.2.1, trivial⟩
    · simpa [Int.add_assoc] using storeSite.2.2.1
    · exact static_top loaded valueStatic
    · decide
    · decide
    · rw [pointer]
      exact data_field_separate _ _ _ (metadata_outside_data 26) (heap_is_code dataLayout.data p)
    · rw [pointer]
      exact data_field_separate _ _ _ (metadata_outside_data 25) (heap_is_code dataLayout.data p)
    · exact meta_is_code 25 (by decide)
    · exact meta_is_code 26 (by decide)
    · rw [pointer]
      exact data_is_code _ (data_nonnegative _ (heap_is_code dataLayout.data p))
  refine ⟨(prepared.executed.trans valueExecuted).trans lastExecuted,
    store_invocation_static loaded valueStatic targetNonnegative,
    Virtual.store_invocation_rep dataLayout source loaded pointerLabel (readerPC 22) returnField p
      (source.registers srcReg) valueRep pointer accumulator (metadata_outside_data 26), ?_⟩
  change loaded.pc + 3 = s.pc + (28 : Int)
  rw [valuePC, prepared.pc]
  simp [Int.add_assoc]

end SmcTuring.SMC.Concrete
