module
public import SmcTuring.Appendix.InputOperand
public import SmcTuring.Native.DwordImage

public section
namespace SmcTuring.Appendix.InputDword
open Native Native.DwordCode Native.DwordLayout Native.DwordEffects

theorem current_source_word (memory : ByteMemory.Memory) (pc : Nat)
    (address symbol : BitVec 32)
    (current : ByteMemory.bytesAt memory pc 10 = InputOperand.sourceBytes address symbol) :
    get memory (pc+6) = symbol := by
  exact Option.some.inj ((read_total memory (pc+6)).symm.trans
    (InputOperand.current_source memory pc address symbol current))

/-- The minimally corrected M13 source produces the complete live target
packet in both modes. Every helper form is decoded at its actual current PC;
long-mode DWORD exchanges restore low AX and zero-extend RAX. -/
theorem copy_correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : DwordImage.Intact mode layout state.memory)
    (sourcePC targetPC : Nat) (sourceField : layout.source = sourcePC+6)
    (targetField : layout.destination = targetPC+3) (address symbol old : BitVec 32)
    (currentSource : ByteMemory.bytesAt state.memory sourcePC 10 = InputOperand.sourceBytes address symbol)
    (currentTarget : ByteMemory.bytesAt state.memory targetPC 7 = InputOperand.targetBytes old) :
    DwordCode.Trace mode state (program mode layout) (finish mode layout state) ∧
    (finish mode layout state).memory = put state.memory (targetPC+3) symbol ∧
    ByteMemory.bytesAt (finish mode layout state).memory targetPC 7 = InputOperand.targetBytes symbol ∧
    InputOperand.targetDecode (ByteMemory.bytesAt (finish mode layout state).memory targetPC 7) = some symbol ∧
    (finish mode layout state).accumulator = lift mode (low mode state.accumulator) ∧
    (finish mode layout state).stack = state.stack ∧
    (finish mode layout state).carry = state.carry ∧
    DwordImage.Intact mode layout (finish mode layout state).memory := by
  have loaded : get state.memory layout.source = symbol := by
    rw [sourceField]
    exact current_source_word state.memory sourcePC address symbol currentSource
  have memory : (finish mode layout state).memory = put state.memory (targetPC+3) symbol := by
    rw [effect mode layout valid state entry,loaded,targetField]
  have packet : ByteMemory.bytesAt (finish mode layout state).memory targetPC 7 = InputOperand.targetBytes symbol := by
    rw [memory,put_word]
    exact InputOperand.patched_target state.memory targetPC old symbol currentTarget
  have contract := registers mode layout valid state entry
  exact ⟨DwordImage.trace mode layout valid state entry intact,memory,packet,
    by rw [packet,InputOperand.target_roundtrip],contract.1,contract.2.1,contract.2.2,
    DwordImage.finish_intact mode layout valid state entry intact⟩

theorem copy_pure (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (sourcePC targetPC : Nat) (sourceField : layout.source = sourcePC+6)
    (targetField : layout.destination = targetPC+3) :
    OwnedRun mode (fun field => field = sourcePC+6 ∨ field = targetPC+3) (program mode layout) state := by
  apply DwordImage.supported_run mode layout valid state entry
  · exact Or.inl sourceField
  · exact Or.inr targetField

theorem source_code_frame (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (sourcePC targetPC : Nat) (targetField : layout.destination = targetPC+3)
    (apart : targetPC+7 ≤ sourcePC ∨ sourcePC+10 ≤ targetPC) :
    ByteMemory.bytesAt (finish mode layout state).memory sourcePC 10 = ByteMemory.bytesAt state.memory sourcePC 10 := by
  rw [effect mode layout valid state entry,targetField]
  unfold put
  apply ByteMemory.bytes_at_frame
  intro index
  have small := index.isLt
  simp only [Native.LittleEndian.word_encode_length,ByteMemory.Inside]
  omega

end SmcTuring.Appendix.InputDword
