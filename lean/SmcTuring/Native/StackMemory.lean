module
public import SmcTuring.Native.MixedFrames
public import SmcTuring.Native.StringStack

public section
namespace SmcTuring.Native.StackMemory
@[expose] def size (mode : Mode) := (wordPrefix mode).length+6
@[expose] def form (mode : Mode) (op : MemoryOp) (pc target : Nat) : Native.Form mode :=
  .memory op (Relocation.instructionDisp mode op pc target)

theorem exchange_stack_effect (mode : Mode) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+size mode) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    Execution.execute mode (form mode .exchangeStack pc target) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+size mode)
        stack := MixedMemory.getWord mode state.memory target
        memory := ByteMemory.putWord mode state.memory target state.stack} := by
  have length : Native.instructionLength mode (.memory .exchangeStack 0) = size mode := by cases mode <;> rfl
  have hit := Relocation.instruction_memory_hits mode .exchangeStack pc target state entry (by simpa only [length] using range)
  have next := Relocation.next_pc mode state (form mode .exchangeStack pc target) pc entry
  have actual : Native.instructionLength mode (form mode .exchangeStack pc target) = size mode := by cases mode <;> rfl
  rw [actual] at next
  change Execution.executeMemory mode .exchangeStack state (Execution.nextPC mode (form mode .exchangeStack pc target) state)
    (Execution.memoryAddress mode (Execution.nextPC mode (form mode .exchangeStack pc target) state)
      (Relocation.instructionDisp mode .exchangeStack pc target)) = _
  change Execution.memoryAddress mode (Execution.nextPC mode (form mode .exchangeStack pc target) state)
    (Relocation.instructionDisp mode .exchangeStack pc target) = Arithmetic.encodeNat mode target at hit
  rw [hit,next,Execution.executeMemory,MixedMemory.load_nat mode state.memory target fits,
    Arithmetic.encode_nat_toNat mode target fits]

theorem store_acc_effect (mode : Mode) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+size mode) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    Execution.execute mode (form mode .storeAcc pc target) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+size mode)
        memory := ByteMemory.putWord mode state.memory target state.accumulator} := by
  have length : Native.instructionLength mode (.memory .storeAcc 0) = size mode := by cases mode <;> rfl
  have hit := Relocation.instruction_memory_hits mode .storeAcc pc target state entry (by simpa only [length] using range)
  have next := Relocation.next_pc mode state (form mode .storeAcc pc target) pc entry
  have actual : Native.instructionLength mode (form mode .storeAcc pc target) = size mode := by cases mode <;> rfl
  rw [actual] at next
  change Execution.executeMemory mode .storeAcc state (Execution.nextPC mode (form mode .storeAcc pc target) state)
    (Execution.memoryAddress mode (Execution.nextPC mode (form mode .storeAcc pc target) state)
      (Relocation.instructionDisp mode .storeAcc pc target)) = _
  change Execution.memoryAddress mode (Execution.nextPC mode (form mode .storeAcc pc target) state)
    (Relocation.instructionDisp mode .storeAcc pc target) = Arithmetic.encodeNat mode target at hit
  rw [hit,next,Execution.executeMemory,Execution.storeState,Arithmetic.encode_nat_toNat mode target fits]

theorem moffs_effect (mode : Mode) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc) (fits : target < 2^(8*mode.wordBytes)) :
    Execution.execute mode (.moffs (Arithmetic.encodeNat mode target)) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+Native.moffsOperandOffset mode+mode.wordBytes)
        memory := ByteMemory.putWord mode state.memory target state.accumulator} := by
  rw [Execution.execute,Relocation.next_pc mode state _ pc entry,Execution.storeState,
    Arithmetic.encode_nat_toNat mode target fits]
  have size : Native.instructionLength mode (.moffs (Arithmetic.encodeNat mode target)) =
      Native.moffsOperandOffset mode+mode.wordBytes := by cases mode <;> rfl
  rw [size,Nat.add_assoc]
end SmcTuring.Native.StackMemory
