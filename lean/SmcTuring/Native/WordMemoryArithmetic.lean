module
public import SmcTuring.Native.WordNegation

public section
namespace SmcTuring.Native.WordMemoryArithmetic
inductive Op where | exchange | subtract | add
  deriving DecidableEq
@[expose] def opcode : Op → MemoryOp
  | .exchange => .exchangeAcc | .subtract => .subtract | .add => .add
@[expose] def size (mode : Mode) := (wordPrefix mode).length+6
@[expose] def form (mode : Mode) (op : Op) (pc target : Nat) : Native.Form mode :=
  .memory (opcode op) (Relocation.instructionDisp mode (opcode op) pc target)
@[expose] def result {mode : Mode} (op : Op) (old acc : Word mode) : Word mode :=
  match op with | .exchange => acc | .subtract => old-acc | .add => old+acc
@[expose] def flag {mode : Mode} (op : Op) (old acc : Word mode) (carry : Bool) :=
  match op with | .exchange => carry | .subtract => Arithmetic.unsignedBorrow old acc | .add => BitVec.uaddOverflow old acc
@[expose] def accumulator {mode : Mode} (op : Op) (old acc : Word mode) : Word mode :=
  match op with | .exchange => old | _ => acc

theorem form_length (mode : Mode) (op : Op) (pc target : Nat) :
    Native.instructionLength mode (form mode op pc target) = size mode := by
  cases op <;> cases mode <;> rfl

theorem located_effect (mode : Mode) (op : Op) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+size mode) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    Execution.execute mode (form mode op pc target) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+size mode)
        accumulator := accumulator op (MixedMemory.getWord mode state.memory target) state.accumulator
        carry := flag op (MixedMemory.getWord mode state.memory target) state.accumulator state.carry
        memory := ByteMemory.putWord mode state.memory target
          (result op (MixedMemory.getWord mode state.memory target) state.accumulator)} := by
  have length : Native.instructionLength mode (.memory (opcode op) 0) = size mode := by
    cases mode <;> cases op <;> rfl
  have hit := Relocation.instruction_memory_hits mode (opcode op) pc target state entry (by simpa only [length] using range)
  have next := Relocation.next_pc mode state (form mode op pc target) pc entry
  rw [form_length] at next
  change Execution.executeMemory mode (opcode op) state (Execution.nextPC mode (form mode op pc target) state)
    (Execution.memoryAddress mode (Execution.nextPC mode (form mode op pc target) state)
      (Relocation.instructionDisp mode (opcode op) pc target)) = _
  change Execution.memoryAddress mode (Execution.nextPC mode (form mode op pc target) state)
    (Relocation.instructionDisp mode (opcode op) pc target) = Arithmetic.encodeNat mode target at hit
  rw [hit,next]
  cases op <;> simp only [opcode,Execution.executeMemory,Execution.storeState,
    MixedMemory.load_nat mode state.memory target fits,Arithmetic.encode_nat_toNat mode target fits,result,flag,accumulator]

end SmcTuring.Native.WordMemoryArithmetic
