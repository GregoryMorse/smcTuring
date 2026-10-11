module
public import SmcTuring.SMC.ConcreteStores

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def instructionCount : Mov.Instruction → Nat
  | .immediate _ (.offset _) => 11
  | .immediate _ (.address _) => 3
  | .load _ _ _ => 233
  | .store _ _ _ => 239

theorem instruction_count_positive (instruction : Mov.Instruction) : 0 < instructionCount instruction := by
  cases instruction with
  | immediate _ word => cases word <;> simp only [instructionCount] <;> decide
  | load _ _ _ => simp only [instructionCount]; decide
  | store _ _ _ => simp only [instructionCount]; decide

/-- Successful source MOVs compile to actual fetched executions, retaining the
complete source state and static control words. Source-register aliasing is free. -/
theorem instruction_success (instruction : Mov.Instruction) (source next : Mov.State) (s : State)
    (supported : Supported instruction) (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileInstruction instruction)) (success : Mov.execute instruction source = some next) :
    ∃ finish, CompiledInstructionSpec next s finish (instructionCount instruction) (compileInstruction instruction).length := by
  cases instruction with
  | immediate r word =>
    cases word with
    | address cell => exact False.elim supported
    | offset choice =>
      have equal : { source with registers := write source.registers r (.offset choice) } = next :=
        Option.some.inj success
      subst next
      refine ⟨immediateResult r choice s, ?_⟩
      simpa [instructionCount, compileInstruction, read_op_length] using immediate_success source r choice s ready rep site
  | load r base offset =>
    cases address : Mov.address source base offset with
    | none => simp [Mov.execute, address] at success
    | some p =>
      have equal : { source with registers := write source.registers r (source.memory p) } = next :=
        Option.some.inj (by simpa [Mov.execute, address] using success)
      subst next
      refine ⟨loadResult r base offset s, ?_⟩
      simpa [instructionCount, compileInstruction, address_program_length, read_op_length] using
        load_success source r base offset p s ready rep site address
  | store base offset srcReg =>
    cases address : Mov.address source base offset with
    | none => simp [Mov.execute, address] at success
    | some p =>
      have equal : { source with memory := write source.memory p (source.registers srcReg) } = next :=
        Option.some.inj (by simpa [Mov.execute, address] using success)
      subst next
      refine ⟨storeResult base offset srcReg s, ?_⟩
      simpa [instructionCount, compileInstruction, address_program_length, call_program_length] using
        store_success source base offset srcReg p s ready rep site address

/-- Source traps are reflected by an intended terminal transfer in a positive,
bounded number of code-writing instructions, before any invalid dereference. -/
theorem instruction_fault (instruction : Mov.Instruction) (source : Mov.State) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileInstruction instruction)) (fault : Mov.execute instruction source = none) :
    ∃ count finish, AddressFaultSpec source s finish count ∧ count ≤ instructionCount instruction := by
  cases instruction with
  | immediate r word => simp [Mov.execute] at fault
  | load r base offset =>
    have invalid : Mov.address source base offset = none := by
      cases address : Mov.address source base offset <;> simp_all [Mov.execute]
    have addressSite := ((linear_at_append image s.pc (addressProgram base offset)
      (readOp 22 (.store (.fixed (sourceRegister r))))).mp site).1
    rcases address_fault source base offset s ready rep addressSite invalid with ⟨count, finish, correct⟩
    refine ⟨count, finish, correct, ?_⟩
    have := correct.bounded
    change count ≤ 233
    omega
  | store base offset srcReg =>
    have invalid : Mov.address source base offset = none := by
      cases address : Mov.address source base offset <;> simp_all [Mov.execute]
    have addressSite := ((linear_at_append image s.pc (addressProgram base offset)
      (callProgram (.fixed (readerPC (Four.slot srcReg).val)) ++ callProgram (.fixed (readerPC 22 + 3)))).mp site).1
    rcases address_fault source base offset s ready rep addressSite invalid with ⟨count, finish, correct⟩
    refine ⟨count, finish, correct, ?_⟩
    have := correct.bounded
    change count ≤ 239
    omega

end SmcTuring.SMC.Concrete
