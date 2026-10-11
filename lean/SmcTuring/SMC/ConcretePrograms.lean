module
public import SmcTuring.SMC.ConcreteCompiler

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def programCount : List Mov.Instruction → Nat
  | [] => 0
  | instruction :: rest => instructionCount instruction + programCount rest

theorem compile_program_cons (instruction : Mov.Instruction) (rest : List Mov.Instruction) :
    compileProgram (instruction :: rest) = compileInstruction instruction ++ compileProgram rest := rfl

/-- Successful complete source programs execute through the fixed constructed
image whenever their compiled snippet is placed there. Counts add, with every
instruction writing code and every boundary retaining the source representation. -/
theorem program_success (program : List Mov.Instruction) (source next : Mov.State) (s : State)
    (supported : ∀ instruction ∈ program, Supported instruction)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileProgram program)) (success : Mov.run program source = some next) :
    ∃ finish, CompiledInstructionSpec next s finish (programCount program) (compileProgram program).length := by
  induction program generalizing source next s with
  | nil =>
    simp only [Mov.run, Option.some.injEq] at success
    subst next
    exact ⟨s, ⟨rfl, trivial⟩, ready, rep, by simp [compileProgram]⟩
  | cons instruction rest ih =>
    have parts := (linear_at_append image s.pc (compileInstruction instruction) (compileProgram rest)).mp
      (by simpa only [compile_program_cons] using site)
    have headSupported := supported instruction (by simp)
    have tailSupported : ∀ i ∈ rest, Supported i := fun i member => supported i (by simp [member])
    cases first : Mov.execute instruction source with
    | none => simp [Mov.run, first] at success
    | some intermediate =>
      have last : Mov.run rest intermediate = some next := by simpa [Mov.run, first] using success
      rcases instruction_success instruction source intermediate s headSupported ready rep parts.1 first with ⟨middle, head⟩
      have tailSite : LinearAt image middle.pc (compileProgram rest) := by rw [head.pc]; exact parts.2
      rcases ih intermediate next middle tailSupported head.static head.represented tailSite last with ⟨finish, tail⟩
      refine ⟨finish, head.executed.trans tail.executed, tail.static, tail.represented, ?_⟩
      rw [tail.pc, head.pc]
      simp [compile_program_cons, Int.add_assoc]

structure ProgramFaultSpec (start finish : State) (count bound : Nat) : Prop where
  positive : 0 < count
  bounded : count ≤ bound
  executed : Executes count start finish
  static : Static finish
  terminal : finish.pc = terminalPC

/-- Every source failure is reflected by an intended terminal transfer within
the successful-prefix count plus the failing instruction's bound. -/
theorem program_fault (program : List Mov.Instruction) (source : Mov.State) (s : State)
    (supported : ∀ instruction ∈ program, Supported instruction)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (compileProgram program)) (fault : Mov.run program source = none) :
    ∃ count finish, ProgramFaultSpec s finish count (programCount program) := by
  induction program generalizing source s with
  | nil => simp [Mov.run] at fault
  | cons instruction rest ih =>
    have parts := (linear_at_append image s.pc (compileInstruction instruction) (compileProgram rest)).mp
      (by simpa only [compile_program_cons] using site)
    have headSupported := supported instruction (by simp)
    have tailSupported : ∀ i ∈ rest, Supported i := fun i member => supported i (by simp [member])
    cases first : Mov.execute instruction source with
    | none =>
      rcases instruction_fault instruction source s ready rep parts.1 first with ⟨count, finish, head, bound⟩
      refine ⟨count, finish, head.positive, ?_, head.executed, head.static, head.terminal⟩
      simp only [programCount]
      omega
    | some intermediate =>
      have last : Mov.run rest intermediate = none := by simpa [Mov.run, first] using fault
      rcases instruction_success instruction source intermediate s headSupported ready rep parts.1 first with ⟨middle, head⟩
      have tailSite : LinearAt image middle.pc (compileProgram rest) := by rw [head.pc]; exact parts.2
      rcases ih intermediate middle tailSupported head.static head.represented tailSite last with ⟨count, finish, tail⟩
      refine ⟨instructionCount instruction + count, finish, ?_, ?_, head.executed.trans tail.executed,
        tail.static, tail.terminal⟩
      · have := tail.positive
        omega
      · have := tail.bounded
        simp only [programCount]
        omega

end SmcTuring.SMC.Concrete
