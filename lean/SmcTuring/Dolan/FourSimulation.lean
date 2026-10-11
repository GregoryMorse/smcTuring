module
public import SmcTuring.Dolan.FourCompile

public section

namespace SmcTuring.Dolan.Four

@[expose] def repeatRun (program : List Instruction) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (run program s).bind (repeatRun program n)

@[expose] def LoopHalts (program : List Instruction) (s : State) : Prop :=
  ∃ n finish, repeatRun program n s = some finish ∧ run program finish = none

@[expose] def LoopDiverges (program : List Instruction) (s : State) : Prop :=
  ∀ n, ∃ finish, repeatRun program n s = some finish

/-- Each completed source body corresponds to one completed compiled body.
Thus the source and target have the same explicit unconditional backedge. -/
theorem repeat_compiles (program : List Mov.Instruction) (n : Nat) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) :
    match Mov.repeatRun program n source with
    | none => repeatRun (compile program) n target = none
    | some next => ∃ finish, repeatRun (compile program) n target = some finish ∧ Coherent next finish ⟨0, by decide⟩ := by
  induction n generalizing source target with
  | zero => exact ⟨target, rfl, rep⟩
  | succ n ih =>
    cases first : Mov.run program source with
    | none =>
      have stopped := (compile_fault_iff program source target rep).2 first
      simp [Mov.repeatRun, repeatRun, first, stopped]
    | some middle =>
      rcases compile_success program source middle target rep first with ⟨physical, completed, represented⟩
      have tail := ih middle physical represented
      cases rest : Mov.repeatRun program n middle with
      | none => simpa [Mov.repeatRun, repeatRun, first, completed, rest] using tail
      | some next =>
        simp only [rest] at tail
        rcases tail with ⟨finish, tailRun, finishRep⟩
        simp only [Mov.repeatRun, first, Option.bind_some, rest]
        refine ⟨finish, ?_, finishRep⟩
        simpa [Mov.repeatRun, repeatRun, first, completed, rest] using tailRun

theorem compiled_halting_iff (program : List Mov.Instruction) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) :
    LoopHalts (compile program) target ↔ Mov.LoopHalts program source := by
  constructor
  · rintro ⟨n, finish, completed, fault⟩
    cases sourceRun : Mov.repeatRun program n source with
    | none =>
      have failed := repeat_compiles program n source target rep
      simp only [sourceRun] at failed
      rw [failed] at completed
      cases completed
    | some next =>
      have correct := repeat_compiles program n source target rep
      simp only [sourceRun] at correct
      rcases correct with ⟨actual, actualRun, actualRep⟩
      have equal : actual = finish := Option.some.inj (actualRun.symm.trans completed)
      subst actual
      exact ⟨n, next, (Mov.passes_iff_repeat program n source next).2 sourceRun,
        (compile_fault_iff program next finish actualRep).1 fault⟩
  · rintro ⟨n, next, completed, fault⟩
    have sourceRun := (Mov.passes_iff_repeat program n source next).1 completed
    have correct := repeat_compiles program n source target rep
    simp only [sourceRun] at correct
    rcases correct with ⟨finish, finishRun, finishRep⟩
    exact ⟨n, finish, finishRun, (compile_fault_iff program next finish finishRep).2 fault⟩

theorem compiled_divergence_iff (program : List Mov.Instruction) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) :
    LoopDiverges (compile program) target ↔ Mov.LoopDiverges program source := by
  constructor
  · intro infinite n
    rcases infinite n with ⟨finish, completed⟩
    cases sourceRun : Mov.repeatRun program n source with
    | none =>
      have failed := repeat_compiles program n source target rep
      simp only [sourceRun] at failed
      rw [failed] at completed
      cases completed
    | some next => exact ⟨next, (Mov.passes_iff_repeat program n source next).2 sourceRun⟩
  · intro infinite n
    rcases infinite n with ⟨next, completed⟩
    have sourceRun := (Mov.passes_iff_repeat program n source next).1 completed
    have correct := repeat_compiles program n source target rep
    simp only [sourceRun] at correct
    rcases correct with ⟨finish, finishRun, _⟩
    exact ⟨finish, finishRun⟩

@[expose] def kernelProgram : List Instruction := compile Mov.kernelProgram

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem kernel_length : kernelProgram.length = 2252 := by decide

/-- Dolan's computational result in the disclosed model: exactly four
registers, the three MOV forms, one static body and one unconditional backedge,
invalid-zero halting, and unbounded words/memory. The initial memory is generated
from the finite TM table and input, without any oracle for future execution. -/
theorem four_register_mov_simulation : ∃ program : List Instruction,
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      let c := TM.initialConfiguration machine input
      let s := initialState (Mov.initialKernelState machine c)
      (LoopHalts program s ↔ TM.Halts machine c) ∧
      (LoopDiverges program s ↔ TM.Diverges machine c) := by
  refine ⟨kernelProgram, ?_⟩
  intro alphabet states machine input
  let c := TM.initialConfiguration machine input
  let source := Mov.initialKernelState machine c
  have coherent := initial_coherent source
  exact ⟨(compiled_halting_iff Mov.kernelProgram source _ coherent).trans (Mov.kernel_halting_iff machine c),
    (compiled_divergence_iff Mov.kernelProgram source _ coherent).trans (Mov.kernel_divergence_iff machine c)⟩

end SmcTuring.Dolan.Four
