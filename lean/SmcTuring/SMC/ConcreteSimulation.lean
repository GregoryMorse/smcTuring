module
public import SmcTuring.SMC.ConcreteLoops
public import SmcTuring.SMC.ConcreteTMInitialization

public section

namespace SmcTuring.SMC.Concrete

open Dolan

theorem Executes.prefix {count small : Nat} {start finish : State} (completed : Executes count start finish)
    (bounded : small ≤ count) : ∃ middle, Executes small start middle := by
  have partition : small + (count - small) = count := Nat.add_sub_of_le bounded
  have full := completed.1
  rw [← partition, run_image_add] at full
  cases first : runImage 1 image small start with
  | none => simp [first] at full
  | some middle =>
    refine ⟨middle, first, ?_⟩
    have pure := completed.2
    rw [← partition] at pure
    exact ((pure_steps_composition 1 image small (count - small) start middle first).mp pure).1

/-- Any finite number of successful source passes becomes one fetched pure
execution, with a positive fixed instruction count per pass and full state. -/
theorem kernel_passes (source next : Mov.State) (passes : Nat) (s : State)
    (history : Mov.Passes Mov.kernelProgram source next passes) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) :
    ∃ finish, Executes (passes * kernelCount) s finish ∧ Static finish ∧
      Virtual.Rep dataLayout next finish ∧ finish.pc = kernelPC := by
  induction history generalizing s with
  | zero => exact ⟨s, ⟨rfl, trivial⟩, ready, rep, pc⟩
  | succ completed rest ih =>
    rcases kernel_success _ _ s ready rep pc completed with ⟨middle, first⟩
    rcases ih middle first.static first.represented first.pc with ⟨finish, last, stable, represented, atKernel⟩
    refine ⟨finish, ?_, stable, represented, atKernel⟩
    simpa [Nat.succ_mul, Nat.add_comm] using first.executed.trans last

@[expose] def ReachesTerminal (s : State) : Prop :=
  ∃ count finish, runImage 1 image count s = some finish ∧ finish.pc = terminalPC

@[expose] def RunsForever (s : State) : Prop :=
  ∀ count, ∃ finish, runImage 1 image count s = some finish

@[expose] def PureForever (s : State) : Prop := ∀ count, PureSteps 1 image count s

theorem source_halt_terminal (source : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) (halted : Mov.LoopHalts Mov.kernelProgram source) :
    ∃ count finish, Executes count s finish ∧ finish.pc = terminalPC := by
  rcases halted with ⟨passes, sourceFinish, history, stopped⟩
  rcases kernel_passes source sourceFinish passes s history ready rep pc with ⟨middle, before, stable, represented, atKernel⟩
  rcases kernel_fault sourceFinish middle stable represented atKernel stopped with ⟨count, finish, finalStep⟩
  exact ⟨passes * kernelCount + count, finish, before.trans finalStep.executed, finalStep.terminal⟩

theorem source_diverges_forever (source : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) (infinite : Mov.LoopDiverges Mov.kernelProgram source) :
    RunsForever s ∧ PureForever s := by
  have prefixes : ∀ count, ∃ finish, Executes count s finish := by
    intro count
    rcases infinite count with ⟨next, history⟩
    rcases kernel_passes source next count s history ready rep pc with ⟨finish, completed, _, _, _⟩
    have bounded : count ≤ count * kernelCount := by
      have positive := kernel_count_positive
      exact Nat.le_mul_of_pos_right count positive
    exact completed.prefix bounded
  exact ⟨fun count => by rcases prefixes count with ⟨finish, completed⟩; exact ⟨finish, completed.1⟩,
    fun count => by rcases prefixes count with ⟨_, completed⟩; exact completed.2⟩

theorem terminal_not_forever (s : State) (halted : ReachesTerminal s) : ¬ RunsForever s := by
  rcases halted with ⟨count, finish, completed, terminal⟩
  intro infinite
  rcases infinite (count + 1) with ⟨later, history⟩
  rw [run_image_add, completed, Option.bind_some] at history
  simp [runImage, terminal_observation finish terminal] at history

theorem source_terminal_iff (source : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) :
    ReachesTerminal s ↔ Mov.LoopHalts Mov.kernelProgram source := by
  constructor
  · intro terminal
    apply Classical.byContradiction
    intro notHalted
    have infinite := (Mov.loop_diverges_iff_not_halts Mov.kernelProgram source).mpr notHalted
    exact terminal_not_forever s terminal (source_diverges_forever source s ready rep pc infinite).1
  · intro halted
    rcases source_halt_terminal source s ready rep pc halted with ⟨count, finish, completed, terminal⟩
    exact ⟨count, finish, completed.1, terminal⟩

theorem source_forever_iff (source : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) :
    RunsForever s ↔ Mov.LoopDiverges Mov.kernelProgram source := by
  constructor
  · intro infinite
    apply (Mov.loop_diverges_iff_not_halts Mov.kernelProgram source).mpr
    intro halted
    exact terminal_not_forever s ((source_terminal_iff source s ready rep pc).mpr halted) infinite
  · intro infinite
    exact (source_diverges_forever source s ready rep pc infinite).1

theorem tm_terminal_iff {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) :
    ReachesTerminal (initialTMState machine input) ↔ TM.Halts machine (TM.initialConfiguration machine input) := by
  rw [source_terminal_iff _ _ (initial_tm_static machine input) (initial_tm_rep machine input).1 (by rfl),
    Mov.kernel_halting_iff]

theorem tm_forever_iff {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) :
    RunsForever (initialTMState machine input) ↔ TM.Diverges machine (TM.initialConfiguration machine input) := by
  rw [source_forever_iff _ _ (initial_tm_static machine input) (initial_tm_rep machine input).1 (by rfl),
    Mov.kernel_divergence_iff]

@[expose] def PureComputation (s : State) : Prop :=
  ∀ count finish, runImage 1 image count s = some finish → PureSteps 1 image count s

theorem terminal_later_none (s finish : State) (count later : Nat)
    (completed : runImage 1 image count s = some finish) (terminal : finish.pc = terminalPC) (strict : count < later) :
    runImage 1 image later s = none := by
  have partition : count + (later - count) = later := by omega
  rw [← partition, run_image_add, completed, Option.bind_some]
  cases difference : later - count with
  | zero => omega
  | succ rest => simp [runImage, terminal_observation finish terminal]

theorem terminal_execution_pure {s finish : State} {count : Nat} (completed : Executes count s finish)
    (terminal : finish.pc = terminalPC) : PureComputation s := by
  intro later actual history
  by_cases bounded : later ≤ count
  · rcases completed.prefix bounded with ⟨_, prefixExecution⟩
    exact prefixExecution.2
  · have noLater := terminal_later_none s finish count later completed.1 terminal (by omega)
    rw [noLater] at history
    cases history

theorem source_pure (source : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) : PureComputation s := by
  by_cases halted : Mov.LoopHalts Mov.kernelProgram source
  · rcases source_halt_terminal source s ready rep pc halted with ⟨count, finish, completed, terminal⟩
    exact terminal_execution_pure completed terminal
  · have infinite := (Mov.loop_diverges_iff_not_halts Mov.kernelProgram source).mpr halted
    have pure := (source_diverges_forever source s ready rep pc infinite).2
    exact fun count _ _ => pure count

/-- The fixed, explicitly constructed unbounded word image simulates every
finite-input TM. Both halting and divergence are equivalent, and every reached
instruction writes an owned instruction operand. Byte/CPU refinement is separate. -/
theorem fixed_pure_smc_simulation :
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      (ReachesTerminal (initialTMState machine input) ↔ TM.Halts machine (TM.initialConfiguration machine input)) ∧
      (RunsForever (initialTMState machine input) ↔ TM.Diverges machine (TM.initialConfiguration machine input)) ∧
      PureComputation (initialTMState machine input) := by
  intro alphabet states machine input
  exact ⟨tm_terminal_iff machine input, tm_forever_iff machine input,
    source_pure _ _ (initial_tm_static machine input) (initial_tm_rep machine input).1 (by rfl)⟩

end SmcTuring.SMC.Concrete
