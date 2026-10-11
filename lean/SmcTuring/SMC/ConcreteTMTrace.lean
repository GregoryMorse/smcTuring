module
public import SmcTuring.SMC.ConcreteSimulation

public section

namespace SmcTuring.SMC.Concrete

open Dolan

/-- A TM step consumes at least one complete source body pass. This strengthens
the existing finite-run simulation with the progress bound needed for late events. -/
theorem source_tm_run_progress {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (steps : Nat) (start finish : TM.Configuration alphabet states) (source : Mov.State)
    (scanned : Mov.ScanRep machine start 0 source) (completed : TM.run machine steps start = some finish) :
    ∃ passes sourceFinish, steps ≤ passes ∧ Mov.Passes Mov.kernelProgram source sourceFinish passes ∧
      Mov.ScanRep machine finish 0 sourceFinish := by
  induction steps generalizing start finish source with
  | zero =>
    have same : start = finish := Option.some.inj completed
    subst finish
    exact ⟨0, source, Nat.zero_le _, Mov.Passes.zero source, scanned⟩
  | succ steps ih =>
    cases first : TM.step machine start with
    | none => simp [TM.run, first] at completed
    | some intermediate =>
      have last : TM.run machine steps intermediate = some finish := by simpa [TM.run, first] using completed
      rcases Mov.simulate_step machine start intermediate 0 source scanned first with
        ⟨firstPasses, sourceMiddle, positive, _, before, nextRep⟩
      rcases ih intermediate finish sourceMiddle nextRep last with ⟨lastPasses, sourceFinish, bound, after, finalRep⟩
      exact ⟨firstPasses + lastPasses, sourceFinish, by omega,
        Mov.passes_append Mov.kernelProgram before after, finalRep⟩

structure TMTraceSpec {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (configuration : TM.Configuration alphabet states) (source : Mov.State) (start finish : State)
    (steps passes : Nat) : Prop where
  progress : steps ≤ passes
  executed : Executes (passes * kernelCount) start finish
  static : Static finish
  pc : finish.pc = kernelPC
  scanned : Mov.ScanRep machine configuration 0 source
  represented : Virtual.Rep dataLayout source finish

theorem tm_run_correct {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (steps : Nat) (configuration : TM.Configuration alphabet states)
    (completed : TM.run machine steps (TM.initialConfiguration machine input) = some configuration) :
    ∃ passes source finish, TMTraceSpec machine configuration source (initialTMState machine input) finish steps passes := by
  rcases source_tm_run_progress machine steps _ configuration
    (Mov.initialKernelState machine (TM.initialConfiguration machine input)) (initial_tm_rep machine input).2 completed with
    ⟨passes, sourceFinish, bound, history, scanned⟩
  rcases kernel_passes _ sourceFinish passes (initialTMState machine input) history
    (initial_tm_static machine input) (initial_tm_rep machine input).1 (by rfl) with
    ⟨finish, executed, stable, represented, atKernel⟩
  exact ⟨passes, sourceFinish, finish, bound, executed, stable, atKernel, scanned, represented⟩

theorem configuration_head_word {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (configuration : TM.Configuration alphabet states) (source : Mov.State) (s : State)
    (scanned : Mov.ScanRep machine configuration 0 source) (rep : Virtual.Rep dataLayout source s) :
    s.memory (Virtual.registerField dataLayout .current) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).cell configuration.head)) := by
  rw [rep.1 .current, scanned.1.2.1.1.1]

/-- Every logical tape cell is observed, including cells beyond the original
input and on the negative side of the tape. This is a full-output invariant. -/
theorem configuration_tape_words {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (configuration : TM.Configuration alphabet states) (source : Mov.State) (s : State)
    (scanned : Mov.ScanRep machine configuration 0 source) (rep : Virtual.Rep dataLayout source s) (position : Int) :
    s.memory (heapField dataLayout.data ((Table.tapeLayout alphabet states).cell position, false)) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).symbol (configuration.tape position))) := by
  rw [rep.2 _, scanned.1.2.1.2.1 position]

end SmcTuring.SMC.Concrete
