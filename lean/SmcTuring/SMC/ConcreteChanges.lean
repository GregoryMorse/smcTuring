module
public import SmcTuring.SMC.ConcreteTMTrace
public import SmcTuring.SMC.ImageChanges

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def CodeChangeAt (start : State) (time : Nat) : Prop :=
  ∃ s instruction next, runImage 1 image time start = some s ∧ fetch image s = some (instruction, next) ∧
    ChangesCode image.codeField 1 instruction next s

@[expose] def InfinitelyChanges (s : State) : Prop := ∀ bound, ∃ time, bound ≤ time ∧ CodeChangeAt s time

theorem changes_in_steps_event (count : Nat) (s : State) (changed : ChangesInSteps 1 image count s) :
    ∃ time, time < count ∧ CodeChangeAt s time := by
  induction count generalizing s with
  | zero => exact False.elim changed
  | succ count ih =>
    rcases changed with ⟨instruction, next, fetched, here | later⟩
    · exact ⟨0, by omega, s, instruction, next, rfl, fetched, here⟩
    · rcases ih (execute 1 instruction next s) later with ⟨time, bound, actual, eventInstruction, eventNext, before, event, different⟩
      refine ⟨time + 1, by omega, actual, eventInstruction, eventNext, ?_, event, different⟩
      simpa [runImage, step, fetched] using before

theorem code_change_after (start middle : State) (beforeCount time : Nat)
    (before : runImage 1 image beforeCount start = some middle) (event : CodeChangeAt middle time) :
    CodeChangeAt start (beforeCount + time) := by
  rcases event with ⟨s, instruction, next, reached, fetched, different⟩
  refine ⟨s, instruction, next, ?_, fetched, different⟩
  rw [run_image_add, before, Option.bind_some]
  exact reached

theorem tm_step_moves_head {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start finish : TM.Configuration alphabet states) (completed : TM.step machine start = some finish) :
    finish.head ≠ start.head := by
  cases transition : machine.transition start.state (start.tape start.head) with
  | none => simp [TM.step, transition] at completed
  | some entry =>
    rcases entry with ⟨symbol, direction, state⟩
    have equal : ({
        state := state
        head := if direction then start.head + 1 else start.head - 1
        tape := write start.tape start.head symbol } : TM.Configuration alphabet states) = finish :=
      Option.some.inj (by simpa [TM.step, transition] using completed)
    have heads := congrArg (fun configuration : TM.Configuration alphabet states => configuration.head) equal
    cases direction <;> simp only [Bool.false_eq_true, ite_false, ite_true] at heads <;> omega

theorem configuration_current_changes {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start finish : TM.Configuration alphabet states) (source sourceFinish : Mov.State)
    (scanned : Mov.ScanRep machine start 0 source) (scannedFinish : Mov.ScanRep machine finish 0 sourceFinish)
    (completed : TM.step machine start = some finish) : sourceFinish.registers .current ≠ source.registers .current := by
  intro same
  rw [scannedFinish.1.2.1.1.1, scanned.1.2.1.1.1] at same
  have cells := Mov.Word.address.inj same
  exact tm_step_moves_head machine start finish completed ((Table.tapeLayout alphabet states).cell_injective cells)

/-- Every nonhalting initialized TM creates actual operand changes arbitrarily
late in the fetched SMC execution. Repeated stores of the old word do not suffice. -/
theorem divergent_tm_infinitely_changes {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) (infinite : TM.Diverges machine (TM.initialConfiguration machine input)) :
    InfinitelyChanges (initialTMState machine input) := by
  intro bound
  rcases infinite bound with ⟨configuration, completed⟩
  rcases infinite (bound + 1) with ⟨nextConfiguration, continued⟩
  have last : TM.run machine 1 configuration = some nextConfiguration := by
    simpa only [TM.run_add, completed, Option.bind_some] using continued
  have step : TM.step machine configuration = some nextConfiguration := by
    cases first : TM.step machine configuration with
    | none => simp [TM.run, first] at last
    | some actual =>
      have same : actual = nextConfiguration := by simpa [TM.run, first] using last
      exact congrArg some same
  rcases tm_run_correct machine input bound configuration completed with ⟨passes, source, middle, before⟩
  rcases Mov.simulate_step machine configuration nextConfiguration 0 source before.scanned step with
    ⟨nextPasses, sourceFinish, _, _, history, scannedFinish⟩
  rcases kernel_passes source sourceFinish nextPasses middle history before.static before.represented before.pc with
    ⟨finish, after, _, represented, _⟩
  have changed := Virtual.represented_register_change dataLayout 1 image (nextPasses * kernelCount)
    source sourceFinish middle finish .current before.represented represented after.1
    (by simpa only [source_register_field] using source_register_code .current)
    (configuration_current_changes machine configuration nextConfiguration source sourceFinish before.scanned scannedFinish step)
  rcases changes_in_steps_event _ middle changed with ⟨time, _, event⟩
  refine ⟨passes * kernelCount + time, ?_, code_change_after _ middle _ time before.executed.1 event⟩
  have progress := before.progress
  have positive := kernel_count_positive
  have scaled : passes ≤ passes * kernelCount := Nat.le_mul_of_pos_right passes positive
  omega

/-- The word-model computation and infinite-modification result. The image and
finite-input initializer are concrete definitions, and code changes are actual
fetched value changes at arbitrarily late instruction times. Native refinement
remains a separate obligation. A distinct-field witness is proved in
ConcreteFreshFields. -/
theorem pure_infinitely_smc_universality :
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      (ReachesTerminal (initialTMState machine input) ↔ TM.Halts machine (TM.initialConfiguration machine input)) ∧
      (RunsForever (initialTMState machine input) ↔ TM.Diverges machine (TM.initialConfiguration machine input)) ∧
      PureComputation (initialTMState machine input) ∧
      (TM.Diverges machine (TM.initialConfiguration machine input) → InfinitelyChanges (initialTMState machine input)) := by
  intro alphabet states machine input
  have computation := fixed_pure_smc_simulation alphabet states machine input
  exact ⟨computation.1, computation.2.1, computation.2.2, divergent_tm_infinitely_changes machine input⟩

end SmcTuring.SMC.Concrete
