module
public import SmcTuring.MathlibTM0.Compiler
public import SmcTuring.SMC.ConcreteTerminalTape

public section

namespace SmcTuring.MathlibTM0

theorem source_run_reaches {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (count : Nat) (start finish : TM.Configuration alphabet states)
    (completed : TM.run machine count start = some finish) :
    StateTransition.Reaches (TM.step machine) start finish := by
  induction count generalizing start with
  | zero =>
    have same : start = finish := Option.some.inj completed
    subst finish
    exact Relation.ReflTransGen.refl
  | succ count ih =>
    cases first : TM.step machine start with
    | none => simp [TM.run, first] at completed
    | some next =>
      have rest : TM.run machine count next = some finish := by simpa [TM.run, first] using completed
      exact Relation.ReflTransGen.head first (ih next rest)

theorem source_reaches_run {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start finish : TM.Configuration alphabet states)
    (reached : StateTransition.Reaches (TM.step machine) start finish) :
    ∃ count, TM.run machine count start = some finish := by
  induction reached with
  | refl => exact ⟨0, rfl⟩
  | @tail middle finish history last ih =>
    rcases ih with ⟨count, completed⟩
    refine ⟨count + 1, ?_⟩
    rw [TM.run_add, completed]
    simpa [TM.run] using last

theorem source_halts_eval {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start : TM.Configuration alphabet states) :
    TM.Halts machine start ↔ (StateTransition.eval (TM.step machine) start).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨count, finish, completed, halted⟩
    exact ⟨finish, StateTransition.mem_eval.mpr ⟨source_run_reaches machine count start finish completed, halted⟩⟩
  · rintro ⟨finish, result⟩
    rcases StateTransition.mem_eval.mp result with ⟨reached, halted⟩
    rcases source_reaches_run machine start finish reached with ⟨count, completed⟩
    exact ⟨count, finish, completed, halted⟩

variable {alphabet states : Nat} [Inhabited (Fin alphabet)] [Inhabited (Fin states)]

/-- Refinement for the actual imported Mathlib transition functions. Each
library transition takes a positive number of source transitions. -/
theorem compiler_respects (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) :
    StateTransition.Respects (Turing.TM0.step machine) (TM.step (compile machine)) Rep := by
  intro library source rep
  cases chosen : machine library.q library.Tape.head with
  | none =>
    have halted : Turing.TM0.step machine library = none := by simp [Turing.TM0.step, chosen]
    rw [halted]
    exact (missing_step_iff machine library source rep).mpr halted
  | some command =>
    rcases command with ⟨next, statement⟩
    cases statement with
    | move dir =>
      simp only [Turing.TM0.step, chosen, Option.map_some]
      exact ⟨moveResult source next dir, move_rep library source next dir rep,
        Relation.TransGen.single (move_step machine library source next dir rep chosen)⟩
    | write symbol =>
      simp only [Turing.TM0.step, chosen, Option.map_some]
      have before : StateTransition.Reaches₁ (TM.step (compile machine)) source (writeMiddle source next symbol) :=
        Relation.TransGen.single (write_first_step machine library source next symbol rep chosen)
      exact ⟨writeResult source next symbol, write_rep library source next symbol rep,
        before.trans
          (Relation.TransGen.single (write_second_step machine source next symbol))⟩

theorem standard_halts_iff (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) (input : List (Fin alphabet)) :
    TM.Halts (compile machine) (TM.initialConfiguration (compile machine) input) ↔
      (Turing.TM0.eval machine input).Dom := by
  rw [source_halts_eval]
  exact StateTransition.tr_eval_dom (compiler_respects machine) (initial_rep machine input)

/-- Actual Mathlib TM0 partial evaluation, the fixed SMC image, purity, and
unending actual code changes are connected without a hypothesized adapter. -/
theorem fixed_smc_mathlib_simulation (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (input : List (Fin alphabet)) :
    (SMC.Concrete.ReachesTerminal (SMC.Concrete.initialTMState (compile machine) input) ↔
      (Turing.TM0.eval machine input).Dom) ∧
    (SMC.Concrete.RunsForever (SMC.Concrete.initialTMState (compile machine) input) ↔
      ¬ (Turing.TM0.eval machine input).Dom) ∧
    SMC.Concrete.PureComputation (SMC.Concrete.initialTMState (compile machine) input) ∧
    (¬ (Turing.TM0.eval machine input).Dom →
      SMC.Concrete.InfinitelyChanges (SMC.Concrete.initialTMState (compile machine) input)) := by
  have core := SMC.Concrete.pure_infinitely_smc_universality alphabet (2 * states) (compile machine) input
  have halted := standard_halts_iff machine input
  have infinite : TM.Diverges (compile machine) (TM.initialConfiguration (compile machine) input) ↔
      ¬ (Turing.TM0.eval machine input).Dom :=
    (TM.diverges_iff_not_halts _ _).trans (not_congr halted)
  exact ⟨core.1.trans halted, core.2.1.trans infinite, core.2.2.1,
    fun notHalted => core.2.2.2 (infinite.mpr notHalted)⟩

/-- Every terminal SMC run yields Mathlib's actual partial-evaluation output.
The stronger relation also observes the complete two-sided tape in code words;
the absolute head coordinate is carried by the related source configuration. -/
theorem standard_terminal_output (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (input : List (Fin alphabet)) (count : Nat) (finish : SMC.State)
    (reached : SMC.runImage 1 SMC.Concrete.image count (SMC.Concrete.initialTMState (compile machine) input) = some finish)
    (terminal : finish.pc = SMC.Concrete.terminalPC) :
    ∃ (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states)),
      library.Tape.right₀ ∈ Turing.TM0.eval machine input ∧ Rep library source ∧
      SMC.Concrete.TapeWords source finish ∧
      ∀ position : Int,
        finish.memory (SMC.heapField SMC.Concrete.dataLayout.data
          ((Dolan.Table.tapeLayout alphabet (2 * states)).cell (source.head + position), false)) =
        SMC.encodeWord SMC.Concrete.dataLayout.data
          (.address ((Dolan.Table.tapeLayout alphabet (2 * states)).symbol (library.Tape.nth position))) := by
  rcases SMC.Concrete.terminal_output_reflects (compile machine) input count finish reached terminal with
    ⟨steps, source, completed, halted, words⟩
  have sourceResult : source ∈ StateTransition.eval (TM.step (compile machine))
      (TM.initialConfiguration (compile machine) input) :=
    StateTransition.mem_eval.mpr ⟨source_run_reaches _ steps _ source completed, halted⟩
  rcases StateTransition.tr_eval_rev (compiler_respects machine) (initial_rep machine input) sourceResult with
    ⟨library, rep, evaluated⟩
  refine ⟨library, source, (Part.mem_map_iff _).mpr ⟨library, evaluated, rfl⟩, rep, words, ?_⟩
  intro position
  rw [words.2 (source.head + position), rep.2 position]

end SmcTuring.MathlibTM0
