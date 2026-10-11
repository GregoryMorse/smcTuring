module
public import SmcTuring.SMC.ComputableFiniteTM0

public section

namespace SmcTuring.Examples.Addition

/-- Exact transcription of main.cpp:462-479. Symbols 0,1,2 mean 0,1,_;
labels are the printed states minus one. State 2 (index 1) has no transition. -/
@[expose] def machine : TM.Machine 3 7 :=
  { blank := 2
    start := 0
    transition := fun state symbol => match state.val, symbol.val with
      | 0, 0 => some (0, true, 0)
      | 0, 1 => some (1, true, 0)
      | 0, 2 => some (2, true, 2)
      | 2, 0 => some (0, true, 2)
      | 2, 1 => some (1, true, 3)
      | 2, 2 => some (2, true, 1)
      | 3, 0 => some (0, true, 3)
      | 3, 1 => some (1, true, 3)
      | 3, 2 => some (2, false, 4)
      | 4, 0 => some (1, false, 4)
      | 4, 1 => some (0, false, 5)
      | 5, 0 => some (0, false, 5)
      | 5, 1 => some (1, false, 5)
      | 5, 2 => some (2, false, 6)
      | 6, 1 => some (0, false, 6)
      | 6, 0 => some (1, true, 0)
      | 6, 2 => some (1, true, 0)
      | _, _ => none }

@[expose] def input : List (Fin 3) := [0, 1, 0, 0, 2, 1, 0, 0, 1, 2]
@[expose] def expected : List (Fin 3) := [1, 1, 0, 1, 2, 0, 0, 0, 0, 2]
@[expose] def window (configuration : TM.Configuration 3 7) : List (Fin 3) :=
  List.ofFn (fun index : Fin 10 => configuration.tape (index.val : Int))
@[expose] def observe (configuration : TM.Configuration 3 7) : Fin 7 × Int × List (Fin 3) :=
  (configuration.state, configuration.head, window configuration)

set_option maxRecDepth 8192 in
/-- Kernel reduction checks all 132 actual source transitions and their result. -/
theorem addition_trace :
    (TM.run machine 132 (TM.initialConfiguration machine input)).map observe =
      some (1, 10, expected) := by rfl

/-- Displayed repository output, using its literal symbol convention. -/
theorem displayed_output :
    expected.map (fun symbol => if symbol.val = 0 then '0' else if symbol.val = 1 then '1' else '_') =
      "1101_0000_".toList := by rfl

/-- The result is genuinely halted in the undefined printed state 2. -/
theorem addition_halts_with_output :
    ∃ configuration : TM.Configuration 3 7,
      TM.run machine 132 (TM.initialConfiguration machine input) = some configuration ∧
      TM.step machine configuration = none ∧
      configuration.state = 1 ∧ configuration.head = 10 ∧ window configuration = expected := by
  rcases Option.map_eq_some_iff.mp addition_trace with ⟨configuration, ran, observed⟩
  have state : configuration.state = 1 := congrArg (fun result : Fin 7 × Int × List (Fin 3) => result.1) observed
  have head : configuration.head = 10 := congrArg (fun result : Fin 7 × Int × List (Fin 3) => result.2.1) observed
  have output : window configuration = expected := congrArg (fun result : Fin 7 × Int × List (Fin 3) => result.2.2) observed
  refine ⟨configuration, ran, ?_, state, head, output⟩
  apply TM.missing_transition_halts
  rw [state]
  rfl

/-- Instantiate the general theorem with the unchanged repository example.
The terminal SMC state retains the entire two-sided tape and head, and its
printed window is 1101_0000_. Every reached computational instruction is pure. -/
theorem addition_pure_smc :
    SMC.Concrete.PureComputation (SMC.Concrete.initialTMState machine input) ∧
    ∃ (configuration : TM.Configuration 3 7) (count : Nat) (finish : SMC.State),
      TM.run machine 132 (TM.initialConfiguration machine input) = some configuration ∧
      SMC.runImage 1 SMC.Concrete.image count (SMC.Concrete.initialTMState machine input) = some finish ∧
      finish.pc = SMC.Concrete.terminalPC ∧ SMC.Concrete.TapeWords configuration finish ∧
      configuration.head = 10 ∧ window configuration = expected := by
  rcases addition_halts_with_output with ⟨configuration, ran, halted, _, head, output⟩
  rcases SMC.Concrete.tm_halt_output machine input 132 configuration ran halted with ⟨count, finish, terminal⟩
  have pure := (SMC.Concrete.pure_infinitely_smc_universality 3 7 machine input).2.2.1
  exact ⟨pure, configuration, count, finish, ran, terminal.executed.1, terminal.terminal, terminal.output, head, output⟩

end SmcTuring.Examples.Addition
