module
public import SmcTuring.SMC.ConcreteTerminalTape
public import SmcTuring.SMC.FiniteExecution
public import SmcTuring.SMC.FiniteSerialization
public import SmcTuring.FrozenTM

public section

namespace SmcTuring.SMC.Concrete

/-- This finite register/journal record contains no memory or header function. -/
@[expose] def initialDescription : Finite.State :=
  { acc := 0, stack := returnField, pc := kernelPC, carry := false, changes := [] }

/-- A closed default-word algorithm whose only external inputs are a finite
transition table, finite input list and queried integer address. -/
@[expose] def initialWords {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (field : Int) : Int :=
  (initialTMState (TM.thaw machine) input).memory field

theorem initial_description_correct {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) :
    Finite.meaning (initialWords machine input) initialDescription = initialTMState (TM.thaw machine) input := rfl

/-- A terminating bounded evaluator over finite data. Header lookup and initial
word lookup are the fixed arithmetic/list algorithms, not caller-supplied oracles. -/
@[expose] def finiteRun {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) : Option Finite.State :=
  Finite.run 1 headers (initialWords machine input) count initialDescription

theorem finite_run_correct {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) :
    (finiteRun machine input count).map (Finite.meaning (initialWords machine input)) =
      runImage 1 image count (initialTMState (TM.thaw machine) input) := by
  exact Finite.run_correct 1 image (initialWords machine input) count initialDescription

theorem original_machine_finite_run {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) :
    (finiteRun (TM.freeze machine) input count).map (Finite.meaning (initialWords (TM.freeze machine) input)) =
      runImage 1 image count (initialTMState machine input) := by
  simpa only [TM.thaw_freeze] using finite_run_correct (TM.freeze machine) input count

/-- Every reached state has a finite list certificate of exactly count writes.
Every other address still has the computable initial word. No infinite tape is
materialized, and no future execution data enters the default generator. -/
theorem every_reached_state_finite {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) (finish : State)
    (completed : runImage 1 image count (initialTMState (TM.thaw machine) input) = some finish) :
    ∃ description, finiteRun machine input count = some description ∧
      Finite.meaning (initialWords machine input) description = finish ∧ description.changes.length = count ∧
      ∀ field, field ∉ description.changes.map Prod.fst → finish.memory field = initialWords machine input field := by
  rcases Finite.reached_description 1 image (initialWords machine input) count initialDescription finish completed with
    ⟨description, ran, same, length⟩
  refine ⟨description, ran, same, ?_, ?_⟩
  · simpa only [initialDescription, List.length_nil, Nat.zero_add] using length
  · intro field outside
    rw [← same]
    exact Finite.lookup_outside (initialWords machine input) description.changes field outside

@[expose] def FiniteReachesTerminal {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) : Prop :=
  ∃ count description, finiteRun machine input count = some description ∧ description.pc = terminalPC

@[expose] def FiniteRunsForever {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) : Prop := ∀ count, ∃ description, finiteRun machine input count = some description

theorem finite_terminal_equivalence {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) :
    FiniteReachesTerminal machine input ↔ ReachesTerminal (initialTMState (TM.thaw machine) input) := by
  constructor
  · rintro ⟨count, description, actual, terminal⟩
    have correct := finite_run_correct machine input count
    rw [actual, Option.map_some] at correct
    exact ⟨count, Finite.meaning (initialWords machine input) description, correct.symm, terminal⟩
  · rintro ⟨count, finish, reached, terminal⟩
    rcases every_reached_state_finite machine input count finish reached with ⟨description, actual, same, _, _⟩
    exact ⟨count, description, actual, (congrArg (fun s : State => s.pc) same).trans terminal⟩

theorem finite_divergence_equivalence {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) :
    FiniteRunsForever machine input ↔ RunsForever (initialTMState (TM.thaw machine) input) := by
  constructor
  · intro infinite count
    rcases infinite count with ⟨description, actual⟩
    have correct := finite_run_correct machine input count
    rw [actual, Option.map_some] at correct
    exact ⟨Finite.meaning (initialWords machine input) description, correct.symm⟩
  · intro infinite count
    rcases infinite count with ⟨finish, reached⟩
    rcases every_reached_state_finite machine input count finish reached with ⟨description, actual, _, _, _⟩
    exact ⟨description, actual⟩

/-- The word-model outcomes are computed by a finite-data evaluator. A formal
simulation of this evaluator by the established TM library remains separate. -/
theorem finite_data_computation {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) :
    (FiniteReachesTerminal machine input ↔ TM.Halts (TM.thaw machine) (TM.initialConfiguration (TM.thaw machine) input)) ∧
      (FiniteRunsForever machine input ↔ TM.Diverges (TM.thaw machine) (TM.initialConfiguration (TM.thaw machine) input)) := by
  exact ⟨(finite_terminal_equivalence machine input).trans (tm_terminal_iff (TM.thaw machine) input),
    (finite_divergence_equivalence machine input).trans (tm_forever_iff (TM.thaw machine) input)⟩

@[expose] def finiteEncodedRun {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) : Option (List Nat) :=
  (finiteRun machine input count).map Finite.serializeNat

theorem encoded_run_roundtrip {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) :
    (finiteEncodedRun machine input count).bind Finite.deserializeNat = finiteRun machine input count := by
  cases result : finiteRun machine input count with
  | none => simp [finiteEncodedRun, result]
  | some description => simp [finiteEncodedRun, result, Finite.deserialize_serialize_nat]

/-- A finite prefix has a reversible natural-number-list state encoding of
length 4 + 2*count, and decoding it recovers the complete actual word state. -/
theorem every_reached_state_encoded {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) (finish : State)
    (completed : runImage 1 image count (initialTMState (TM.thaw machine) input) = some finish) :
    ∃ words description, finiteEncodedRun machine input count = some words ∧
      Finite.deserializeNat words = some description ∧
      Finite.meaning (initialWords machine input) description = finish ∧ words.length = 4 + 2 * count := by
  rcases every_reached_state_finite machine input count finish completed with ⟨description, actual, same, length, _⟩
  refine ⟨Finite.serializeNat description, description, ?_, Finite.deserialize_serialize_nat description, same, ?_⟩
  · simp only [finiteEncodedRun, actual, Option.map_some]
  · rw [Finite.serialize_nat_length, length]

end SmcTuring.SMC.Concrete
