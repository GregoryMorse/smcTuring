module
public import SmcTuring.SMC.ConcreteChanges

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def FieldChangeAt (start : State) (time : Nat) (field : Int) : Prop :=
  ∃ s instruction next, runImage 1 image time start = some s ∧
    fetch image s = some (instruction, next) ∧
    (execute 1 instruction next s).memory field ≠ s.memory field

/-- Actual fetched changes occur in fields beyond every finite address bound.
This is stronger than infinitely many changes in a fixed finite set of fields. -/
@[expose] def UnboundedChangedFields (start : State) : Prop :=
  ∀ bound : Nat, ∃ field time, (bound : Int) < field ∧ image.codeField field ∧ FieldChangeAt start time field

theorem field_change_is_code_change (start : State) (time : Nat) (field : Int)
    (code : image.codeField field) (event : FieldChangeAt start time field) : CodeChangeAt start time := by
  rcases event with ⟨s, instruction, next, reached, fetched, changed⟩
  exact ⟨s, instruction, next, reached, fetched, field, code, changed⟩

theorem field_change_in_run (count : Nat) (start finish : State) (field : Int)
    (completed : runImage 1 image count start = some finish)
    (different : finish.memory field ≠ start.memory field) :
    ∃ time, time < count ∧ FieldChangeAt start time field := by
  induction count generalizing start with
  | zero =>
    have same : start = finish := Option.some.inj completed
    subst start
    exact False.elim (different rfl)
  | succ count ih =>
    cases fetched : fetch image start with
    | none => simp [runImage, step, fetched] at completed
    | some entry =>
      rcases entry with ⟨instruction, next⟩
      have tail : runImage 1 image count (execute 1 instruction next start) = some finish := by
        simpa [runImage, step, fetched] using completed
      by_cases unchanged : (execute 1 instruction next start).memory field = start.memory field
      · rcases ih _ tail (by simpa only [unchanged] using different) with
          ⟨time, bound, s, eventInstruction, eventNext, reached, event, changed⟩
        refine ⟨time + 1, by omega, s, eventInstruction, eventNext, ?_, event, changed⟩
        simpa [runImage, step, fetched] using reached
      · exact ⟨0, by omega, start, instruction, next, rfl, fetched, unchanged⟩

/-- A finite one-state, one-symbol TM that moves right forever. -/
@[expose] def walkerMachine : TM.Machine 1 1 :=
  { blank := 0, start := 0, transition := fun _ _ => some (0, true, 0) }

@[expose] def walkerConfiguration (steps : Nat) : TM.Configuration 1 1 :=
  { state := 0, head := (steps : Int), tape := fun _ => 0 }

theorem walker_initial : TM.initialConfiguration walkerMachine [] = walkerConfiguration 0 := by
  simp [TM.initialConfiguration, walkerMachine, walkerConfiguration]

theorem walker_step (steps : Nat) :
    TM.step walkerMachine (walkerConfiguration steps) = some (walkerConfiguration (steps + 1)) := by
  simp [TM.step, walkerMachine, walkerConfiguration]

theorem walker_run (steps : Nat) :
    TM.run walkerMachine steps (TM.initialConfiguration walkerMachine []) = some (walkerConfiguration steps) := by
  induction steps with
  | zero => exact congrArg some walker_initial
  | succ steps ih =>
    rw [TM.run_add, ih, Option.bind_some]
    simp only [TM.run, walker_step, Option.bind_some]

theorem walker_diverges : TM.Diverges walkerMachine (TM.initialConfiguration walkerMachine []) :=
  fun steps => ⟨walkerConfiguration steps, walker_run steps⟩

theorem walker_field_bound (bound : Nat) :
    (bound : Int) < heapField dataLayout.data ((Table.tapeLayout 1 1).cell ((bound + 1 : Nat) : Int), true) := by
  have enumeration : Encoding.zigzag (((bound + 1 : Nat) : Int)) = 2 * (bound + 1) := rfl
  simp only [heapField, fieldAddress, dataLayout, Table.tapeLayout, Encoding.standardLayout]
  rw [enumeration]
  simp
  omega

/-- For every address bound, the walker changes a distinct tape-link operand
beyond that bound. Boundary differences are traced back to actual fetched
instructions changing that particular field. -/
theorem walker_unbounded_fields : UnboundedChangedFields (initialTMState walkerMachine []) := by
  intro bound
  let position : Int := ((bound + 1 : Nat) : Int)
  let field := heapField dataLayout.data ((Table.tapeLayout 1 1).cell position, true)
  rcases tm_run_correct walkerMachine [] (bound + 2) (walkerConfiguration (bound + 2)) (walker_run _) with
    ⟨passes, source, finish, traced⟩
  have initialRep := initial_tm_rep walkerMachine []
  have oldLink := initialRep.2.1.2.1.2.2.2 position (by
    change 0 < position
    dsimp [position]
    omega)
  have newLink := traced.scanned.1.2.1.2.2.1 position (by
    change position < ((bound + 2 : Nat) : Int)
    dsimp [position]
    omega)
  have oldValue : (initialTMState walkerMachine []).memory field =
      encodeWord dataLayout.data (.address ((Table.tapeLayout 1 1).cell (position + 1))) := by
    rw [initialRep.1.2 _, oldLink]
  have newValue : finish.memory field =
      encodeWord dataLayout.data (.address ((Table.tapeLayout 1 1).cell (position - 1))) := by
    rw [traced.represented.2 _, newLink]
  have different : finish.memory field ≠ (initialTMState walkerMachine []).memory field := by
    rw [newValue, oldValue]
    intro equal
    have cells := Mov.Word.address.inj (encode_word_injective dataLayout.data equal)
    have positions := (Table.tapeLayout 1 1).cell_injective cells
    omega
  rcases field_change_in_run _ _ finish field traced.executed.1 different with ⟨time, _, changed⟩
  refine ⟨field, time, walker_field_bound bound, ?_, changed⟩
  change -38 ≤ field
  have positive := walker_field_bound bound
  change (bound : Int) < field at positive
  omega

theorem pure_unbounded_smc_witness :
    RunsForever (initialTMState walkerMachine []) ∧ PureComputation (initialTMState walkerMachine []) ∧
      InfinitelyChanges (initialTMState walkerMachine []) ∧ UnboundedChangedFields (initialTMState walkerMachine []) := by
  have computation := pure_infinitely_smc_universality 1 1 walkerMachine []
  exact ⟨computation.2.1.mpr walker_diverges, computation.2.2.1,
    computation.2.2.2 walker_diverges, walker_unbounded_fields⟩

end SmcTuring.SMC.Concrete
