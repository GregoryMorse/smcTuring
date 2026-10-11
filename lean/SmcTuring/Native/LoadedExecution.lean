module
public import SmcTuring.Native.RegionExecution

public section

namespace SmcTuring.Native.LoadedExecution

open MemoryRegion RegionExecution

/-- A native state with exactly the finite loaded byte image and the four
observed scalar components. Exterior memory is absent from this state. -/
structure State (mode : Mode) (region : Region) where
  pc : Word mode
  accumulator : Word mode
  stack : Word mode
  carry : Bool
  memory : Image region

@[expose] def expand (mode : Mode) (region : Region) (state : State mode region) : Execution.State mode :=
  ⟨state.pc, state.accumulator, state.stack, state.carry, MemoryRegion.expand region state.memory⟩

@[expose] def snapshot (mode : Mode) (region : Region) (state : Execution.State mode) : State mode region :=
  ⟨state.pc, state.accumulator, state.stack, state.carry, MemoryRegion.snapshot region state.memory⟩

theorem snapshot_agrees (mode : Mode) (region : Region) (state : Execution.State mode) :
    StateAgree mode region (expand mode region (snapshot mode region state)) state :=
  ⟨rfl, rfl, rfl, rfl, expanded_snapshot_agrees region state.memory⟩

theorem snapshot_expand (mode : Mode) (region : Region) (state : State mode region) :
    snapshot mode region (expand mode region state) = state := by
  cases state
  simp only [snapshot, expand, MemoryRegion.snapshot_expand]

/-- Partial finite execution: the current bytes choose the form, and every
fetch/read/write window must fit before an instruction can be accepted.
The returned form is an observed event, never an input to this evaluator. -/
@[expose] def step (mode : Mode) (region : Region) (state : State mode region) :
    Option (Form mode × State mode region) :=
  let current := expand mode region state
  (Fetch.fetch mode current.memory current.pc.toNat).bind fun form =>
    if Safe mode region form current then
      some (form, snapshot mode region (Execution.execute mode form current)) else none

/-- Every safe step of an agreeing total-byte model has an accepted finite step. -/
theorem step_complete (mode : Mode) (region : Region) (state : State mode region)
    (model : Execution.State mode) (form : Form mode)
    (same : StateAgree mode region (expand mode region state) model)
    (fetched : Fetch.fetch mode model.memory model.pc.toNat = some form)
    (safe : Safe mode region form model) :
    step mode region state = some (form, snapshot mode region (Execution.execute mode form (expand mode region state))) ∧
      StateAgree mode region
        (expand mode region (snapshot mode region (Execution.execute mode form (expand mode region state))))
        (Execution.execute mode form model) := by
  have fetchedHere := (fetch_agrees mode region _ model same safe.1).trans fetched
  have safeHere := safe_agrees mode region form _ model same safe
  refine ⟨?_, ?_⟩
  · simp only [step, fetchedHere, Option.bind_some, ite_eq_left safeHere]
  · have executed := execute_agrees mode region form _ model same safe.2.1
    have finite := snapshot_agrees mode region (Execution.execute mode form (expand mode region state))
    exact ⟨finite.1.trans executed.1, finite.2.1.trans executed.2.1,
      finite.2.2.1.trans executed.2.2.1, finite.2.2.2.1.trans executed.2.2.2.1,
      agree_trans region finite.2.2.2.2 executed.2.2.2.2⟩

/-- An accepted finite step is an actual safe current-byte step of every agreeing
exterior completion, with all observed scalar and loaded-byte effects equal. -/
theorem step_sound (mode : Mode) (region : Region) (state finish : State mode region)
    (model : Execution.State mode) (form : Form mode)
    (same : StateAgree mode region (expand mode region state) model)
    (stepped : step mode region state = some (form, finish)) :
    Fetch.fetch mode model.memory model.pc.toNat = some form ∧
      Safe mode region form model ∧
      StateAgree mode region (expand mode region finish) (Execution.execute mode form model) := by
  unfold step at stepped
  cases fetched : Fetch.fetch mode (expand mode region state).memory (expand mode region state).pc.toNat with
  | none => simp only [fetched, Option.bind_none, reduceCtorEq] at stepped
  | some current =>
    simp only [fetched, Option.bind_some] at stepped
    split at stepped
    next safe =>
      have paired := Option.some.inj stepped
      have sameForm := congrArg Prod.fst paired
      have sameFinish := congrArg Prod.snd paired
      dsimp at sameForm sameFinish
      subst current
      subst finish
      have modelSafe := safe_agrees mode region form model _ (state_agree_symm mode region same) safe
      have modelFetched := (fetch_agrees mode region _ model same modelSafe.1).symm.trans fetched
      exact ⟨modelFetched, modelSafe, (step_complete mode region state model form same modelFetched modelSafe).2⟩
    next rejected => simp only [reduceCtorEq] at stepped

inductive Trace (mode : Mode) (region : Region) : State mode region → List (Form mode) → State mode region → Prop where
  | nil (state : State mode region) : Trace mode region state [] state
  | step {state finish next : State mode region} {form : Form mode} {rest : List (Form mode)}
      (stepped : step mode region state = some (form, next))
      (tail : Trace mode region next rest finish) : Trace mode region state (form :: rest) finish

/-- A safe total-byte trace can be executed using only a finite loaded image. -/
theorem trace_complete (mode : Mode) (region : Region) {model finish : Execution.State mode}
    {forms : List (Form mode)} (trace : Fetch.Trace mode model forms finish)
    (safe : SafeRun mode region forms model) (state : State mode region)
    (same : StateAgree mode region (expand mode region state) model) :
    ∃ loadedFinish, Trace mode region state forms loadedFinish ∧
      StateAgree mode region (expand mode region loadedFinish) finish := by
  induction trace generalizing state with
  | nil => exact ⟨state, Trace.nil state, same⟩
  | @step model finish form rest fetched tail ih =>
    have one := step_complete mode region state model form same fetched safe.1
    obtain ⟨loadedFinish, loadedTrace, agrees⟩ := ih safe.2 _ one.2
    exact ⟨loadedFinish, Trace.step one.1 loadedTrace, agrees⟩

/-- Every finite trace refines automatic native fetch and has a contained access
footprint at every successive state. No later safe trace is assumed. -/
theorem trace_sound (mode : Mode) (region : Region) {state finish : State mode region}
    {forms : List (Form mode)} (trace : Trace mode region state forms finish)
    (model : Execution.State mode) (same : StateAgree mode region (expand mode region state) model) :
    Fetch.Trace mode model forms (Execution.runForms mode forms model) ∧
      SafeRun mode region forms model ∧
      StateAgree mode region (expand mode region finish) (Execution.runForms mode forms model) := by
  induction trace generalizing model with
  | nil => exact ⟨Fetch.Trace.nil model, trivial, same⟩
  | @step state finish next form rest stepped tail ih =>
    have one := step_sound mode region state next model form same stepped
    have continued := ih (Execution.execute mode form model) one.2.2
    exact ⟨Fetch.Trace.step one.1 continued.1, ⟨one.2.1, continued.2.1⟩, continued.2.2⟩

end SmcTuring.Native.LoadedExecution
