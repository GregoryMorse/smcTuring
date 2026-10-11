module
public import SmcTuring.Native.ControlBounds

public section

namespace SmcTuring.Native.CheckedExecution

open MemoryRegion RegionExecution MappedExecution ControlBounds

instance (mode : Mode) (environment : Environment) (form : Form mode) (state : Execution.State mode) :
    Decidable (TargetValid mode environment form state) := by
  cases form with
  | memory operation displacement => cases operation <;> unfold TargetValid <;> infer_instance
  | moffs address => unfold TargetValid; infer_instance
  | exchangeIndirect => unfold TargetValid; infer_instance
  | callRelative displacement => unfold TargetValid; infer_instance

/-- The finite evaluator checks all modeled memory windows and actual CALL
pointer loads. Hardware fetch coherence, segments and CET remain external. -/
@[expose] def step (mode : Mode) (environment : Environment) (region : Region)
    (state : LoadedExecution.State mode region) : Option (Form mode × LoadedExecution.State mode region) :=
  (LoadedExecution.step mode region state).bind fun result =>
    if Accesses mode environment result.1 (LoadedExecution.expand mode region state) ∧
        TargetValid mode environment result.1 (LoadedExecution.expand mode region state)
    then some result else none

theorem target_valid_agrees (mode : Mode) (environment : Environment) (region : Region) (form : Form mode)
    (left right : Execution.State mode) (same : StateAgree mode region left right)
    (reads : ReadWithin mode region form right) :
    TargetValid mode environment form left ↔ TargetValid mode environment form right := by
  have effects := execute_agrees mode region form left right same reads
  cases form with
  | memory operation displacement => cases operation <;> simp only [TargetValid, effects.1]
  | moffs address => rfl
  | exchangeIndirect => rfl
  | callRelative displacement => simp only [TargetValid, effects.1]

theorem step_complete (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (state finish : LoadedExecution.State mode region) (form : Form mode)
    (stepped : LoadedExecution.step mode region state = some (form, finish))
    (target : TargetValid mode environment form (LoadedExecution.expand mode region state)) :
    step mode environment region state = some (form, finish) := by
  have safe := (LoadedExecution.step_sound mode region state finish (LoadedExecution.expand mode region state) form
    (state_agree_refl mode region _) stepped).2.1
  have allowed := accesses_of_safe mode environment region mapping form _ safe
  simp only [step, stepped, Option.bind_some, ite_eq_left (And.intro allowed target)]

theorem step_sound (mode : Mode) (environment : Environment) (region : Region)
    (state finish : LoadedExecution.State mode region) (form : Form mode)
    (stepped : step mode environment region state = some (form, finish)) :
    LoadedExecution.step mode region state = some (form, finish) ∧
      Accesses mode environment form (LoadedExecution.expand mode region state) ∧
      TargetValid mode environment form (LoadedExecution.expand mode region state) := by
  unfold step at stepped
  cases selected : LoadedExecution.step mode region state with
  | none => simp only [selected, Option.bind_none, reduceCtorEq] at stepped
  | some result =>
    simp only [selected, Option.bind_some] at stepped
    split at stepped
    next allowed =>
      have paired := Option.some.inj stepped
      subst result
      exact ⟨rfl, allowed⟩
    next denied => simp only [reduceCtorEq] at stepped

/-- Even if instruction fetch and all memory windows succeed, a bad CALL
pointer load is rejected; it is not converted to a source-machine halt. -/
theorem step_target_denied (mode : Mode) (environment : Environment) (region : Region)
    (state finish : LoadedExecution.State mode region) (form : Form mode)
    (stepped : LoadedExecution.step mode region state = some (form, finish))
    (denied : ¬ TargetValid mode environment form (LoadedExecution.expand mode region state)) :
    step mode environment region state = none := by
  have disallowed : ¬ (Accesses mode environment form (LoadedExecution.expand mode region state) ∧
      TargetValid mode environment form (LoadedExecution.expand mode region state)) := fun allowed => denied allowed.2
  simp only [step, stepped, Option.bind_some, ite_eq_right disallowed]

inductive Trace (mode : Mode) (environment : Environment) (region : Region) :
    LoadedExecution.State mode region → List (Form mode) → LoadedExecution.State mode region → Prop where
  | nil (state) : Trace mode environment region state [] state
  | step {state finish next} {form} {rest}
      (stepped : step mode environment region state = some (form, next))
      (tail : Trace mode environment region next rest finish) : Trace mode environment region state (form :: rest) finish

/-- An actual safe loaded trace with derived targets is accepted by the combined
checker. Loaded-byte agreement supplies every intermediate target, not an oracle. -/
theorem trace_complete (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) {state finish : LoadedExecution.State mode region}
    {forms : List (Form mode)} (trace : LoadedExecution.Trace mode region state forms finish)
    (model : Execution.State mode) (same : StateAgree mode region (LoadedExecution.expand mode region state) model)
    (targets : Targets mode environment forms model) : Trace mode environment region state forms finish := by
  induction trace generalizing model with
  | nil => exact Trace.nil _
  | @step state finish next form rest stepped tail ih =>
    have one := LoadedExecution.step_sound mode region state next model form same stepped
    have targetHere := (target_valid_agrees mode environment region form _ model same one.2.1.2.1).mpr targets.1
    exact Trace.step (step_complete mode environment region mapping state next form stepped targetHere)
      (ih (Execution.execute mode form model) one.2.2 targets.2)

theorem trace_loaded (mode : Mode) (environment : Environment) (region : Region)
    {state finish : LoadedExecution.State mode region} {forms : List (Form mode)}
    (trace : Trace mode environment region state forms finish) : LoadedExecution.Trace mode region state forms finish := by
  induction trace with
  | nil => exact LoadedExecution.Trace.nil _
  | step stepped _ ih => exact LoadedExecution.Trace.step (step_sound mode environment region _ _ _ stepped).1 ih

theorem trace_targets (mode : Mode) (environment : Environment) (region : Region)
    {state finish : LoadedExecution.State mode region} {forms : List (Form mode)}
    (trace : Trace mode environment region state forms finish) (model : Execution.State mode)
    (same : StateAgree mode region (LoadedExecution.expand mode region state) model) : Targets mode environment forms model := by
  induction trace generalizing model with
  | nil => trivial
  | @step state finish next form rest stepped tail ih =>
    have checked := step_sound mode environment region state next form stepped
    have one := LoadedExecution.step_sound mode region state next model form same checked.1
    exact ⟨(target_valid_agrees mode environment region form _ model same one.2.1.2.1).mp checked.2.2,
      ih (Execution.execute mode form model) one.2.2⟩

/-- Every accepted combined trace refines live-byte fetch and passes each modeled
memory/address/permission/CALL-target check at the actual successive states. -/
theorem trace_sound (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) {state finish : LoadedExecution.State mode region}
    {forms : List (Form mode)} (trace : Trace mode environment region state forms finish)
    (model : Execution.State mode) (same : StateAgree mode region (LoadedExecution.expand mode region state) model) :
    Fetch.Trace mode model forms (Execution.runForms mode forms model) ∧
      AccessRun mode environment forms model ∧ Targets mode environment forms model ∧
      StateAgree mode region (LoadedExecution.expand mode region finish) (Execution.runForms mode forms model) := by
  have original := LoadedExecution.trace_sound mode region (trace_loaded mode environment region trace) model same
  exact ⟨original.1, access_run_of_safe mode environment region mapping forms model original.2.1,
    trace_targets mode environment region trace model same, original.2.2⟩

end SmcTuring.Native.CheckedExecution
