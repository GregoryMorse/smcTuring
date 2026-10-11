module
public import SmcTuring.MathlibTM0.Simulation
public import Mathlib.Data.Fintype.EquivFin

public section

namespace SmcTuring.MathlibTM0.FiniteSupport

open Turing

variable {Symbol Label : Type*} [Inhabited Symbol] [Inhabited Label]

abbrev Labels (support : Finset Label) := {label : Label // label ∈ support}

omit [Inhabited Label] in
/-- Only the supported control labels occur in the restricted machine. -/
theorem labels_finite (support : Finset Label) : Finite (Labels support) := by infer_instance

omit [Inhabited Label] in
theorem labels_card (support : Finset Label) : Fintype.card (Labels support) = support.card := by
  simp [Labels]

/-- The original initial label belongs to the finite support. -/
@[expose, instance_reducible] def labelInhabited (machine : TM0.Machine Symbol Label)
    (support : Finset Label) (supported : TM0.Supports machine (support : Set Label)) :
    Inhabited (Labels support) := ⟨⟨default, supported.1⟩⟩

variable (machine : TM0.Machine Symbol Label) (support : Finset Label)
    (supported : TM0.Supports machine (support : Set Label))

section
variable [Inhabited (Labels support)]

/-- Restrict every transition to its proved finite domain and codomain. -/
@[expose] def restrict : TM0.Machine Symbol (Labels support) :=
  fun label symbol => match selected : machine label.val symbol with
    | none => none
    | some (next, statement) => some (⟨next, supported.2 selected label.property⟩, statement)

/-- Forget the finite label witness; preserve the entire tape. -/
@[expose] def embed (configuration : TM0.Cfg Symbol (Labels support)) : TM0.Cfg Symbol Label :=
  ⟨configuration.q.val, configuration.Tape⟩

/-- Every restricted step is exactly the original step, including a halt. -/
theorem step_embedding (configuration : TM0.Cfg Symbol (Labels support)) :
    (TM0.step (restrict machine support supported) configuration).map (embed support) =
      TM0.step machine (embed support configuration) := by
  rcases configuration with ⟨label, tape⟩
  unfold TM0.step restrict embed
  dsimp only
  split
  · rename_i selected
    rw [selected]
    rfl
  · rename_i next statement selected
    dsimp only [Option.map]
    rw [selected]

/-- Successful transitions give one actual step, hence positive progress. -/
theorem restrict_respects :
    StateTransition.Respects (TM0.step (restrict machine support supported)) (TM0.step machine)
      (fun restricted original => embed support restricted = original) := by
  apply StateTransition.fun_respects.mpr
  intro configuration
  have exactStep := step_embedding machine support supported configuration
  cases selected : TM0.step (restrict machine support supported) configuration with
  | none =>
    change TM0.step machine (embed support configuration) = none
    simpa [selected] using exactStep.symm
  | some next =>
    change StateTransition.Reaches₁ (TM0.step machine) (embed support configuration) (embed support next)
    exact Relation.TransGen.single (by simpa [selected] using exactStep.symm)

/-- Restriction preserves partial evaluation and the complete terminal configuration. -/
theorem configuration_eval (configuration : TM0.Cfg Symbol (Labels support)) :
    StateTransition.eval (TM0.step machine) (embed support configuration) =
      (StateTransition.eval (TM0.step (restrict machine support supported)) configuration).map (embed support) :=
  StateTransition.tr_eval' _ _ _ (restrict_respects machine support supported) configuration

/-- A restricted default chosen from the support embeds to the original default. -/
theorem initial_embedding (initial : (default : Labels support).val = (default : Label)) (input : List Symbol) :
    embed support (TM0.init input) = (TM0.init input : TM0.Cfg Symbol Label) := by
  unfold embed TM0.init
  rw [initial]

/-- Exact partial output, with the supplied blank and initial label preserved. -/
theorem eval_eq (initial : (default : Labels support).val = (default : Label)) (input : List Symbol) :
    TM0.eval (restrict machine support supported) input = TM0.eval machine input := by
  unfold TM0.eval
  rw [←initial_embedding support initial input, configuration_eval machine support supported]
  rfl

end
end SmcTuring.MathlibTM0.FiniteSupport
