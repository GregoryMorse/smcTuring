module
public import SmcTuring.MathlibTM0.FiniteSupport

public section

namespace SmcTuring.MathlibTM0.Numbering

open Turing

variable {Symbol Label NewSymbol NewLabel : Type}
  [Inhabited Symbol] [Inhabited Label] [Inhabited NewSymbol] [Inhabited NewLabel]

/-- Encode the alphabet while explicitly preserving its blank. -/
@[expose] def symbolMap (symbols : Symbol ≃ NewSymbol)
    (blank : symbols default = default) : PointedMap Symbol NewSymbol := ⟨symbols, blank⟩

/-- Decode the alphabet with the same blank convention. -/
@[expose] def symbolInverse (symbols : Symbol ≃ NewSymbol)
    (blank : symbols default = default) : PointedMap NewSymbol Symbol :=
  ⟨symbols.symm, by rw [←blank]; exact symbols.symm_apply_apply _⟩

/-- Finite renumbering changes only the symbol/label names. -/
@[expose] def transport (machine : TM0.Machine Symbol Label)
    (symbols : Symbol ≃ NewSymbol) (blank : symbols default = default)
    (labels : Label ≃ NewLabel) : TM0.Machine NewSymbol NewLabel :=
  machine.map (symbolMap symbols blank) (symbolInverse symbols blank) labels labels.symm

variable (machine : TM0.Machine Symbol Label)
  (symbols : Symbol ≃ NewSymbol) (blank : symbols default = default)
  (labels : Label ≃ NewLabel) (initial : labels default = default)

include initial

/-- The library's exact machine mapping gives positive transition refinement. -/
theorem transport_respects :
    StateTransition.Respects (TM0.step machine) (TM0.step (transport machine symbols blank labels))
      (fun original numbered => original.map (symbolMap symbols blank) labels = numbered) := by
  simpa only [Set.mem_univ, true_and, transport] using
    TM0.Machine.map_respects machine (symbolMap symbols blank) (symbolInverse symbols blank)
      (PointedMap.mk labels initial) labels.symm (TM0.univ_supports machine)
      (fun symbol => symbols.symm_apply_apply symbol) (fun label _ => labels.symm_apply_apply label)

/-- Evaluation retains the complete two-sided tape, beyond the observed right tail. -/
theorem configuration_eval (configuration : TM0.Cfg Symbol Label) :
    StateTransition.eval (TM0.step (transport machine symbols blank labels))
        (configuration.map (symbolMap symbols blank) labels) =
      (StateTransition.eval (TM0.step machine) configuration).map
        (TM0.Cfg.map (symbolMap symbols blank) labels) :=
  StateTransition.tr_eval' _ _ _ (transport_respects machine symbols blank labels initial) configuration

/-- The numbered initial configuration corresponds to the supplied start and blank. -/
theorem initial_encoding (input : List Symbol) :
    (TM0.init input : TM0.Cfg Symbol Label).map (symbolMap symbols blank) labels =
      (TM0.init (input.map symbols) : TM0.Cfg NewSymbol NewLabel) :=
  TM0.map_init (symbolMap symbols blank) (PointedMap.mk labels initial) input

omit initial [Inhabited Label] [Inhabited NewLabel] in
/-- The library's output observation commutes with alphabet encoding. -/
theorem right_output (configuration : TM0.Cfg Symbol Label) :
    (configuration.map (symbolMap symbols blank) labels).Tape.right₀ =
      configuration.Tape.right₀.map (symbolMap symbols blank) := by
  simp only [TM0.Cfg.map, Tape.map, Tape.right₀, ListBlank.map_cons]

/-- Exact partial tape output after renumbering; both halting and data are retained. -/
theorem eval_eq (input : List Symbol) :
    TM0.eval (transport machine symbols blank labels) (input.map symbols) =
      (TM0.eval machine input).map (fun output => output.map (symbolMap symbols blank)) := by
  unfold TM0.eval
  rw [←initial_encoding symbols blank labels initial input, configuration_eval machine symbols blank labels initial]
  simp only [Part.map_map]
  exact congrArg (fun observe => (StateTransition.eval (TM0.step machine) (TM0.init input)).map observe)
    (funext fun configuration => right_output symbols blank labels configuration)

end SmcTuring.MathlibTM0.Numbering
