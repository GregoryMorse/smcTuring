module
public import SmcTuring.SMC.ComputableExecution
public import Mathlib.Computability.Partrec

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

variable {alphabet states : Nat}

abbrev SearchInput (alphabet states : Nat) := Prod (TM.FrozenMachine alphabet states) (List (Fin alphabet))

/-- A finite prefix is a successful search result only at the actual terminal
PC. Missing headers and nonterminal states are rejected. -/
@[expose] def terminalPrefix (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) : Option StateCode :=
  ((Concrete.finiteRun machine input count).map stateCode).bind fun state =>
    if state.2.2.1 = zigzag Concrete.terminalPC then some state else none

theorem terminal_prefix_primrec : Primrec₂ (fun input : SearchInput alphabet states => terminalPrefix input.1 input.2) := by
  have machine : Primrec (fun input : Prod (SearchInput alphabet states) Nat => input.1.1) := Primrec.fst.comp Primrec.fst
  have symbols : Primrec (fun input : Prod (SearchInput alphabet states) Nat => input.1.2) := Primrec.snd.comp Primrec.fst
  have prefixResult := concrete_finite_run_primrec.comp (Primrec.pair machine (Primrec.pair symbols Primrec.snd))
  have state : Primrec (fun input : Prod (Prod (SearchInput alphabet states) Nat) StateCode => input.2) := Primrec.snd
  have pc := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp state))
  exact (Primrec.option_bind prefixResult
    (Primrec.ite (Primrec.eq.comp pc (Primrec.const (zigzag Concrete.terminalPC)))
      (Primrec.option_some.comp state) (Primrec.const none)).to₂).of_eq fun input => by rfl

theorem terminal_prefix_some (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) (code : StateCode) :
    terminalPrefix machine input count = some code ↔
      ∃ description, Concrete.finiteRun machine input count = some description ∧
        description.pc = Concrete.terminalPC ∧ stateCode description = code := by
  cases ran : Concrete.finiteRun machine input count with
  | none => simp [terminalPrefix, ran]
  | some description =>
    have pc : (stateCode description).2.2.1 = zigzag description.pc := by rfl
    have same : zigzag description.pc = zigzag Concrete.terminalPC ↔ description.pc = Concrete.terminalPC :=
      Dolan.Encoding.zigzag_injective.eq_iff
    by_cases terminal : description.pc = Concrete.terminalPC <;> simp [terminalPrefix, ran, pc, same, terminal]

theorem terminal_prefix_mem (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) (code : StateCode) :
    code ∈ terminalPrefix machine input count ↔
      ∃ description, Concrete.finiteRun machine input count = some description ∧
        description.pc = Concrete.terminalPC ∧ stateCode description = code := by
  simpa only [Option.mem_def] using terminal_prefix_some machine input count code

/-- Search increasing finite prefixes. The result is the complete coded journal
state; divergence has no result. Both machine and input are finite data. -/
@[expose] def terminalSearch (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) : Part StateCode :=
  Nat.rfindOpt (terminalPrefix machine input)

theorem terminal_search_partrec : Partrec (fun input : SearchInput alphabet states => terminalSearch input.1 input.2) :=
  Partrec.rfindOpt terminal_prefix_primrec.to_comp

theorem terminal_search_domain (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) :
    (terminalSearch machine input).Dom ↔ Concrete.FiniteReachesTerminal machine input := by
  rw [terminalSearch, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨count, code, present⟩
    rcases (terminal_prefix_mem machine input count code).mp present with ⟨description, ran, terminal, _⟩
    exact ⟨count, description, ran, terminal⟩
  · rintro ⟨count, description, ran, terminal⟩
    exact ⟨count, stateCode description, (terminal_prefix_mem machine input count (stateCode description)).mpr ⟨description, ran, terminal, rfl⟩⟩

theorem terminal_search_halts (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) :
    (terminalSearch machine input).Dom ↔ TM.Halts (TM.thaw machine) (TM.initialConfiguration (TM.thaw machine) input) :=
  (terminal_search_domain machine input).trans (Concrete.finite_data_computation machine input).1

theorem terminal_search_diverges (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) :
    ¬ (terminalSearch machine input).Dom ↔ TM.Diverges (TM.thaw machine) (TM.initialConfiguration (TM.thaw machine) input) := by
  rw [terminal_search_halts, TM.diverges_iff_not_halts]

/-- Every returned journal is a genuine terminal prefix of the original SMC
execution, with its complete memory meaning preserved. -/
theorem terminal_search_output (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (code : StateCode)
    (returned : code ∈ terminalSearch machine input) :
    ∃ count, Concrete.finiteRun machine input count = some (decodeState code) ∧
      (decodeState code).pc = Concrete.terminalPC ∧
      runImage 1 Concrete.image count (Concrete.initialTMState (TM.thaw machine) input) =
        some (Finite.meaning (Concrete.initialWords machine input) (decodeState code)) := by
  rcases Nat.rfindOpt_spec returned with ⟨count, present⟩
  rcases (terminal_prefix_mem machine input count code).mp present with ⟨description, ran, terminal, coded⟩
  have decoded : decodeState code = description := by rw [←coded, decode_state_code]
  rw [decoded]
  refine ⟨count, ran, terminal, ?_⟩
  have correct := Concrete.finite_run_correct machine input count
  rw [ran, Option.map_some] at correct
  exact correct.symm

end SmcTuring.SMC.Effective
