module
public import SmcTuring.SMC.ComputableTM0
public import SmcTuring.MathlibTM0.Numbering

public section

namespace SmcTuring.SMC.Effective

open Turing

variable {alphabet states alphabetCount labelCount : Nat}

/-- The interpreter receives only the finite encoded table/input descriptor. -/
@[expose] def searchTape (input : SearchInput alphabet states) : List InterpreterAlphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])

/-- The numbered output carries the complete returned journal on its main track. -/
@[expose] def JournalOutput [Inhabited (Fin alphabetCount)]
    (symbols : InterpreterAlphabet ≃ Fin alphabetCount) (blank : symbols default = default)
    (journal : StateCode) (output : ListBlank (Fin alphabetCount)) : Prop :=
  ∃ tracks : ListBlank (PartrecToTM2.K' -> Option PartrecToTM2.Γ'),
    (TM2to1.addBottom tracks).map (MathlibTM0.Numbering.symbolMap symbols blank) = output ∧
    tracks.map (PointedMap.mk (fun row : PartrecToTM2.K' -> Option PartrecToTM2.Γ' => row .main) rfl) =
      ListBlank.mk ((PartrecToTM2.trList [Encodable.encode journal]).map some).reverse

/-- Literal finite alphabet/labels, supplied defaults, exact halting domain and
full journal output. The numbered transition table is fixed before the input. -/
theorem terminal_search_numbered_tm0 (alphabet states : Nat) :
    ∃ (alphabetCount labelCount : Nat) (symbols : InterpreterAlphabet ≃ Fin alphabetCount)
      (start : Fin labelCount),
      letI : Inhabited (Fin alphabetCount) := ⟨symbols default⟩
      letI : Inhabited (Fin labelCount) := ⟨start⟩
      ∃ numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount),
        ∀ input : SearchInput alphabet states,
          ((TM0.eval numbered ((searchTape input).map symbols)).Dom ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          ∀ output : ListBlank (Fin alphabetCount),
            output ∈ TM0.eval numbered ((searchTape input).map symbols) ->
            ∃ journal : StateCode, journal ∈ terminalSearch input.1 input.2 ∧
              JournalOutput symbols rfl journal output := by
  classical
  obtain ⟨code, support, supported, contract⟩ := terminal_search_tm0_with_output alphabet states
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  let originalMachine := TM1to0.tr (TM2to1.tr PartrecToTM2.tr)
  let : Inhabited (MathlibTM0.FiniteSupport.Labels support) :=
    MathlibTM0.FiniteSupport.labelInhabited originalMachine support supported
  let symbols := Fintype.equivFin InterpreterAlphabet
  let labels := Fintype.equivFin (MathlibTM0.FiniteSupport.Labels support)
  let : Inhabited (Fin (Fintype.card InterpreterAlphabet)) := ⟨symbols default⟩
  let : Inhabited (Fin (Fintype.card (MathlibTM0.FiniteSupport.Labels support))) := ⟨labels default⟩
  let restricted := MathlibTM0.FiniteSupport.restrict originalMachine support supported
  let numbered := MathlibTM0.Numbering.transport restricted symbols rfl labels
  refine ⟨_, _, symbols, labels default, numbered, ?_⟩
  intro input
  have originalContract := contract input
  have restrictedOutput := MathlibTM0.FiniteSupport.eval_eq originalMachine support supported rfl (searchTape input)
  have numberedOutput := MathlibTM0.Numbering.eval_eq restricted symbols rfl labels rfl (searchTape input)
  rw [restrictedOutput] at numberedOutput
  have domain : (TM0.eval numbered ((searchTape input).map symbols)).Dom ↔
      (TM0.eval originalMachine (searchTape input)).Dom := Iff.of_eq (congrArg Part.Dom numberedOutput)
  refine ⟨domain.trans originalContract.1, ?_⟩
  intro output returned
  rw [numberedOutput] at returned
  rcases (Part.mem_map_iff _).mp returned with ⟨originalOutput, originalReturned, outputEq⟩
  rcases originalContract.2 originalOutput originalReturned with ⟨journal, journalReturned, tracks, tracksEq, mainEq⟩
  refine ⟨journal, journalReturned, tracks, ?_, mainEq⟩
  exact (congrArg (fun result => result.map (MathlibTM0.Numbering.symbolMap symbols rfl)) tracksEq).trans outputEq

/-- The fixed pure SMC compiler starts from the numbered finite input. -/
@[expose] def numberedInitial [Inhabited (Fin alphabetCount)] [Inhabited (Fin labelCount)]
    (numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount))
    (symbols : InterpreterAlphabet ≃ Fin alphabetCount) (input : SearchInput alphabet states) : State :=
  Concrete.initialTMState (MathlibTM0.compile numbered) ((searchTape input).map symbols)

/-- The actual partial-recursive terminal-search interpreter composes with the
checked finite-label TM0/source/SMC adapters. It preserves both divergence and
complete terminal-journal output in the fixed pure instruction image. -/
theorem terminal_search_pure_smc (alphabet states : Nat) :
    ∃ (alphabetCount labelCount : Nat) (symbols : InterpreterAlphabet ≃ Fin alphabetCount)
      (start : Fin labelCount),
      letI : Inhabited (Fin alphabetCount) := ⟨symbols default⟩
      letI : Inhabited (Fin labelCount) := ⟨start⟩
      ∃ numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount),
        ∀ input : SearchInput alphabet states,
          (Concrete.ReachesTerminal (numberedInitial numbered symbols input) ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          (Concrete.RunsForever (numberedInitial numbered symbols input) ↔
            TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          Concrete.PureComputation (numberedInitial numbered symbols input) ∧
          (TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2) ->
            Concrete.InfinitelyChanges (numberedInitial numbered symbols input)) ∧
          ∀ (count : Nat) (finish : State),
            runImage 1 Concrete.image count (numberedInitial numbered symbols input) = some finish ->
            finish.pc = Concrete.terminalPC ->
            ∃ (journal : StateCode) (library : TM0.Cfg (Fin alphabetCount) (Fin labelCount))
              (source : TM.Configuration alphabetCount (2 * labelCount)),
              journal ∈ terminalSearch input.1 input.2 ∧
              JournalOutput symbols rfl journal library.Tape.right₀ ∧
              MathlibTM0.Rep library source ∧ Concrete.TapeWords source finish := by
  obtain ⟨alphabetCount, labelCount, symbols, start, numbered, contract⟩ := terminal_search_numbered_tm0 alphabet states
  let : Inhabited (Fin alphabetCount) := ⟨symbols default⟩
  let : Inhabited (Fin labelCount) := ⟨start⟩
  refine ⟨alphabetCount, labelCount, symbols, start, numbered, ?_⟩
  intro input
  have computed := contract input
  have simulated := MathlibTM0.fixed_smc_mathlib_simulation numbered ((searchTape input).map symbols)
  have divergence := TM.diverges_iff_not_halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)
  refine ⟨simulated.1.trans computed.1,
    simulated.2.1.trans ((not_congr computed.1).trans divergence.symm), simulated.2.2.1,
    (fun diverges => simulated.2.2.2 ((not_congr computed.1).mpr (divergence.mp diverges))), ?_⟩
  intro count finish reached terminal
  rcases MathlibTM0.standard_terminal_output numbered ((searchTape input).map symbols) count finish reached terminal with
    ⟨library, source, output, represented, words, _⟩
  rcases computed.2 library.Tape.right₀ output with ⟨journal, returned, journalOutput⟩
  exact ⟨journal, library, source, returned, journalOutput, represented, words⟩

end SmcTuring.SMC.Effective
