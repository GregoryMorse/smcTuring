module
public import SmcTuring.SMC.ComputableTMCode
public import Mathlib.Computability.TuringMachine.ToPartrec

public section

namespace SmcTuring.SMC.Effective

open Turing

variable {alphabet states : Nat}

/-- The library evaluator uses a finite four-symbol stack alphabet. -/
theorem tm2_alphabet_finite : Finite PartrecToTM2.Γ' := by infer_instance

/-- Its local storage is one optional symbol, not an unbounded internal variable. -/
theorem tm2_local_storage_finite : Finite (Option PartrecToTM2.Γ') := by infer_instance

/-- The four stack identifiers are exhaustively enumerated. -/
theorem tm2_stacks_enumerated (stackId : PartrecToTM2.K') :
    stackId ∈ [PartrecToTM2.K'.main, .rev, .aux, .stack] := by
  cases stackId <;> simp

/-- For each fixed library program, its reachable label support is genuinely
finite even though the ambient datatype describes all possible programs. -/
theorem tm2_control_support_finite (code : ToPartrec.Code) :
    Finite { label : PartrecToTM2.Λ' // label ∈ PartrecToTM2.codeSupp code .halt } := by infer_instance

/-- The actual library TM2 evaluates the proved unbounded interpreter. The
certificate includes the starting label and closure of its finite control set. -/
theorem terminal_search_tm2 (alphabet states : Nat) :
    ∃ code : ToPartrec.Code,
      PartrecToTM2.trNormal code .halt ∈ PartrecToTM2.codeSupp code .halt ∧
      (∀ label ∈ PartrecToTM2.codeSupp code .halt,
        TM2.SupportsStmt (PartrecToTM2.codeSupp code .halt) (PartrecToTM2.tr label)) ∧
      ∀ input : List.Vector Nat 1,
        StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init code input.val) =
          (terminalSearchNat alphabet states input.head).map (fun output => PartrecToTM2.halt [output]) := by
  obtain ⟨code, computed⟩ := terminal_search_library_code alphabet states
  have supported := PartrecToTM2.tr_supports code .halt
  refine ⟨code, supported.1, supported.2, ?_⟩
  intro input
  rw [PartrecToTM2.tr_eval, computed input]
  rfl

/-- Every operational library-code step has a positive finite TM2 simulation,
using the actual compiler relation. -/
theorem tm2_compiler_positive_steps :
    StateTransition.Respects ToPartrec.step (TM2.step PartrecToTM2.tr) PartrecToTM2.TrCfg :=
  PartrecToTM2.tr_respects

/-- Entering the compiled interpreter entails at least one actual TM2 step. -/
theorem tm2_compiler_initial_progress (code : ToPartrec.Code) (input : List Nat) :
    ∃ finish : PartrecToTM2.Cfg', StateTransition.Reaches₁ (TM2.step PartrecToTM2.tr) (PartrecToTM2.init code input) finish := by
  obtain ⟨finish, _, progressed⟩ := PartrecToTM2.tr_init code input
  exact ⟨finish, progressed⟩

end SmcTuring.SMC.Effective
