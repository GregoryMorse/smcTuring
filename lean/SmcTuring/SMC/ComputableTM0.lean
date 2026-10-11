module
public import SmcTuring.SMC.ComputableTM2

public section

namespace SmcTuring.SMC.Effective

open Turing

variable {alphabet states : Nat}

instance tm2StackFintype : Fintype PartrecToTM2.K' where
  elems := { .main, .rev, .aux, .stack }
  complete stackId := by cases stackId <;> simp

abbrev InterpreterAlphabet := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
abbrev InterpreterTM1Label := TM2to1.Λ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ')

/-- The multi-track alphabet of the TM2-to-TM1 reduction is finite. -/
theorem interpreter_alphabet_finite : Finite InterpreterAlphabet := by infer_instance

/-- The library stack machine starts from exactly the compiled code/input
configuration, using a program-dependent initial label. -/
theorem tm2_code_initial (code : ToPartrec.Code) (input : List Nat) :
    letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
    TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input) = PartrecToTM2.init code input := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  unfold TM2.init PartrecToTM2.init
  congr 1
  funext stackId
  cases stackId <;> rfl

/-- Complete output on the main stack, for every finite library program. -/
theorem tm2_code_eval (code : ToPartrec.Code) (input : List Nat) :
    letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
    TM2.eval PartrecToTM2.tr PartrecToTM2.K'.main (PartrecToTM2.trList input) =
      (code.eval input).map PartrecToTM2.trList := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  unfold TM2.eval
  rw [tm2_code_initial, PartrecToTM2.tr_eval]
  rfl

/-- The actual TM0 reduction has finite control support and halts exactly
when the proved SMC terminal search returns. The input is its finite stack/tape
encoding; no tape or transition oracle is an input. -/
theorem terminal_search_tm0 (alphabet states : Nat) :
    ∃ code : ToPartrec.Code,
      letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
      ∃ support : Finset (TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr)),
        TM0.Supports (TM1to0.tr (TM2to1.tr PartrecToTM2.tr)) (support : Set _) ∧
        (∀ vector : List.Vector Nat 1, code.eval vector.val =
          (terminalSearchNat alphabet states vector.head).map (fun result => [result])) ∧
        ∀ input : SearchInput alphabet states,
          (TM0.eval (TM1to0.tr (TM2to1.tr PartrecToTM2.tr))
            (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input]))).Dom ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2) := by
  obtain ⟨code, computed⟩ := terminal_search_library_code alphabet states
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  have support2 := PartrecToTM2.tr_supports code .halt
  have support1 := TM2to1.tr_supports PartrecToTM2.tr support2
  have support0 := TM1to0.tr_supports (TM2to1.tr PartrecToTM2.tr) support1
  refine ⟨code, TM1to0.trStmts (TM2to1.tr PartrecToTM2.tr) (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp code .halt)), support0, computed, ?_⟩
  intro input
  rw [TM1to0.tr_eval]
  have program := computed (⟨[Encodable.encode input], rfl⟩ : List.Vector Nat 1)
  change code.eval [Encodable.encode input] =
    (terminalSearchNat alphabet states (Encodable.encode input)).map (fun output => [output]) at program
  have stackDomain :
      (TM2.eval PartrecToTM2.tr PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])).Dom ↔
        (code.eval [Encodable.encode input]).Dom :=
    Iff.of_eq (congrArg Part.Dom (tm2_code_eval code [Encodable.encode input]))
  have programDomain : (code.eval [Encodable.encode input]).Dom ↔
      (terminalSearchNat alphabet states (Encodable.encode input)).Dom := Iff.of_eq (congrArg Part.Dom program)
  exact (TM2to1.tr_eval_dom PartrecToTM2.tr PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])).trans
    (stackDomain.trans (programDomain.trans (terminal_search_nat_domain input)))

/-- Tape output of the actual TM0 reduction retains the complete encoded
terminal journal on its main track. -/
theorem tm0_terminal_output (code : ToPartrec.Code) (alphabet states : Nat)
    (computed : ∀ input : List.Vector Nat 1,
      code.eval input.val = (terminalSearchNat alphabet states input.head).map (fun output => [output])) :
    letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
    ∀ (input : SearchInput alphabet states) (output : ListBlank InterpreterAlphabet),
      output ∈ TM0.eval (TM1to0.tr (TM2to1.tr PartrecToTM2.tr))
        (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])) →
      ∃ journal : StateCode, journal ∈ terminalSearch input.1 input.2 ∧
        ∃ tracks : ListBlank (PartrecToTM2.K' -> Option PartrecToTM2.Γ'),
          TM2to1.addBottom tracks = output ∧
          tracks.map ((PointedMap.mk (fun row : PartrecToTM2.K' -> Option PartrecToTM2.Γ' => row .main) rfl)) =
            ListBlank.mk ((PartrecToTM2.trList [Encodable.encode journal]).map some).reverse := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  intro input output returned
  have tapePresent : output ∈ TM1.eval (TM2to1.tr PartrecToTM2.tr)
      (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])) := by
    rw [←TM1to0.tr_eval]
    exact returned
  have stackDom := (TM2to1.tr_eval_dom PartrecToTM2.tr PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])).mp tapePresent.1
  obtain ⟨stackOutput, stackPresent⟩ := Part.dom_iff_mem.mp stackDom
  have stackCoded : stackOutput ∈ (code.eval [Encodable.encode input]).map PartrecToTM2.trList := by
    rw [←tm2_code_eval]
    exact stackPresent
  rcases (Part.mem_map_iff _).mp stackCoded with ⟨numbers, numbersPresent, stackEq⟩
  have program := computed (⟨[Encodable.encode input], rfl⟩ : List.Vector Nat 1)
  change code.eval [Encodable.encode input] = (terminalSearchNat alphabet states (Encodable.encode input)).map (fun n => [n]) at program
  rw [program] at numbersPresent
  rcases (Part.mem_map_iff _).mp numbersPresent with ⟨naturalOutput, naturalPresent, numbersEq⟩
  rw [terminal_search_nat_encoded] at naturalPresent
  rcases (Part.mem_map_iff _).mp naturalPresent with ⟨journal, journalPresent, naturalEq⟩
  rcases TM2to1.tr_eval PartrecToTM2.tr PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input]) tapePresent stackPresent with
    ⟨heapStacks, tracks, outputEq, projectionEq, mainEq⟩
  refine ⟨journal, journalPresent, tracks, outputEq, ?_⟩
  have target := projectionEq PartrecToTM2.K'.main
  rw [mainEq, ←stackEq, ←numbersEq, ←naturalEq] at target
  exact target

/-- A returned terminal state necessarily comes after positive SMC progress. -/
theorem terminal_search_positive_progress (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet))
    (journal : StateCode) (returned : journal ∈ terminalSearch machine input) :
    ∃ count, 0 < count ∧ Concrete.finiteRun machine input count = some (decodeState journal) := by
  rcases terminal_search_output machine input journal returned with ⟨count, ran, terminal, _⟩
  refine ⟨count, ?_, ran⟩
  cases count with
  | zero =>
    have initial : Concrete.initialDescription = decodeState journal := Option.some.inj ran
    rw [←initial] at terminal
    change (264 : Int) = 1000000 at terminal
    omega
  | succ count => omega

/-- One fixed finite-support TM0 program gives both the exact halting domain
and recovery of the complete terminal SMC journal for every finite input. -/
theorem terminal_search_tm0_with_output (alphabet states : Nat) :
    ∃ code : ToPartrec.Code,
      letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
      ∃ support : Finset (TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr)),
        TM0.Supports (TM1to0.tr (TM2to1.tr PartrecToTM2.tr)) (support : Set _) ∧
        ∀ input : SearchInput alphabet states,
          ((TM0.eval (TM1to0.tr (TM2to1.tr PartrecToTM2.tr))
            (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input]))).Dom ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          ∀ output : ListBlank InterpreterAlphabet,
            output ∈ TM0.eval (TM1to0.tr (TM2to1.tr PartrecToTM2.tr))
              (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])) →
            ∃ journal : StateCode, journal ∈ terminalSearch input.1 input.2 ∧
              ∃ tracks : ListBlank (PartrecToTM2.K' -> Option PartrecToTM2.Γ'),
                TM2to1.addBottom tracks = output ∧
                tracks.map (PointedMap.mk (fun row : PartrecToTM2.K' -> Option PartrecToTM2.Γ' => row .main) rfl) =
                  ListBlank.mk ((PartrecToTM2.trList [Encodable.encode journal]).map some).reverse := by
  obtain ⟨code, support, supported, computed, domain⟩ := terminal_search_tm0 alphabet states
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  refine ⟨code, support, supported, ?_⟩
  intro input
  exact ⟨domain input, tm0_terminal_output code alphabet states computed input⟩

end SmcTuring.SMC.Effective
