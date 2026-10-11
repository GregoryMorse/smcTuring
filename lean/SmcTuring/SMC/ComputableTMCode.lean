module
public import SmcTuring.SMC.ComputableSearch
public import Mathlib.Computability.TuringMachine.Config

public section

namespace SmcTuring.SMC.Effective

variable {alphabet states : Nat}

/-- Canonical natural interface to the actual unbounded search. Malformed
encoded finite machine/input descriptions have no result. -/
@[expose] def terminalSearchNat (alphabet states : Nat) (payload : Nat) : Part Nat :=
  Part.bind (Part.ofOption (Encodable.decode (α := SearchInput alphabet states) payload)) fun input =>
    (terminalSearch input.1 input.2).map Encodable.encode

theorem terminal_search_nat_partrec : Nat.Partrec (terminalSearchNat alphabet states) :=
  terminal_search_partrec

theorem terminal_search_nat_encoded (input : SearchInput alphabet states) :
    terminalSearchNat alphabet states (Encodable.encode input) =
      (terminalSearch input.1 input.2).map Encodable.encode := by
  simp [terminalSearchNat, Encodable.encodek]

theorem terminal_search_nat_domain (input : SearchInput alphabet states) :
    (terminalSearchNat alphabet states (Encodable.encode input)).Dom ↔
      TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2) := by
  rw [terminal_search_nat_encoded]
  exact terminal_search_halts input.1 input.2

/-- The vector-input basis certificate is derived from the proved natural
partial-recursion certificate, rather than assumed. -/
theorem terminal_search_vector_partrec : Nat.Partrec' (fun input : List.Vector Nat 1 => terminalSearchNat alphabet states input.head) :=
  Nat.Partrec'.part_iff₁.mpr (Partrec.nat_iff.mpr terminal_search_nat_partrec)

/-- An actual finite library program evaluates the unbounded SMC interpreter
on every encoded finite machine/input descriptor. -/
theorem terminal_search_library_code (alphabet states : Nat) :
    ∃ code : Turing.ToPartrec.Code, ∀ input : List.Vector Nat 1,
      code.eval input.val = (terminalSearchNat alphabet states input.head).map (fun output => [output]) := by
  exact Turing.ToPartrec.Code.exists_code (terminal_search_vector_partrec (alphabet := alphabet) (states := states))

end SmcTuring.SMC.Effective
