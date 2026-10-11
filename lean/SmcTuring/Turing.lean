module
public import SmcTuring.Memory

public section

namespace SmcTuring.TM

/-- A standard finite-alphabet, finite-state, two-sided Turing machine.
Each transition writes one symbol, moves one place, and chooses a new state.
None means halt. The finite indices supply effective enumerations. -/
structure Machine (alphabet states : Nat) where
  blank : Fin alphabet
  start : Fin states
  transition : Fin states → Fin alphabet → Option (Fin alphabet × Bool × Fin states)

structure Configuration (alphabet states : Nat) where
  state : Fin states
  head : Int
  tape : Int → Fin alphabet

@[expose] def step {alphabet states : Nat} (machine : Machine alphabet states)
    (c : Configuration alphabet states) : Option (Configuration alphabet states) :=
  match machine.transition c.state (c.tape c.head) with
  | none => none
  | some (symbol, right, state) =>
    some { state := state
           head := if right then c.head + 1 else c.head - 1
           tape := write c.tape c.head symbol }

/-- A finite input is placed to the right of head zero; all other cells are blank. -/
@[expose] def initialConfiguration {alphabet states : Nat} (machine : Machine alphabet states)
    (input : List (Fin alphabet)) : Configuration alphabet states :=
  { state := machine.start
    head := 0
    tape := fun position => if position < 0 then machine.blank
            else (input[position.toNat]?).getD machine.blank }

@[expose] def run {alphabet states : Nat} (machine : Machine alphabet states) :
    Nat → Configuration alphabet states → Option (Configuration alphabet states)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (run machine n)

/-- Halting is a missing transition reached after finitely many actual steps. -/
@[expose] def Halts {alphabet states : Nat} (machine : Machine alphabet states)
    (start : Configuration alphabet states) : Prop :=
  ∃ n finish, run machine n start = some finish ∧ step machine finish = none

/-- Infinite computation is defined through every finite prefix, not by
selecting a separate finite-memory hardware instance for each prefix. -/
@[expose] def Diverges {alphabet states : Nat} (machine : Machine alphabet states)
    (start : Configuration alphabet states) : Prop :=
  ∀ n, ∃ finish, run machine n start = some finish

theorem missing_transition_halts {alphabet states : Nat} (machine : Machine alphabet states)
    (c : Configuration alphabet states)
    (h : machine.transition c.state (c.tape c.head) = none) :
    step machine c = none := by
  simp [step, h]

theorem transition_correct {alphabet states : Nat} (machine : Machine alphabet states)
    (c : Configuration alphabet states) (symbol : Fin alphabet) (right : Bool) (state : Fin states)
    (h : machine.transition c.state (c.tape c.head) = some (symbol, right, state)) :
    step machine c = some { state := state
                            head := if right then c.head + 1 else c.head - 1
                            tape := write c.tape c.head symbol } := by
  simp [step, h]

theorem initialized_negative_blank {alphabet states : Nat} (machine : Machine alphabet states)
    (input : List (Fin alphabet)) (position : Int) (h : position < 0) :
    (initialConfiguration machine input).tape position = machine.blank := by
  simp [initialConfiguration, h]

theorem run_add {alphabet states : Nat} (machine : Machine alphabet states)
    (first second : Nat) (c : Configuration alphabet states) :
    run machine (first + second) c = (run machine first c).bind (run machine second) := by
  induction first generalizing c with
  | zero => simp [run]
  | succ first ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases step machine c <;> simp [ih]

/-- An already halted configuration cannot execute a positive number of steps. -/
theorem run_halted {alphabet states : Nat} (machine : Machine alphabet states)
    (c : Configuration alphabet states) (h : step machine c = none) (n : Nat) :
    run machine (n + 1) c = none := by
  simp [run, h]

theorem halt_not_diverge {alphabet states : Nat} (machine : Machine alphabet states)
    (start : Configuration alphabet states) (h : Halts machine start) :
    ¬ Diverges machine start := by
  rcases h with ⟨n, finish, hn, hs⟩
  intro infinite
  rcases infinite (n + 1) with ⟨later, hl⟩
  rw [run_add, hn] at hl
  simp [run, hs] at hl

/-- A failed finite prefix already contains a reached halting configuration. -/
theorem run_failure_halts {alphabet states : Nat} (machine : Machine alphabet states)
    (n : Nat) (start : Configuration alphabet states) (h : run machine n start = none) :
    Halts machine start := by
  induction n generalizing start with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step machine start with
    | none => exact ⟨0, start, rfl, hs⟩
    | some next =>
      have hn : run machine n next = none := by simpa [run, hs] using h
      rcases ih next hn with ⟨k, finish, hk, hf⟩
      exact ⟨k + 1, finish, by simpa [run, hs] using hk, hf⟩

theorem diverges_iff_not_halts {alphabet states : Nat} (machine : Machine alphabet states)
    (start : Configuration alphabet states) :
    Diverges machine start ↔ ¬ Halts machine start := by
  constructor
  · intro infinite halted
    exact halt_not_diverge machine start halted infinite
  · intro notHalted n
    cases h : run machine n start with
    | none => exact False.elim (notHalted (run_failure_halts machine n start h))
    | some finish => exact ⟨finish, rfl⟩

end SmcTuring.TM
