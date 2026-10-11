module
public import SmcTuring.Turing

public section

namespace SmcTuring.Dolan.Table

structure Entry (alphabet states : Nat) where
  trigger : Fin alphabet
  symbol : Fin alphabet
  direction : Bool
  destination : Fin states
  deriving DecidableEq

/-- The finite list of actual transitions for one state. Undefined transitions
are omitted, so exhausting this list represents a missing TM transition. -/
@[expose] def entries {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) : List (Entry alphabet states) :=
  (List.ofFn (fun symbol : Fin alphabet => symbol)).filterMap fun trigger =>
    (machine.transition state trigger).map fun result =>
      { trigger := trigger, symbol := result.1, direction := result.2.1, destination := result.2.2 }

theorem entries_sound {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (entry : Entry alphabet states) (h : entry ∈ entries machine state) :
    machine.transition state entry.trigger = some (entry.symbol, entry.direction, entry.destination) := by
  rcases List.mem_filterMap.mp h with ⟨trigger, _, mapped⟩
  cases result : machine.transition state trigger with
  | none => simp [result] at mapped
  | some transition =>
    rcases transition with ⟨symbol, direction, destination⟩
    have same : { trigger := trigger, symbol := symbol, direction := direction,
                  destination := destination : Entry alphabet states } = entry := by
      simpa [result] using mapped
    subst entry
    exact result

theorem entries_complete {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (trigger symbol : Fin alphabet) (direction : Bool) (destination : Fin states)
    (h : machine.transition state trigger = some (symbol, direction, destination)) :
    ({ trigger := trigger, symbol := symbol, direction := direction,
       destination := destination : Entry alphabet states }) ∈ entries machine state := by
  apply List.mem_filterMap.mpr
  exact ⟨trigger, List.mem_ofFn.mpr ⟨trigger, rfl⟩, by simp [h]⟩

theorem entries_length {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) : (entries machine state).length ≤ alphabet := by
  simpa [entries] using List.length_filterMap_le
    (fun trigger : Fin alphabet => (machine.transition state trigger).map fun result =>
      ({ trigger := trigger, symbol := result.1, direction := result.2.1,
         destination := result.2.2 : Entry alphabet states }))
    (List.ofFn (fun symbol : Fin alphabet => symbol))

theorem missing_transition_iff {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (trigger : Fin alphabet) :
    machine.transition state trigger = none ↔
      ∀ entry ∈ entries machine state, entry.trigger ≠ trigger := by
  constructor
  · intro missing entry member equal
    have actual := entries_sound machine state entry member
    rw [equal, missing] at actual
    cases actual
  · intro missing
    cases h : machine.transition state trigger with
    | none => rfl
    | some transition =>
      rcases transition with ⟨symbol, direction, destination⟩
      have member := entries_complete machine state trigger symbol direction destination h
      exact False.elim (missing _ member rfl)

end SmcTuring.Dolan.Table
