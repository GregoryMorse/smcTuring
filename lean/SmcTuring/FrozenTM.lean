module
public import SmcTuring.Turing

public section

namespace SmcTuring.TM

/-- A TM's entire external input is finite data, with no transition function
oracle. Short or absent rows denote missing transitions. -/
structure FrozenMachine (alphabet states : Nat) where
  blank : Fin alphabet
  start : Fin states
  table : List (List (Option (Fin alphabet × Bool × Fin states)))

@[expose] def freeze {alphabet states : Nat} (machine : Machine alphabet states) : FrozenMachine alphabet states :=
  { blank := machine.blank, start := machine.start,
    table := List.ofFn fun state : Fin states => List.ofFn fun symbol : Fin alphabet => machine.transition state symbol }

@[expose] def thaw {alphabet states : Nat} (machine : FrozenMachine alphabet states) : Machine alphabet states :=
  { blank := machine.blank, start := machine.start,
    transition := fun state symbol => (((machine.table[state.val]?).getD [])[symbol.val]?).getD none }

theorem freeze_transition {alphabet states : Nat} (machine : Machine alphabet states) (state : Fin states) (symbol : Fin alphabet) :
    (thaw (freeze machine)).transition state symbol = machine.transition state symbol := by
  simp [freeze, thaw]

theorem thaw_freeze {alphabet states : Nat} (machine : Machine alphabet states) : thaw (freeze machine) = machine := by
  have same : (thaw (freeze machine)).transition = machine.transition :=
    funext fun state => funext fun symbol => freeze_transition machine state symbol
  cases machine with
  | mk blank start transition =>
    change ({ blank := blank, start := start, transition := _ } : Machine alphabet states) =
      { blank := blank, start := start, transition := transition }
    congr 1

theorem freeze_rows {alphabet states : Nat} (machine : Machine alphabet states) : (freeze machine).table.length = states := by
  simp [freeze]

theorem freeze_columns {alphabet states : Nat} (machine : Machine alphabet states) (state : Fin states) :
    (((freeze machine).table[state.val]?).getD []).length = alphabet := by
  simp [freeze]

end SmcTuring.TM
