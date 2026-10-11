module
public import SmcTuring.Dolan.Transitions
public import SmcTuring.Dolan.Initialization

public section

namespace SmcTuring.Dolan.Table

open Mov Encoding

@[expose] def tableLimit (alphabet states : Nat) : Nat := alphabet + 1 + 5 * (alphabet * states)

/-- Allocate a cursor cell and four body cells for every possible candidate.
Only the candidates in the filtered transition list are used. -/
@[expose] def node {states : Nat} (alphabet : Nat) (state : Fin states) (index : Nat) : Nat :=
  alphabet + 1 + 5 * (index + alphabet * state.val)

@[expose] def cursor {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Nat) : Nat :=
  if index < (entries machine state).length then node alphabet state index else 0

@[expose] def head {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) : Nat := cursor machine state 0

/-- The nine used fields follow the linked-cell layout in Dolan's construction.
The tenth field is unused. A destination stores the head of its state's list. -/
@[expose] def recordWord {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Nat) (entry : Entry alphabet states)
    (component : Nat) (choice : Bool) : Word :=
  match component, choice with
  | 0, false => .address (node alphabet state index + 1)
  | 0, true => .address (cursor machine state (index + 1))
  | 1, false => .address (entry.trigger.val + 1)
  | 1, true => .address (node alphabet state index + 2)
  | 2, false => .address (entry.symbol.val + 1)
  | 2, true => .address (node alphabet state index + 3)
  | 3, false => .offset entry.direction
  | 3, true => .address (node alphabet state index + 4)
  | 4, false => .address (head machine entry.destination)
  | _, _ => .offset false

@[expose] def TableRep {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (memory : Memory) : Prop :=
  ∀ (state : Fin states) (index : Fin (entries machine state).length)
    (component : Fin 5) (choice : Bool),
    memory (node alphabet state index.val + component.val, choice) =
      recordWord machine state index.val (entries machine state)[index.val] component.val choice

/-- A finite table is decoded by division and remainder; the memory generator
queries the supplied finite transition table, never a future machine run. -/
@[expose] def tableMemory {alphabet states : Nat} (machine : TM.Machine alphabet states) : Memory :=
  fun p =>
    if p.1 < alphabet + 1 then .offset false else
      let relative := p.1 - (alphabet + 1)
      let row := relative / 5
      let stateIndex := row / alphabet
      let candidate := row % alphabet
      if h : stateIndex < states then
        let state : Fin states := ⟨stateIndex, h⟩
        match (entries machine state)[candidate]? with
        | none => .offset false
        | some entry => recordWord machine state candidate entry (relative % 5) p.2
      else .offset false

theorem record_coordinates (alphabet state index component : Nat)
    (positive : 0 < alphabet) (hi : index < alphabet) (hc : component < 5) :
    let relative := 5 * (index + alphabet * state) + component
    (relative / 5) / alphabet = state ∧
    (relative / 5) % alphabet = index ∧ relative % 5 = component := by
  have row : (5 * (index + alphabet * state) + component) / 5 = index + alphabet * state := by
    calc
      _ = (component + 5 * (index + alphabet * state)) / 5 := by rw [Nat.add_comm]
      _ = component / 5 + (index + alphabet * state) := Nat.add_mul_div_left _ _ (by decide)
      _ = index + alphabet * state := by simp [Nat.div_eq_of_lt hc]
  dsimp
  rw [row]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ positive]
    simp [Nat.div_eq_of_lt hi]
  · simp [Nat.mod_eq_of_lt hi]
  · simp [Nat.mod_eq_of_lt hc]

theorem node_bounds {alphabet states : Nat} (state : Fin states) (index component : Nat)
    (hi : index < alphabet) (hc : component < 5) :
    alphabet + 1 ≤ node alphabet state index + component ∧
      node alphabet state index + component < tableLimit alphabet states := by
  have row : index + alphabet * state.val < alphabet * states := by
    calc
      _ < alphabet + alphabet * state.val := Nat.add_lt_add_right hi _
      _ = alphabet * (state.val + 1) := by simp [Nat.mul_add, Nat.add_comm]
      _ ≤ alphabet * states := Nat.mul_le_mul_left _ state.isLt
  simp only [node, tableLimit]
  omega

theorem table_memory_correct {alphabet states : Nat} (machine : TM.Machine alphabet states) :
    TableRep machine (tableMemory machine) := by
  intro state index component choice
  have positive : 0 < alphabet := Nat.lt_of_le_of_lt (Nat.zero_le _) machine.blank.isLt
  have hi : index.val < alphabet := Nat.lt_of_lt_of_le index.isLt (entries_length machine state)
  have coords := record_coordinates alphabet state.val index.val component.val positive hi component.isLt
  rcases coords with ⟨hs, hi', hc⟩
  have relative : node alphabet state index.val + component.val - (alphabet + 1) =
      5 * (index.val + alphabet * state.val) + component.val := by
    simp only [node]
    omega
  have notLow : ¬ node alphabet state index.val + component.val < alphabet + 1 :=
    Nat.not_lt.mpr (node_bounds state index.val component.val hi component.isLt).1
  simp [tableMemory, notLow, relative, hs, hi', hc, state.isLt, index.isLt]

@[expose] def tapeLayout (alphabet states : Nat) : Layout alphabet :=
  standardLayout alphabet (5 * (alphabet * states))

theorem tape_above_table (alphabet states : Nat) (position : Int) :
    tableLimit alphabet states ≤ (tapeLayout alphabet states).cell position := by
  simp only [tapeLayout, standardLayout, tableLimit]
  omega

theorem symbols_below_table (alphabet states : Nat) (symbol : Fin alphabet) :
    (tapeLayout alphabet states).symbol symbol < alphabet + 1 := by
  simp only [tapeLayout, standardLayout]
  omega

@[expose] def initialMemory {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) : Memory := fun p =>
  if p.1 < tableLimit alphabet states then tableMemory machine p
  else encodedMemory (5 * (alphabet * states)) c p

theorem initial_table_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) : TableRep machine (initialMemory machine c) := by
  intro state index component choice
  have hi : index.val < alphabet := Nat.lt_of_lt_of_le index.isLt (entries_length machine state)
  have below := (node_bounds state index.val component.val hi component.isLt).2
  simpa [initialMemory, below] using table_memory_correct machine state index component choice

theorem initial_memory_tape_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) :
    MemoryRep (tapeLayout alphabet states) c (initialMemory machine c) := by
  have original : MemoryRep (tapeLayout alphabet states) c
      (encodedMemory (5 * (alphabet * states)) c) := by
    simpa [tapeLayout] using encoded_memory_correct (5 * (alphabet * states)) c
  rcases original with ⟨payload, left, right⟩
  refine ⟨?_, ?_, ?_⟩
  · intro position
    simpa [initialMemory, Nat.not_lt.mpr (tape_above_table alphabet states position)] using payload position
  · intro position hp
    simpa [initialMemory, Nat.not_lt.mpr (tape_above_table alphabet states position)] using left position hp
  · intro position hp
    simpa [initialMemory, Nat.not_lt.mpr (tape_above_table alphabet states position)] using right position hp

theorem node_first {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val, false) = .address (node alphabet state index.val + 1) := by
  simpa [recordWord] using table state index ⟨0, by decide⟩ false

theorem node_next {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val, true) = .address (cursor machine state (index.val + 1)) := by
  simpa [recordWord] using table state index ⟨0, by decide⟩ true

theorem body_trigger {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 1, false) =
      .address ((entries machine state)[index.val].trigger.val + 1) := by
  simpa [recordWord] using table state index ⟨1, by decide⟩ false

theorem body_write_link {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 1, true) = .address (node alphabet state index.val + 2) := by
  simpa [recordWord] using table state index ⟨1, by decide⟩ true

theorem write_symbol {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 2, false) =
      .address ((entries machine state)[index.val].symbol.val + 1) := by
  simpa [recordWord] using table state index ⟨2, by decide⟩ false

theorem write_direction_link {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 2, true) = .address (node alphabet state index.val + 3) := by
  simpa [recordWord] using table state index ⟨2, by decide⟩ true

theorem direction_value {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 3, false) = .offset ((entries machine state)[index.val].direction) := by
  simpa [recordWord] using table state index ⟨3, by decide⟩ false

theorem direction_destination_link {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 3, true) = .address (node alphabet state index.val + 4) := by
  simpa [recordWord] using table state index ⟨3, by decide⟩ true

theorem destination_head {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory)
    (table : TableRep machine memory) (state : Fin states) (index : Fin (entries machine state).length) :
    memory (node alphabet state index.val + 4, false) =
      .address (head machine (entries machine state)[index.val].destination) := by
  simpa [recordWord] using table state index ⟨4, by decide⟩ false

theorem table_rep_frame {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (before after : Memory) (table : TableRep machine before)
    (frame : ∀ p, alphabet + 1 ≤ p.1 → p.1 < tableLimit alphabet states → after p = before p) :
    TableRep machine after := by
  intro state index component choice
  have hi : index.val < alphabet := Nat.lt_of_lt_of_le index.isLt (entries_length machine state)
  have bounds := node_bounds state index.val component.val hi component.isLt
  calc
    after _ = before _ := frame _ bounds.1 bounds.2
    _ = _ := table state index component choice

end SmcTuring.Dolan.Table
