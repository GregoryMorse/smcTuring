module
public import SmcTuring.Dolan.TableLayout
public import SmcTuring.Dolan.Frames
public import SmcTuring.Dolan.Programs

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

@[expose] def loadCandidateProgram : List Instruction :=
  [.load .x .transition .zero, .load .x .x .zero, .load .y .current .zero]

@[expose] def candidateInput (s : State) (trigger symbol : Nat) : State :=
  { s with registers := write (write s.registers .x (.address trigger)) .y (.address symbol) }

theorem load_candidate_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Fin (entries machine c.state).length) (s : State)
    (table : TableRep machine s.memory) (tape : TapeRep (tapeLayout alphabet states) c s)
    (ht : s.registers .transition = .address (node alphabet c.state index.val))
    (h0 : s.registers .zero = .offset false) :
    run loadCandidateProgram s = some (candidateInput s
      ((entries machine c.state)[index.val].trigger.val + 1) ((c.tape c.head).val + 1)) := by
  have hs := tape.1.1
  have payload := tape.2.1 c.head
  simp only [tapeLayout, standardLayout] at hs payload
  have first := node_first machine s.memory table c.state index
  have trigger := body_trigger machine s.memory table c.state index
  simp [loadCandidateProgram, candidateInput, run, execute, address, write, ht, hs, h0,
    first, trigger, payload]
  all_goals
    funext r
    by_cases hx : r = .x <;> by_cases hy : r = .y <;> simp_all [write]

@[expose] def loadSymbolProgram : List Instruction :=
  [.load .y .transition .zero, .load .y .y .one, .load .y .y .zero]

@[expose] def symbolInput (s : State) (symbol : Nat) : State :=
  { s with registers := write s.registers .y (.address symbol) }

theorem load_symbol_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length) (s : State)
    (table : TableRep machine s.memory)
    (ht : s.registers .transition = .address (node alphabet state index.val))
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true) :
    run loadSymbolProgram s = some (symbolInput s ((entries machine state)[index.val].symbol.val + 1)) := by
  have first := node_first machine s.memory table state index
  have link := body_write_link machine s.memory table state index
  have symbol := write_symbol machine s.memory table state index
  simp [loadSymbolProgram, symbolInput, run, execute, address, write, ht, h0, h1, first, link, symbol]

@[expose] def loadDirectionProgram : List Instruction :=
  [.load .direction .transition .zero, .load .direction .direction .one,
   .load .direction .direction .one, .load .direction .direction .zero]

@[expose] def directionInput (s : State) (direction : Bool) : State :=
  { s with registers := write s.registers .direction (.offset direction) }

theorem load_direction_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length) (s : State)
    (table : TableRep machine s.memory)
    (ht : s.registers .transition = .address (node alphabet state index.val))
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true) :
    run loadDirectionProgram s = some (directionInput s (entries machine state)[index.val].direction) := by
  have first := node_first machine s.memory table state index
  have link := body_write_link machine s.memory table state index
  have next := write_direction_link machine s.memory table state index
  have direction := direction_value machine s.memory table state index
  simp [loadDirectionProgram, directionInput, run, execute, address, write, ht, h0, h1,
    first, link, next, direction]

/-- Read the next candidate and the destination-state list before selecting.
The choice is the symbol-comparison flag; no conditional branch is emitted. -/
@[expose] def loadCursorChoicesProgram : List Instruction :=
  [.load .x .transition .one, .load .y .transition .zero,
   .load .y .y .one, .load .y .y .one, .load .y .y .one, .load .y .y .zero]

theorem load_cursor_choices_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length) (s : State)
    (table : TableRep machine s.memory)
    (ht : s.registers .transition = .address (node alphabet state index.val))
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true) :
    run loadCursorChoicesProgram s = some (candidateInput s (cursor machine state (index.val + 1))
      (head machine (entries machine state)[index.val].destination)) := by
  have first := node_first machine s.memory table state index
  have nextCandidate := node_next machine s.memory table state index
  have link := body_write_link machine s.memory table state index
  have next := write_direction_link machine s.memory table state index
  have destination := direction_destination_link machine s.memory table state index
  have target := destination_head machine s.memory table state index
  simp [loadCursorChoicesProgram, candidateInput, run, execute, address, write, ht, h0, h1,
    first, nextCandidate, link, next, destination, target]

@[expose] def cursorSelectionProgram : List Instruction :=
  [.store .scratch .zero .x, .store .scratch .one .y, .load .transition .scratch .matched]

@[expose] def cursorSelectionResult (s : State) (scratch : Nat) (matched : Bool) : State :=
  { registers := write s.registers .transition (if matched then s.registers .y else s.registers .x)
    memory := write (write s.memory (scratch, false) (s.registers .x))
                    (scratch, true) (s.registers .y) }

theorem cursor_selection_correct (s : State) (scratch : Nat) (matched : Bool)
    (hn : s.registers .scratch = .address scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hm : s.registers .matched = .offset matched) :
    run cursorSelectionProgram s = some (cursorSelectionResult s scratch matched) := by
  cases matched <;>
    simp [cursorSelectionProgram, cursorSelectionResult, run, execute, address, write, hn, h0, h1, hm]

@[expose] def updateCursorProgram : List Instruction := loadCursorChoicesProgram ++ cursorSelectionProgram

theorem update_cursor_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length) (s : State)
    (matched : Bool) (table : TableRep machine s.memory)
    (ht : s.registers .transition = .address (node alphabet state index.val))
    (hn : s.registers .scratch = .address 0)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run updateCursorProgram s = some finish ∧
      finish.registers .transition = .address
        (if matched then head machine (entries machine state)[index.val].destination
         else cursor machine state (index.val + 1)) := by
  let prepared := candidateInput s (cursor machine state (index.val + 1))
    (head machine (entries machine state)[index.val].destination)
  have loaded : run loadCursorChoicesProgram s = some prepared :=
    load_cursor_choices_correct machine state index s table ht h0 h1
  have pn : prepared.registers .scratch = .address 0 := by simp [prepared, candidateInput, write, hn]
  have p0 : prepared.registers .zero = .offset false := by simp [prepared, candidateInput, write, h0]
  have p1 : prepared.registers .one = .offset true := by simp [prepared, candidateInput, write, h1]
  have pm : prepared.registers .matched = .offset matched := by simp [prepared, candidateInput, write, hm]
  have selected := cursor_selection_correct prepared 0 matched pn p0 p1 pm
  refine ⟨cursorSelectionResult prepared 0 matched, run_composition loaded selected, ?_⟩
  cases matched <;> simp [cursorSelectionResult, prepared, candidateInput, write]

end SmcTuring.Dolan.Mov
