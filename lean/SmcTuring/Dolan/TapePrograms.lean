module
public import SmcTuring.Dolan.Programs

public section

namespace SmcTuring.Dolan.Mov

/-- Literal MOV expansion of the paper's conditional push block.
False direction pushes onto the right stack; true pushes onto the left. -/
@[expose] def pushProgram : List Instruction :=
  [.store .scratch .zero .right, .store .scratch .one .left,
   .load .x .scratch .direction, .store .current .one .x,
   .store .scratch .zero .left, .store .scratch .one .current,
   .load .left .scratch .direction,
   .store .scratch .zero .current, .store .scratch .one .right,
   .load .right .scratch .direction]

@[expose] def pushResult (s : State) (scratch current : Nat) (direction : Bool) : State :=
  let link := if direction then s.registers .left else s.registers .right
  { registers := write (write (write s.registers .x link)
                     .left (if direction then .address current else s.registers .left))
                     .right (if direction then s.registers .right else .address current)
    memory := write (write (write s.memory (current, true) link)
                      (scratch, false) (.address current))
                      (scratch, true) (s.registers .right) }

/-- Full state equality, including the scratch cells, for the literal push program. -/
theorem push_program_correct (s : State) (scratch current : Nat) (direction : Bool)
    (hn : s.registers .scratch = .address scratch)
    (hs : s.registers .current = .address current)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction) (distinct : current ≠ scratch) :
    run pushProgram s = some (pushResult s scratch current direction) := by
  cases direction <;>
    simp [pushProgram, pushResult, run, execute, address, write, hn, hs, h0, h1, hd]
  all_goals
    funext p
    rcases p with ⟨cell, choice⟩
    by_cases hc : cell = current <;> by_cases hn : cell = scratch <;>
      cases choice <;> simp_all [write]

/-- Literal MOV expansion of the corrected pop block. The preserved left
register is L, as required by the two-stack invariant. -/
@[expose] def popProgram : List Instruction :=
  [.store .scratch .zero .left, .store .scratch .one .right,
   .load .current .scratch .direction, .load .x .current .one,
   .store .scratch .zero .x, .store .scratch .one .left,
   .load .left .scratch .direction,
   .store .scratch .zero .right, .store .scratch .one .x,
   .load .right .scratch .direction]

@[expose] def popResult (s : State) (scratch left right : Nat) (direction : Bool) : State :=
  let next := if direction then right else left
  let tail := s.memory (next, true)
  { registers := write (write (write (write s.registers .current (.address next)) .x tail)
                      .left (if direction then .address left else tail))
                      .right (if direction then tail else .address right)
    memory := write (write s.memory (scratch, false) (.address right)) (scratch, true) tail }

theorem pop_program_correct (s : State) (scratch left right : Nat) (direction : Bool)
    (hn : s.registers .scratch = .address scratch)
    (hl : s.registers .left = .address left) (hr : s.registers .right = .address right)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction)
    (leftDistinct : left ≠ scratch) (rightDistinct : right ≠ scratch) :
    run popProgram s = some (popResult s scratch left right direction) := by
  cases direction <;>
    simp [popProgram, popResult, run, execute, address, write, hn, hl, hr, h0, h1, hd,
          leftDistinct, rightDistinct]
  all_goals
    funext p
    rcases p with ⟨cell, choice⟩
    by_cases hn : cell = scratch <;> cases choice <;> simp_all [write]

/-- Keep the push direction on a match; otherwise pop in the opposite
direction so the push is undone. All six instructions are MOVs. -/
@[expose] def popDirectionProgram : List Instruction :=
  [.store .scratch .zero .one, .store .scratch .one .zero,
   .load .x .scratch .direction,
   .store .scratch .zero .x, .store .scratch .one .direction,
   .load .direction .scratch .matched]

@[expose] def popDirectionResult (s : State) (scratch : Nat)
    (direction matched : Bool) : State :=
  { registers := write (write s.registers .x (.offset (!direction)))
                    .direction (.offset (if matched then direction else !direction))
    memory := write (write s.memory (scratch, false) (.offset (!direction)))
                    (scratch, true) (.offset direction) }

theorem pop_direction_program_correct (s : State) (scratch : Nat) (direction matched : Bool)
    (hn : s.registers .scratch = .address scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction)
    (hm : s.registers .matched = .offset matched) :
    run popDirectionProgram s = some (popDirectionResult s scratch direction matched) := by
  cases direction <;> cases matched <;>
    simp [popDirectionProgram, popDirectionResult, run, execute, address, write,
      hn, h0, h1, hd, hm]
  all_goals
    funext p
    rcases p with ⟨cell, choice⟩
    by_cases hn : cell = scratch <;> cases choice <;> simp_all [write]

@[expose] def advanceProgram : List Instruction :=
  pushProgram ++ popDirectionProgram ++ popProgram

/-- Select the old or replacement symbol before storing the current payload. -/
@[expose] def writeProgram (symbol : Word) : List Instruction :=
  [.load .x .current .zero, .immediate .y symbol] ++ selection ++
    [.store .current .zero .value]

@[expose] def writeResult (s : State) (scratch current : Nat)
    (symbol : Word) (matched : Bool) : State :=
  let old := s.memory (current, false)
  let selected := if matched then symbol else old
  { registers := write (write (write s.registers .x old) .y symbol) .value selected
    memory := write (write (write s.memory (scratch, false) old) (scratch, true) symbol)
                    (current, false) selected }

theorem write_program_correct (s : State) (scratch current : Nat) (symbol : Word) (matched : Bool)
    (hn : s.registers .scratch = .address scratch)
    (hs : s.registers .current = .address current)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hm : s.registers .matched = .offset matched) :
    run (writeProgram symbol) s = some (writeResult s scratch current symbol matched) := by
  let prepared : State :=
    { s with registers := write (write s.registers .x (s.memory (current, false))) .y symbol }
  have preparation : run [.load .x .current .zero, .immediate .y symbol] s = some prepared := by
    simp [prepared, run, execute, address, hs, h0]
  have pn : prepared.registers .scratch = .address scratch := by simp [prepared, write, hn]
  have p0 : prepared.registers .zero = .offset false := by simp [prepared, write, h0]
  have p1 : prepared.registers .one = .offset true := by simp [prepared, write, h1]
  have pm : prepared.registers .matched = .offset matched := by simp [prepared, write, hm]
  have selector := selection_correct prepared scratch matched pn p0 p1 pm
  simp only [writeProgram, run_append, preparation, Option.bind_some, selector]
  have sc : (selectionResult prepared scratch matched).registers .current = .address current := by
    simp [selectionResult, prepared, write, hs]
  have sz : (selectionResult prepared scratch matched).registers .zero = .offset false := by
    simp [selectionResult, prepared, write, h0]
  have store := store_correct (selectionResult prepared scratch matched) .current .zero .value
    current false sc sz
  simp only [run, store, Option.bind_some]
  rfl

end SmcTuring.Dolan.Mov
