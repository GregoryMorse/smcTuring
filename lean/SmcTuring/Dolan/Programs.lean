module
public import SmcTuring.Dolan.Machine

public section

namespace SmcTuring.Dolan.Mov

/-- A literal MOV program: initialize the offset registers, store zero at Y,
store one at X, then read Y to obtain the equality flag. -/
@[expose] def comparison : List Instruction :=
  [.immediate .zero (.offset false), .immediate .one (.offset true),
   .store .y .zero .zero, .store .x .zero .one, .load .matched .y .zero]

@[expose] def comparisonResult (s : State) (x y : Nat) : State :=
  { registers := write (write (write s.registers .zero (.offset false)) .one (.offset true))
                       .matched (.offset (decide (x = y)))
    memory := write (write s.memory (y, false) (.offset false)) (x, false) (.offset true) }

/-- Exact execution of the MOV comparison, including its memory side effects. -/
theorem comparison_correct (s : State) (x y : Nat)
    (hx : s.registers .x = .address x) (hy : s.registers .y = .address y) :
    run comparison s = some (comparisonResult s x y) := by
  by_cases h : x = y
  · subst y
    simp [comparison, comparisonResult, run, execute, address, write, hx, hy]
  · have h' : y ≠ x := Ne.symm h
    simp [comparison, comparisonResult, run, execute, address, write, hx, hy, h, h']

/-- This three-instruction selector uses only the original indexed store/load forms. -/
@[expose] def selection : List Instruction :=
  [.store .scratch .zero .x, .store .scratch .one .y, .load .value .scratch .matched]

@[expose] def selectionResult (s : State) (scratch : Nat) (choice : Bool) : State :=
  { registers := write s.registers .value (if choice then s.registers .y else s.registers .x)
    memory := write (write s.memory (scratch, false) (s.registers .x))
                    (scratch, true) (s.registers .y) }

theorem selection_correct (s : State) (scratch : Nat) (choice : Bool)
    (hn : s.registers .scratch = .address scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hm : s.registers .matched = .offset choice) :
    run selection s = some (selectionResult s scratch choice) := by
  cases choice <;>
    simp [selection, selectionResult, run, execute, address, write, hn, h0, h1, hm]

end SmcTuring.Dolan.Mov
