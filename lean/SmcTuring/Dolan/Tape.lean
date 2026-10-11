module
public import SmcTuring.Dolan.Primitives

public section

namespace SmcTuring.Dolan

/-- The persistent tape registers and linked-cell heap. The current cell's link
is intentionally unconstrained: it matters only after pushing onto a stack. -/
structure TapeState where
  left : Nat
  current : Nat
  right : Nat
  mem : Nat → Nat

/-- Abstract effect of the MOV selector block that pushes the current cell.
Direction false means left motion; true means right motion. -/
@[expose] def push (s : TapeState) (direction : Bool) : TapeState :=
  { left := if direction then s.current else s.left
    current := s.current
    right := if direction then s.right else s.current
    mem := write s.mem (s.current + 1) (if direction then s.left else s.right) }

/-- Abstract effect of the corrected pop selectors. The preserved left register
must be selected from left, not from right as in the printed p.3 sequence. -/
@[expose] def pop (s : TapeState) (direction : Bool) : TapeState :=
  let next := if direction then s.right else s.left
  let tail := s.mem (next + 1)
  { left := if direction then s.left else tail
    current := next
    right := if direction then tail else s.right
    mem := s.mem }

@[expose] def advance (s : TapeState) (direction matched : Bool) : TapeState :=
  pop (push s direction) (if matched then direction else !direction)

theorem nonmatch_preserves_registers (s : TapeState) (direction : Bool) :
    let result := advance s direction false
    result.left = s.left ∧ result.current = s.current ∧ result.right = s.right := by
  cases direction <;> simp [advance, push, pop]

theorem nonmatch_preserves_other_memory (s : TapeState) (direction : Bool)
    (address : Nat) (h : address ≠ s.current + 1) :
    (advance s direction false).mem address = s.mem address := by
  cases direction <;> simp [advance, push, pop, h]

theorem move_left_correct (s : TapeState) (h : s.left ≠ s.current) :
    let result := advance s false true
    result.current = s.left ∧ result.left = s.mem (s.left + 1) ∧ result.right = s.current := by
  simp [advance, push, pop, write, h]

theorem move_right_correct (s : TapeState) (h : s.right ≠ s.current) :
    let result := advance s true true
    result.current = s.right ∧ result.left = s.current ∧ result.right = s.mem (s.right + 1) := by
  simp [advance, push, pop, write, h]

end SmcTuring.Dolan
