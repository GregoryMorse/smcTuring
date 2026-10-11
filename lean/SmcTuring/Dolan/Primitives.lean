module
public import SmcTuring.Memory

public section

namespace SmcTuring.Dolan

/-- The memory effects of two MOV stores followed by a MOV load. The clobbered
addresses are the symbol scratch cells, not simulated tape or transition cells. -/
@[expose] def compare (m : Nat → Nat) (x y : Nat) : Nat :=
  write (write m x 0) y 1 x

theorem compare_correct (m : Nat → Nat) (x y : Nat) :
    compare m x y = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [compare, write, h]

/-- Fill a two-word selector and load one of its two entries. -/
@[expose] def select (m : Nat → Nat) (scratch left right : Nat) (choice : Bool) : Nat :=
  write (write m scratch left) (scratch + 1) right (scratch + choice.toNat)

theorem select_correct (m : Nat → Nat) (scratch left right : Nat) (choice : Bool) :
    select m scratch left right choice = if choice then right else left := by
  cases choice <;> simp [select, write]

/-- Five MOV operations compare a candidate with the sentinel, restoring the
candidate cell. The sentinel contents are scratch and may be clobbered. -/
@[expose] def sentinelCompare (m : Nat → Nat) (candidate sentinel : Nat) : Nat × (Nat → Nat) :=
  let saved := m candidate
  let cleared := write m sentinel 0
  let marked := write cleared candidate 1
  (marked sentinel, write marked candidate saved)

theorem sentinel_compare_correct (m : Nat → Nat) (candidate sentinel : Nat) :
    (sentinelCompare m candidate sentinel).1 = if candidate = sentinel then 1 else 0 := by
  by_cases h : candidate = sentinel
  · simp [sentinelCompare, write, h]
  · have h' := Ne.symm h
    simp [sentinelCompare, write, h, h']

theorem sentinel_candidate_restored (m : Nat → Nat) (candidate sentinel : Nat) :
    (sentinelCompare m candidate sentinel).2 candidate = m candidate := by
  simp [sentinelCompare]

/-- Correct polarity: equality selects invalid zero; inequality selects scratch. -/
@[expose] def haltAddress (sentinel : Nat) (equal : Bool) : Nat :=
  if equal then 0 else sentinel

theorem halt_address_zero_iff (sentinel : Nat) (h : sentinel ≠ 0) (equal : Bool) :
    haltAddress sentinel equal = 0 ↔ equal = true := by
  cases equal <;> simp [haltAddress, h]

/-- The table printed on Dolan p.4 has the opposite polarity to the stated H. -/
theorem printed_halt_select_wrong (m : Nat → Nat) (sentinel : Nat) (h : sentinel ≠ 0) :
    select m sentinel 0 sentinel true ≠ haltAddress sentinel true := by
  simpa [select_correct, haltAddress] using h

end SmcTuring.Dolan
