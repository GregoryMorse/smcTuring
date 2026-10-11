module
public import Init

public section

namespace SmcTuring

/-- A word-addressed memory update, keeping every other address unchanged. -/
@[expose] def write {α β : Type} [DecidableEq α]
    (m : α → β) (a : α) (v : β) : α → β :=
  fun x => if x = a then v else m x

@[simp] theorem read_write_same {α β : Type} [DecidableEq α]
    (m : α → β) (a : α) (v : β) : write m a v a = v := by
  simp [write]

@[simp] theorem read_write_other {α β : Type} [DecidableEq α]
    (m : α → β) (a x : α) (v : β) (h : x ≠ a) :
    write m a v x = m x := by
  simp [write, h]

@[simp] theorem write_back {α β : Type} [DecidableEq α]
    (m : α → β) (a : α) : write m a (m a) = m := by
  funext x
  by_cases h : x = a <;> simp [write, h]

@[simp] theorem write_overwrite {α β : Type} [DecidableEq α]
    (m : α → β) (a : α) (v w : β) :
    write (write m a v) a w = write m a w := by
  funext x
  by_cases h : x = a <;> simp [write, h]

theorem writes_commute {α β : Type} [DecidableEq α]
    (m : α → β) (a b : α) (v w : β) (h : a ≠ b) :
    write (write m a v) b w = write (write m b w) a v := by
  funext x
  by_cases ha : x = a
  · subst x
    simp [write, h]
  · by_cases hb : x = b
    · subst x
      simp [write, ha]
    · simp [write, ha, hb]

end SmcTuring
