module
public import SmcTuring.Memory

public section

namespace SmcTuring.SMC

/-- Two's-complement integer XOR, with each negative integer represented as
the complement of a natural number. Finite-width refinement is separate. -/
@[expose] def xorWord : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- Integer AND. For a nonnegative operand, XOR removes precisely the bits
selected by the other operand when that operand is complemented. -/
@[expose] def andWord : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

theorem and_zero (a : Int) : andWord a 0 = 0 := by cases a <;> simp [andWord]

theorem and_negative_one (a : Int) : andWord a (-1) = a := by
  change andWord a (.negSucc 0) = a
  cases a <;> simp [andWord]

theorem xor_zero (a : Int) : xorWord a 0 = a := by cases a <;> simp [xorWord]

theorem xor_cancel_right (a b : Int) : xorWord (xorWord a b) b = a := by
  cases a <;> cases b <;> simp [xorWord, Nat.xor_assoc]

theorem xor_comm (a b : Int) : xorWord a b = xorWord b a := by
  cases a <;> cases b <;> simp [xorWord, Nat.xor_comm]

theorem xor_cancel_left (a b : Int) : xorWord (xorWord a b) a = b := by
  rw [xor_comm a b]
  exact xor_cancel_right b a

theorem select_word (continuation terminal : Int) (halted : Bool) :
    xorWord (andWord (xorWord continuation terminal) (if halted then -1 else 0)) continuation =
      if halted then terminal else continuation := by
  cases halted
  · simp [and_zero, xor_comm 0 continuation, xor_zero]
  · simp [and_negative_one, xor_cancel_left]

end SmcTuring.SMC
