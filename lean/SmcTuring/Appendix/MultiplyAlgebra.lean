module
public import SmcTuring.Appendix.BranchAlgebra
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring

public section

namespace SmcTuring.Appendix.MultiplyAlgebra

open Machine32

@[expose] def lowBit (word : Word) : Word := 1 &&& word
@[expose] def chosen (factor multiplier : Word) : Word :=
  if lowBit multiplier = 0 then 0 else factor

theorem low_bit_toNat (word : Word) : (lowBit word).toNat = word.toNat % 2 := by
  simp [lowBit, BitVec.toNat_and]

theorem low_bit_cases (word : Word) : lowBit word = 0 ∨ lowBit word = 1 := by
  have bound := Nat.mod_lt word.toNat (by decide : 0 < 2)
  rw [← low_bit_toNat word] at bound
  by_cases zero : (lowBit word).toNat = 0
  · left; apply BitVec.eq_of_toNat_eq; simpa using zero
  · right; apply BitVec.eq_of_toNat_eq; change (lowBit word).toNat = 1; omega

theorem shifted_toNat (word : Word) : (word >>> 1).toNat = word.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem doubled (word : Word) : word <<< 1 = word * 2 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul]

theorem decomposition (word : Word) : word = (word >>> 1) * 2 + lowBit word := by
  apply BitVec.eq_of_toNat_eq
  have expand := Nat.mod_add_div word.toNat 2
  have fits : word.toNat < 4294967296 := word.isLt
  rw [BitVec.toNat_add, BitVec.toNat_mul, shifted_toNat, low_bit_toNat]
  norm_num
  have split : word.toNat / 2 * 2 + word.toNat % 2 = word.toNat := by omega
  rw [split, Nat.mod_eq_of_lt fits]

theorem chosen_product (factor multiplier : Word) : chosen factor multiplier = factor * lowBit multiplier := by
  rcases low_bit_cases multiplier with zero | one
  · simp [chosen, zero]
  · simp [chosen, one]

theorem step_invariant (factor multiplier total : Word) :
    (total + chosen factor multiplier) + (factor <<< 1) * (multiplier >>> 1) = total + factor * multiplier := by
  calc
    _ = total + factor * ((multiplier >>> 1) * 2 + lowBit multiplier) := by
      rw [chosen_product, doubled]
      ring
    _ = _ := by rw [← decomposition multiplier]


theorem shifted_bound (word : Word) (fuel : Nat) (bound : word.toNat < 2 ^ (fuel + 1)) :
    (word >>> 1).toNat < 2 ^ fuel := by
  rw [shifted_toNat]
  rw [Nat.pow_succ] at bound
  omega

/-- The shift-and-add arithmetic, with a finite bound that will be instantiated
by the actual field-word loop. No signed interpretation is required. -/
@[expose] def iterate : Nat -> Word -> Word -> Word -> Word
  | 0, _, _, total => total
  | fuel + 1, factor, multiplier, total =>
      if multiplier = 0 then total
      else iterate fuel (factor <<< 1) (multiplier >>> 1) (total + chosen factor multiplier)

theorem iterate_correct (fuel : Nat) (factor multiplier total : Word)
    (bound : multiplier.toNat < 2 ^ fuel) :
    iterate fuel factor multiplier total = total + factor * multiplier := by
  induction fuel generalizing factor multiplier total with
  | zero =>
      have zero : multiplier = 0 := by
        apply BitVec.eq_of_toNat_eq
        have small : multiplier.toNat < 1 := by simpa using bound
        change multiplier.toNat = 0
        omega
      simp [iterate, zero]
  | succ fuel ih =>
      by_cases zero : multiplier = 0
      · simp [iterate, zero]
      · rw [iterate, ite_eq_right zero, ih _ _ _ (shifted_bound multiplier fuel bound)]
        exact step_invariant factor multiplier total

theorem full_word_product (factor multiplier : Word) : iterate 32 factor multiplier 0 = factor * multiplier := by
  simpa using iterate_correct 32 factor multiplier 0 multiplier.isLt

end SmcTuring.Appendix.MultiplyAlgebra
