module
public import SmcTuring.Appendix.DivisionBody
public import Mathlib.Tactic.IntervalCases

public section
namespace SmcTuring.Appendix.DivisionPacked
open Machine32 (Word State)
open DivisionAlgebra DivisionWordAlgebra

/-- At pass k, low contains the unprocessed suffix above the k quotient bits. -/
@[expose] def packed (dividend : Word) (k quotient : Nat) : Nat :=
  (dividend.toNat % 2 ^ (32 - k)) * 2 ^ k + quotient

theorem prefix_bound (dividend : Word) (k : Nat) (range : k ≤ 32) :
    dividend.toNat / 2 ^ (32 - k) < 2 ^ k := by
  have bound : dividend.toNat < 4294967296 := dividend.isLt
  interval_cases k <;> norm_num at * <;> omega

theorem quotient_bound (dividend divisor : Word) (k : Nat)
    (range : k ≤ 32) (nonzero : 0 < divisor.toNat) :
    (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).quotient < 2 ^ k := by
  have fits := prefix_bound dividend k range
  rw [(scan_correct _ _ _ nonzero fits).1]
  have := Nat.div_le_self (dividend.toNat / 2 ^ (32 - k)) divisor.toNat
  omega

theorem packed_bit (dividend low : Word) (k quotient : Nat)
    (range : k < 32) (small : quotient < 2 ^ k)
    (value : low.toNat = packed dividend k quotient) :
    (if low.msb then 1 else 0 : Nat) =
      (dividend.toNat / 2 ^ (31 - k)) % 2 := by
  have bound : dividend.toNat < 4294967296 := dividend.isLt
  simp only [packed] at value
  rw [BitVec.msb_eq_decide]
  norm_num
  interval_cases k <;> norm_num at * <;> split <;> omega

theorem packed_shift (dividend low : Word) (k quotient : Nat)
    (range : k < 32) (small : quotient < 2 ^ k)
    (value : low.toNat = packed dividend k quotient) :
    (low <<< 1).toNat =
      (dividend.toNat % 2 ^ (31 - k)) * 2 ^ (k + 1) + 2 * quotient := by
  have bound : dividend.toNat < 4294967296 := dividend.isLt
  simp only [packed] at value
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  norm_num
  interval_cases k <;> norm_num at * <;> omega

theorem scan_next (dividend divisor : Word) (k : Nat) (range : k < 32) :
    scan (k + 1) (dividend.toNat / 2 ^ (31 - k)) divisor.toNat =
      step (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat)
        ((dividend.toNat / 2 ^ (31 - k)) % 2) divisor.toNat := by
  have divided : (dividend.toNat / 2 ^ (31 - k)) / 2 =
      dividend.toNat / 2 ^ (32 - k) := by
    rw [Nat.div_div_eq_div_mul]
    interval_cases k <;> norm_num
  simp only [scan, divided]


theorem next_low_toNat (low high divisor : Word) :
    (nextLow low high divisor).toNat = (low <<< 1).toNat +
      (if underflow low high divisor then 0 else 1 : Nat) := by
  have carry := low_add_carry low (underflow low high divisor)
  rw [nextLow, BitVec.toNat_add_of_not_uaddOverflow (by rw [carry]; decide)]
  cases underflow low high divisor <;> simp

theorem packed_step (dividend low high divisor : Word) (k : Nat)
    (range : k < 32) (nonzero : 0 < divisor.toNat)
    (lowValue : low.toNat = packed dividend k
      (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).quotient)
    (highValue : high.toNat =
      (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).remainder) :
    (nextLow low high divisor).toNat = packed dividend (k + 1)
      (scan (k + 1) (dividend.toNat / 2 ^ (31 - k)) divisor.toNat).quotient ∧
    (nextHigh low high divisor).toNat =
      (scan (k + 1) (dividend.toNat / 2 ^ (31 - k)) divisor.toNat).remainder := by
  have quotSmall := quotient_bound dividend divisor k (by omega) nonzero
  have bit := packed_bit dividend low k _ range quotSmall lowValue
  have shifted := packed_shift dividend low k _ range quotSmall lowValue
  have coordinate : 32 - (k + 1) = 31 - k := by omega
  have prefixFits := prefix_bound dividend (k + 1) (by omega)
  rw [coordinate] at prefixFits
  have fits := trial_fits k (dividend.toNat / 2 ^ (31 - k)) divisor.toNat nonzero prefixFits
  have divided : (dividend.toNat / 2 ^ (31 - k)) / 2 =
      dividend.toNat / 2 ^ (32 - k) := by
    rw [Nat.div_div_eq_div_mul]
    interval_cases k <;> norm_num
  rw [divided, ← highValue, ← bit] at fits
  have powBound : 2 ^ (k + 1) ≤ 4294967296 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ 32 by omega)
    exact this
  have fits32 : 2 * high.toNat + (if low.msb then 1 else 0 : Nat) < 4294967296 := by omega
  rw [next_low_toNat, shifted, next_high_toNat _ _ _ fits32, scan_next dividend divisor k range]
  simp only [packed, underflow, trial_toNat low high fits32, bit, highValue]
  rw [coordinate]
  by_cases small : 2 * (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).remainder +
      (dividend.toNat / 2 ^ (31 - k)) % 2 < divisor.toNat
  all_goals simp [step, small] <;> omega

end SmcTuring.Appendix.DivisionPacked

