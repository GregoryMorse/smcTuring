module
public import SmcTuring.Appendix.DivisionSignedAlgebra

public section
namespace SmcTuring.Appendix.DivisionWordAlgebra
open Machine32 BranchAlgebra

@[expose] def incomingBit (word : Word) : Word := if word.msb then 1 else 0
@[expose] def trial (low high : Word) : Word := (high <<< 1) + incomingBit low
@[expose] def underflow (low high divisor : Word) : Bool :=
  decide ((trial low high).toNat < divisor.toNat)
@[expose] def nextLow (low high divisor : Word) : Word :=
  (low <<< 1) + (if underflow low high divisor then 0 else 1)
@[expose] def nextHigh (low high divisor : Word) : Word :=
  if underflow low high divisor then trial low high else trial low high - divisor

theorem doubling_borrow (word : Word) :
    decide ((word <<< 1).toNat < word.toNat) = word.msb := by
  apply Bool.eq_iff_iff.mpr
  have fits : word.toNat < 4294967296 := word.isLt
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.msb_eq_decide,
    decide_eq_true_eq]
  norm_num
  omega

theorem masked_double_no_borrow (word : Word) :
    decide (word.toNat < ((word <<< 1) &&& mask word.msb).toNat) = false := by
  apply Bool.eq_false_iff.mpr
  rw [BitVec.and_comm, and_mask]
  have fits : word.toNat < 4294967296 := word.isLt
  cases sign : word.msb with
  | false => simp
  | true =>
      have large : 2147483648 ≤ word.toNat := by
        simpa using BitVec.le_toNat_of_msb_true sign
      simp only [ite_true, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      norm_num
      omega

theorem subtract_restore (value divisor : Word) :
    value - divisor + (mask (decide (value.toNat < divisor.toNat)) &&& divisor) =
      if value.toNat < divisor.toNat then value else value - divisor := by
  rw [and_mask]
  by_cases small : value.toNat < divisor.toNat <;> simp [small]

theorem quotient_bit (condition : Bool) :
    (1 : Word) &&& ~~~ mask condition = if condition then 0 else 1 := by
  cases condition <;> decide

theorem low_add_carry (low : Word) (condition : Bool) :
    (low <<< 1).uaddOverflow (if condition then 0 else 1) = false := by
  have fits : low.toNat < 4294967296 := low.isLt
  cases condition
  · simp only [BitVec.uaddOverflow, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    norm_num
    omega
  · simp [BitVec.uaddOverflow]
    exact Nat.mod_lt _ (by decide)

theorem trial_toNat (low high : Word)
    (fits : 2 * high.toNat + (if low.msb then 1 else 0 : Nat) < 4294967296) :
    (trial low high).toNat = 2 * high.toNat + (if low.msb then 1 else 0 : Nat) := by
  have doubled : 2 * high.toNat < 4294967296 := by omega
  have shift : (high <<< 1).toNat = 2 * high.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mod_eq_of_lt doubled]
  have bit : (incomingBit low).toNat = (if low.msb then 1 else 0 : Nat) := by
    cases sign : low.msb <;> simp [incomingBit, sign]
  rw [trial, BitVec.toNat_add, shift, bit]
  exact Nat.mod_eq_of_lt fits

theorem next_high_toNat (low high divisor : Word)
    (fits : 2 * high.toNat + (if low.msb then 1 else 0 : Nat) < 4294967296) :
    (nextHigh low high divisor).toNat =
      if 2 * high.toNat + (if low.msb then 1 else 0 : Nat) < divisor.toNat
        then 2 * high.toNat + (if low.msb then 1 else 0 : Nat)
        else 2 * high.toNat + (if low.msb then 1 else 0 : Nat) - divisor.toNat := by
  by_cases small : 2 * high.toNat + (if low.msb then 1 else 0 : Nat) < divisor.toNat
  · simp [nextHigh, underflow, trial_toNat low high fits, small]
  · simp only [nextHigh, underflow, trial_toNat low high fits, small,
      decide_false, Bool.false_eq_true, ite_false]
    rw [BitVec.toNat_sub, trial_toNat low high fits]
    have divisorBound : divisor.toNat < 4294967296 := divisor.isLt
    norm_num
    omega


theorem signed_result_carry (sign : Bool) (word : Word) :
    decide (word.toNat < ((word <<< 1) &&& mask sign).toNat) =
      (sign && decide (0 < word.toNat ∧ word.toNat < 2147483648)) := by
  rw [BitVec.and_comm, and_mask]
  cases sign with
  | false => simp
  | true =>
      apply Bool.eq_iff_iff.mpr
      have fits : word.toNat < 4294967296 := word.isLt
      simp only [ite_true, Bool.true_and, decide_eq_true_eq,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      norm_num
      omega

end SmcTuring.Appendix.DivisionWordAlgebra
