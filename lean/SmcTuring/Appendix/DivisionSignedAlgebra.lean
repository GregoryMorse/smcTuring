module
public import SmcTuring.Appendix.DivisionAlgebra
public import SmcTuring.Appendix.MultiplyAlgebra

public section
namespace SmcTuring.Appendix.DivisionSignedAlgebra

open Machine32 BranchAlgebra

@[expose] def magnitude (word : Word) : Word := word.abs
@[expose] def sample (word : Word) : Word := signBit &&& word
@[expose] def negative (mod : Bool) (x y : Word) : Bool :=
  if mod then x.msb else xor x.msb y.msb
@[expose] def applySign (sign : Bool) (word : Word) : Word :=
  word - (mask sign &&& (word <<< 1))
@[expose] def magnitudeResult (mod : Bool) (x y : Word) : Nat :=
  if mod then (magnitude x).toNat % (magnitude y).toNat
  else (magnitude x).toNat / (magnitude y).toNat
@[expose] def result (mod : Bool) (x y : Word) : Word :=
  applySign (negative mod x y) (BitVec.ofNat 32 (magnitudeResult mod x y))
@[expose] def mathematical (mod : Bool) (x y : Word) : Int :=
  if mod then x.toInt.tmod y.toInt else x.toInt.tdiv y.toInt

theorem sample_sign (word : Word) :
    sample word = if word.msb then signBit else 0 := by
  have bit : signBit = BitVec.twoPow 32 31 := by decide
  rw [sample, bit, BitVec.twoPow_and]
  simp only [BitVec.msb_eq_getLsbD_last, Nat.reduceSub]
  rfl

theorem sample_mask (word : Word) :
    -((sample word) >>> 31) = mask word.msb := by
  rw [sample_sign]
  cases word.msb <;> decide

theorem sample_xor (x y : Word) :
    sample x ^^^ sample y = if xor x.msb y.msb then signBit else 0 := by
  rw [sample_sign, sample_sign]
  cases x.msb <;> cases y.msb <;> decide

theorem borrow_sign (word : Word) :
    decide (word.toNat < signBit.toNat) = !word.msb := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.msb_eq_decide, signBit]

theorem normalize_mask (word : Word) :
    ~~~ ((0 : Word) - (if decide (word.toNat < signBit.toNat) then 1 else 0)) =
      mask word.msb := by
  rw [borrow_sign, sbb_mask, complement_mask]
  simp

theorem negative_bit_mask (condition : Bool) :
    -((if condition then 1 else 0) : Word) = mask condition := by
  cases condition <;> decide

theorem normalize_negative_mask (word : Word) :
    ~~~(-((if decide (word.toNat < signBit.toNat) then 1 else 0) : Word)) =
      mask word.msb := by
  rw [negative_bit_mask, complement_mask, borrow_sign]
  simp

theorem apply_sign (sign : Bool) (word : Word) :
    applySign sign word = if sign then -word else word := by
  rw [applySign, and_mask, MultiplyAlgebra.doubled]
  cases sign with
  | false => simp
  | true =>
      change word - word * (2 : Word) = -word
      ring

theorem absolute_normalization (word : Word) :
    applySign word.msb word = magnitude word := by
  rw [apply_sign]
  rfl

theorem magnitude_toNat (word : Word) :
    (magnitude word).toNat = word.toInt.natAbs := by
  have fits : word.toNat < 4294967296 := word.isLt
  have msb := BitVec.msb_eq_decide word
  cases sign : word.msb with
  | false => simp [magnitude, BitVec.toNat_abs, BitVec.toInt_eq_msb_cond, sign]
  | true =>
      have signed : word.toInt = -((4294967296 - word.toNat : Nat) : Int) := by
        simp only [BitVec.toInt_eq_msb_cond, sign]
        norm_num
        omega
      rw [signed]
      simp [magnitude, BitVec.toNat_abs, sign]

theorem magnitude_bound (word : Word) : (magnitude word).toNat ≤ 2147483648 := by
  have fits : word.toNat < 4294967296 := word.isLt
  have msb := BitVec.msb_eq_decide word
  cases sign : word.msb <;> simp [magnitude, BitVec.toNat_abs, sign] at *
  all_goals omega

theorem magnitude_nonnegative_small (word : Word) (sign : word.msb = false) :
    (magnitude word).toNat < 2147483648 := by
  have msb := BitVec.msb_eq_decide word
  simp [magnitude, BitVec.toNat_abs, sign] at *
  omega

theorem signed_decomposition (word : Word) :
    word.toInt = if word.msb then -((magnitude word).toNat : Int)
      else ((magnitude word).toNat : Int) := by
  have fits : word.toNat < 4294967296 := word.isLt
  cases sign : word.msb <;>
    simp [magnitude, BitVec.toNat_abs, BitVec.toInt_eq_msb_cond, sign]
  omega

theorem magnitude_nonzero (word : Word) (nonzero : word ≠ 0) :
    0 < (magnitude word).toNat := by
  rw [magnitude_toNat, Int.natAbs_pos]
  change word.toInt ≠ (0 : Word).toInt
  rw [BitVec.toInt_ne]
  exact nonzero

theorem mathematical_magnitude (mod : Bool) (x y : Word) :
    mathematical mod x y =
      if negative mod x y then -((magnitudeResult mod x y) : Int)
      else ((magnitudeResult mod x y) : Int) := by
  rw [mathematical, signed_decomposition x, signed_decomposition y]
  cases mod <;> cases sx : x.msb <;> cases sy : y.msb <;>
    simp [sx, sy, negative, magnitudeResult, Int.tdiv_neg, Int.neg_tdiv,
      Int.tmod_neg, Int.neg_tmod, ← Int.ofNat_tmod]

/-- The word pattern matches truncation-toward-zero even at the sole signed
quotient overflow; mathematical signed interpretation has a separate range gate. -/
theorem result_pattern (mod : Bool) (x y : Word) :
    result mod x y = BitVec.ofInt 32 (mathematical mod x y) := by
  rw [result, apply_sign, mathematical_magnitude]
  cases negative mod x y <;> simp [BitVec.ofInt_neg]

theorem quotient_word (x y : Word) :
    BitVec.ofNat 32 (x.toNat / y.toNat) = x.udiv y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt BitVec.toNat_div_toNat_lt]

theorem remainder_word (x y : Word) :
    BitVec.ofNat 32 (x.toNat % y.toNat) = x.umod y := by
  apply BitVec.eq_of_toNat_eq
  have bound : x.toNat % y.toNat < 4294967296 :=
    lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  simp [BitVec.toNat_umod, Nat.mod_eq_of_lt bound]

theorem result_sdiv (x y : Word) : result false x y = x.sdiv y := by
  simp only [result, magnitudeResult, Bool.false_eq_true, ite_false, apply_sign]
  rw [quotient_word]
  cases sx : x.msb <;> cases sy : y.msb <;>
    simp [negative, magnitude, BitVec.abs_eq, BitVec.sdiv_eq, sx, sy]

theorem result_srem (x y : Word) : result true x y = x.srem y := by
  simp only [result, magnitudeResult, ite_true, apply_sign]
  rw [remainder_word]
  cases sx : x.msb <;> cases sy : y.msb <;>
    simp [negative, magnitude, BitVec.abs_eq, BitVec.srem_eq, sx, sy]

theorem result_toInt (mod : Bool) (x y : Word)
    (lower : -2147483648 ≤ mathematical mod x y)
    (upper : mathematical mod x y < 2147483648) :
    (result mod x y).toInt = mathematical mod x y := by
  rw [result_pattern]
  exact BitVec.toInt_ofInt_eq_self (by decide) lower upper


theorem magnitude_half_iff (word : Word) :
    (magnitude word).toNat = 2147483648 ↔ word = (2147483648 : Word) := by
  constructor
  · intro half
    apply BitVec.eq_of_toNat_eq
    have fits : word.toNat < 4294967296 := word.isLt
    cases sign : word.msb with
    | false =>
        have small := magnitude_nonnegative_small word sign
        omega
    | true =>
        simp [magnitude, BitVec.toNat_abs, sign] at half
        change word.toNat = 2147483648
        omega
  · intro same
    subst word
    decide

theorem magnitude_not_min (word : Word) (notMin : word ≠ (2147483648 : Word)) :
    (magnitude word).toNat < 2147483648 := by
  have bound := magnitude_bound word
  have different : (magnitude word).toNat ≠ 2147483648 :=
    fun same => notMin ((magnitude_half_iff word).mp same)
  omega

theorem negative_magnitude_one (word : Word) (sign : word.msb = true) :
    (magnitude word).toNat = 1 ↔ word = (-1 : Word) := by
  constructor
  · intro one
    apply BitVec.eq_of_toNat_eq
    have fits : word.toNat < 4294967296 := word.isLt
    simp [magnitude, BitVec.toNat_abs, sign] at one
    change word.toNat = 4294967295
    omega
  · intro same
    subst word
    decide

theorem positive_quotient_small (x y : Word) (nonzero : y ≠ 0)
    (noOverflow : ¬(x = (2147483648 : Word) ∧ y = (-1 : Word)))
    (positive : negative false x y = false) :
    magnitudeResult false x y < 2147483648 := by
  change (magnitude x).toNat / (magnitude y).toNat < 2147483648
  have belowDividend := Nat.div_le_self (magnitude x).toNat (magnitude y).toNat
  cases signX : x.msb with
  | false =>
      have small := magnitude_nonnegative_small x signX
      omega
  | true =>
      have signY : y.msb = true := by
        cases value : y.msb <;> simp [negative, signX, value] at positive ⊢
      by_cases min : x = (2147483648 : Word)
      · have notMinusOne : y ≠ (-1 : Word) := fun same => noOverflow ⟨min, same⟩
        have denominatorPositive := magnitude_nonzero y nonzero
        have denominatorNotOne : (magnitude y).toNat ≠ 1 :=
          fun one => notMinusOne ((negative_magnitude_one y signY).mp one)
        have denominatorLarge : 2 ≤ (magnitude y).toNat := by omega
        have multiply := Nat.mul_le_mul_left 2147483648 denominatorLarge
        have dividendBound := magnitude_bound x
        apply (Nat.div_lt_iff_lt_mul denominatorPositive).mpr
        norm_num at multiply
        omega
      · have small := magnitude_not_min x min
        omega

theorem quotient_range (x y : Word) (nonzero : y ≠ 0)
    (noOverflow : ¬(x = (2147483648 : Word) ∧ y = (-1 : Word))) :
    -2147483648 ≤ mathematical false x y ∧ mathematical false x y < 2147483648 := by
  have quotientBound : magnitudeResult false x y ≤ 2147483648 := by
    have bound := magnitude_bound x
    have belowDividend := Nat.div_le_self (magnitude x).toNat (magnitude y).toNat
    simp only [magnitudeResult, Bool.false_eq_true, ite_false]
    omega
  rw [mathematical_magnitude]
  cases sign : negative false x y with
  | true => simp only [ite_true]; omega
  | false =>
      have small := positive_quotient_small x y nonzero noOverflow sign
      simp only [Bool.false_eq_true, ite_false]
      omega

theorem remainder_range (x y : Word) (nonzero : y ≠ 0) :
    -2147483648 ≤ mathematical true x y ∧ mathematical true x y < 2147483648 := by
  have remainderSmall : magnitudeResult true x y < 2147483648 := by
    have bound := magnitude_bound y
    have belowDivisor := Nat.mod_lt (magnitude x).toNat (magnitude_nonzero y nonzero)
    simp only [magnitudeResult, ite_true]
    omega
  rw [mathematical_magnitude]
  cases negative true x y <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem quotient_toInt (x y : Word) (nonzero : y ≠ 0)
    (noOverflow : ¬(x = (2147483648 : Word) ∧ y = (-1 : Word))) :
    (result false x y).toInt = x.toInt.tdiv y.toInt :=
  result_toInt false x y (quotient_range x y nonzero noOverflow).1
    (quotient_range x y nonzero noOverflow).2

theorem remainder_toInt (x y : Word) (nonzero : y ≠ 0) :
    (result true x y).toInt = x.toInt.tmod y.toInt :=
  result_toInt true x y (remainder_range x y nonzero).1 (remainder_range x y nonzero).2

end SmcTuring.Appendix.DivisionSignedAlgebra
