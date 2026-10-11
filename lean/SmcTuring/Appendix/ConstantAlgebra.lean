module
public import SmcTuring.Appendix.MultiplyAlgebra

public section

namespace SmcTuring.Appendix.ConstantAlgebra

open Machine32

/-- Listing 6's compile-time NLZ is the number of trailing zero bits. -/
@[expose] def zeros (value : Word) : Nat := value.ctz.toNat
@[expose] def rest (value : Word) : Word := value >>> (zeros value + 1)
@[expose] def scale (count : Nat) : Word := BitVec.ofNat 32 (2 ^ count)

theorem zeros_lt (value : Word) (nonzero : value ≠ 0) : zeros value < 32 := by
  have h := (BitVec.ctz_lt_iff_ne_zero (x := value)).mpr nonzero
  simpa [zeros, BitVec.lt_def] using h

theorem lower_bits_zero (value : Word) : value.toNat % 2 ^ zeros value = 0 := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases below : index < zeros value
  · have h := BitVec.getLsbD_false_of_lt_ctz (x := value) below
    simpa [Nat.testBit_mod_two_pow, below, BitVec.getLsbD] using h
  · simp [Nat.testBit_mod_two_pow, below]

theorem quotient_odd (value : Word) (nonzero : value ≠ 0) :
    (value.toNat / 2 ^ zeros value) % 2 = 1 := by
  have h := BitVec.getLsbD_true_ctz_of_ne_zero nonzero
  simpa [zeros, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq] using h

theorem rest_toNat (value : Word) :
    (rest value).toNat = value.toNat / 2 ^ (zeros value + 1) := by
  simp [rest, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem decomposition_nat (value : Word) (nonzero : value ≠ 0) :
    value.toNat = (2 * (rest value).toNat + 1) * 2 ^ zeros value := by
  have lower := lower_bits_zero value
  have odd := quotient_odd value nonzero
  have expand := Nat.mod_add_div value.toNat (2 ^ zeros value)
  have split := Nat.mod_add_div (value.toNat / 2 ^ zeros value) 2
  have next : value.toNat / 2 ^ zeros value / 2 = (rest value).toNat := by
    rw [rest_toNat, Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [lower, zero_add] at expand
  rw [odd, next] at split
  rw [← expand, ← split]
  ring

theorem decomposition (value : Word) (nonzero : value ≠ 0) :
    value = (2 * rest value + 1) * scale (zeros value) := by
  have h := congrArg (BitVec.ofNat 32) (decomposition_nat value nonzero)
  simpa [BitVec.ofNat_mul, BitVec.ofNat_add, scale] using h

theorem shifted (value : Word) (count : Nat) : value <<< count = value * scale count := by
  apply BitVec.eq_of_toNat_eq
  simp [scale, BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem scale_successor (count : Nat) : scale (count + 1) = 2 * scale count := by
  simp [scale, Nat.pow_succ, BitVec.ofNat_mul, BitVec.mul_comm]

theorem rest_bound (value : Word) (fuel : Nat) (bound : value.toNat < 2 ^ (fuel + 1)) :
    (rest value).toNat < 2 ^ fuel := by
  have positive : 0 < 2 ^ zeros value := Nat.two_pow_pos _
  have two : 2 ≤ 2 ^ (zeros value + 1) := by
    rw [Nat.pow_succ]
    omega
  have division := Nat.div_le_div_left two (a := value.toNat)
  rw [rest_toNat]
  have bound' : value.toNat / 2 < 2 ^ fuel := by
    rw [Nat.pow_succ] at bound
    omega
  omega

/-- After the first retained bit, every gap includes the consumed set bit:
    shift by NLZ(remaining)+1, accumulate, and repeat at compile time. -/
@[expose] def tail : Nat -> Word -> Word -> Word -> Word
  | 0, _, _, total => total
  | fuel + 1, factor, value, total =>
      let nextFactor := factor <<< (zeros value + 1)
      let nextValue := rest value
      if nextValue = 0 then total + nextFactor
      else tail fuel nextFactor nextValue (total + nextFactor)

theorem gap_invariant (factor value total : Word) (nonzero : value ≠ 0) :
    (total + (factor <<< (zeros value + 1))) +
      (factor <<< (zeros value + 1)) * (2 * rest value) = total + factor * (2 * value) := by
  conv_rhs => rw [decomposition value nonzero]
  rw [shifted, scale_successor]
  ring

theorem tail_correct (fuel : Nat) (factor value total : Word)
    (nonzero : value ≠ 0) (bound : value.toNat < 2 ^ fuel) :
    tail fuel factor value total = total + factor * (2 * value) := by
  induction fuel generalizing factor value total with
  | zero =>
      have small : value.toNat < 1 := by simpa using bound
      have zero : value = 0 := by
        apply BitVec.eq_of_toNat_eq
        change value.toNat = 0
        omega
      exact (nonzero zero).elim
  | succ fuel ih =>
      have h := gap_invariant factor value total nonzero
      by_cases terminal : rest value = 0
      · simpa [tail, terminal] using h
      · simp only [tail, terminal, ↓reduceIte]
        rw [ih _ _ _ terminal (rest_bound value fuel bound)]
        exact h

@[expose] def multiply (factor value : Word) : Word :=
  if value = 0 then 0
  else
    let first := factor <<< zeros value
    let remaining := rest value
    if remaining = 0 then first
    else tail 31 first remaining first

theorem first_invariant (factor value : Word) (nonzero : value ≠ 0) :
    (factor <<< zeros value) + (factor <<< zeros value) * (2 * rest value) = factor * value := by
  conv_rhs => rw [decomposition value nonzero]
  rw [shifted]
  ring

/-- All constants and inputs, including zero and negative two's-complement patterns. -/
theorem correct (factor value : Word) : multiply factor value = factor * value := by
  by_cases zero : value = 0
  · simp [multiply, zero]
  · have h := first_invariant factor value zero
    by_cases terminal : rest value = 0
    · rw [multiply, ite_eq_right zero, ite_eq_left terminal]
      simpa [terminal] using h
    · simp only [multiply, zero, terminal, ↓reduceIte]
      rw [tail_correct _ _ _ _ terminal (rest_bound value 31 value.isLt)]
      exact h

theorem gap_count_lt (value : Word) (remaining : value ≠ 0)
    (fuel : Nat) (bound : value.toNat < 2 ^ fuel) : zeros value < fuel := by
  have lower := BitVec.two_pow_ctz_le_toNat_of_ne_zero remaining
  by_contra h
  have larger := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : fuel ≤ zeros value)
  change 2 ^ zeros value ≤ value.toNat at lower
  omega

theorem rest_decreases (value : Word) (nonzero : value ≠ 0) :
    (rest value).toNat < value.toNat := by
  have lower := decomposition_nat value nonzero
  have positive : 0 < 2 ^ zeros value := Nat.two_pow_pos _
  have smaller : (rest value).toNat < 2 * (rest value).toNat + 1 := by omega
  exact lt_of_lt_of_le smaller (lower ▸ Nat.le_mul_of_pos_right _ positive)

/-- Mathematical compile-time shifts may consume the 32nd bit completely. -/
theorem top_bit_consumed (value : Word) (top : zeros value = 31) : rest value = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [rest_toNat, top]
  change value.toNat / 4294967296 = 0
  exact Nat.div_eq_of_lt value.isLt

theorem zero_correct (factor : Word) : multiply factor 0 = 0 := by simp [correct]

theorem signed_low_product (factor value : Int) :
    multiply (BitVec.ofInt 32 factor) (BitVec.ofInt 32 value) = BitVec.ofInt 32 (factor * value) := by
  rw [correct, BitVec.ofInt_mul]

end SmcTuring.Appendix.ConstantAlgebra
