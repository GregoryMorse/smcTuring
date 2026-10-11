module
public import SmcTuring.Appendix.Machine32
public import Mathlib.Tactic.Ring

public section
namespace SmcTuring.Appendix.DivisionAlgebra

/-- Restoring division reads the dividend from most to least significant bit. -/
structure Digits where
  processed : Nat
  quotient : Nat
  remainder : Nat
  deriving DecidableEq, Repr

@[expose] def step (state : Digits) (bit divisor : Nat) : Digits :=
  let trial := 2 * state.remainder + bit
  if trial < divisor then
    ⟨2 * state.processed + bit, 2 * state.quotient, trial⟩
  else
    ⟨2 * state.processed + bit, 2 * state.quotient + 1, trial - divisor⟩

@[expose] def Valid (state : Digits) (divisor : Nat) : Prop :=
  state.processed = state.quotient * divisor + state.remainder ∧
    state.remainder < divisor

theorem step_processed (state : Digits) (bit divisor : Nat) :
    (step state bit divisor).processed = 2 * state.processed + bit := by
  by_cases small : 2 * state.remainder + bit < divisor
  all_goals simp [step, small]

theorem step_valid (state : Digits) (bit divisor : Nat)
    (valid : Valid state divisor) (binary : bit < 2) :
    Valid (step state bit divisor) divisor := by
  rcases valid with ⟨equation, bound⟩
  have expansion : 2 * state.processed + bit =
      (2 * state.quotient) * divisor + (2 * state.remainder + bit) := by
    rw [equation]
    ring
  by_cases small : 2 * state.remainder + bit < divisor
  all_goals simp only [step, small, ite_true, ite_false, Valid]
  · exact ⟨expansion, trivial⟩
  · have distributive : (2 * state.quotient + 1) * divisor =
        (2 * state.quotient) * divisor + divisor := by ring
    rw [distributive]
    constructor <;> omega

/-- Exactly width bits, including leading zeros. This is an arithmetic
specification; execution of the printed word/byte loop is a separate contract. -/
@[expose] def scan : Nat → Nat → Nat → Digits
  | 0, _, _ => ⟨0, 0, 0⟩
  | width + 1, value, divisor =>
      step (scan width (value / 2) divisor) (value % 2) divisor

theorem scan_valid (width value divisor : Nat) (nonzero : 0 < divisor) :
    Valid (scan width value divisor) divisor := by
  induction width generalizing value with
  | zero => exact ⟨by simp [scan], nonzero⟩
  | succ width ih =>
      exact step_valid _ _ _ (ih (value / 2)) (Nat.mod_lt _ (by decide))

theorem scan_processed (width value divisor : Nat) (fits : value < 2 ^ width) :
    (scan width value divisor).processed = value := by
  induction width generalizing value with
  | zero =>
      have zero : value = 0 := by simpa using fits
      simp [scan, zero]
  | succ width ih =>
      have parent : value / 2 < 2 ^ width := by
        rw [Nat.pow_succ] at fits
        omega
      rw [scan, step_processed, ih _ parent]
      have division := Nat.mod_add_div value 2
      omega

theorem scan_correct (width value divisor : Nat) (nonzero : 0 < divisor)
    (fits : value < 2 ^ width) :
    (scan width value divisor).quotient = value / divisor ∧
      (scan width value divisor).remainder = value % divisor := by
  have valid := scan_valid width value divisor nonzero
  unfold Valid at valid
  rw [scan_processed width value divisor fits] at valid
  rcases valid with ⟨equation, bound⟩
  have quotient : value / divisor = (scan width value divisor).quotient := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have expand : ((scan width value divisor).quotient + 1) * divisor =
          (scan width value divisor).quotient * divisor + divisor := by ring
      rw [expand]
      omega
  have remainder : value % divisor = (scan width value divisor).remainder := by
    conv_lhs => rw [equation]
    simp [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt bound]
  exact ⟨quotient.symm, remainder.symm⟩

theorem remainder_le_processed (state : Digits) (divisor : Nat)
    (valid : Valid state divisor) : state.remainder ≤ state.processed := by
  have := valid.1
  omega

/-- With a width-bit dividend, each trial fits in the same width-bit word.
No extra high carry is needed in Listing 12's exactly 32 passes. -/
theorem trial_fits (width value divisor : Nat) (nonzero : 0 < divisor)
    (fits : value < 2 ^ (width + 1)) :
    2 * (scan width (value / 2) divisor).remainder + value % 2 <
      2 ^ (width + 1) := by
  have parent : value / 2 < 2 ^ width := by
    rw [Nat.pow_succ] at fits
    omega
  have small := remainder_le_processed _ divisor
    (scan_valid width (value / 2) divisor nonzero)
  rw [scan_processed width (value / 2) divisor parent] at small
  have division := Nat.mod_add_div value 2
  omega

theorem full_word_division (dividend divisor : Machine32.Word)
    (nonzero : divisor ≠ 0) :
    (scan 32 dividend.toNat divisor.toNat).quotient = dividend.toNat / divisor.toNat ∧
      (scan 32 dividend.toNat divisor.toNat).remainder = dividend.toNat % divisor.toNat := by
  have positive : 0 < divisor.toNat := by
    have nz : divisor.toNat ≠ 0 := by
      intro zero
      apply nonzero
      exact BitVec.eq_of_toNat_eq zero
    omega
  exact scan_correct 32 dividend.toNat divisor.toNat positive dividend.isLt

theorem quotient_fits (dividend divisor : Machine32.Word) :
    dividend.toNat / divisor.toNat < 4294967296 := by
  have := Nat.div_le_self dividend.toNat divisor.toNat
  have bound : dividend.toNat < 4294967296 := dividend.isLt
  omega

end SmcTuring.Appendix.DivisionAlgebra
