module
public import SmcTuring.Appendix.Machine32
public import Mathlib.Tactic.NormNum

public section

namespace SmcTuring.Appendix.BranchAlgebra

open Machine32

@[expose] def signBit : Word := 2147483648
@[expose] def flip (word : Word) : Word := word ^^^ signBit
@[expose] def normalized (signed : Bool) (word : Word) : Word :=
  if signed then flip word else word

/-- The actual raw CF sampled by Listing 10: SUB borrow for gt=true;
NEG nonzero for gt=false. These are greater-than and not-equal, respectively. -/
@[expose] def raw (signed gt : Bool) (left right : Word) : Bool :=
  if gt then decide ((normalized signed right).toNat < (normalized signed left).toNat)
  else decide (normalized signed right - normalized signed left ≠ 0)
@[expose] def selected (signed gt notFlag : Bool) (left right : Word) : Bool :=
  if notFlag then raw signed gt left right else !(raw signed gt left right)
@[expose] def mask (condition : Bool) : Word := if condition then -1 else 0

inductive Relation where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr

@[expose] def holds (signed : Bool) (relation : Relation) (left right : Word) : Prop :=
  match relation with
  | .lt => if signed then left.toInt < right.toInt else left.toNat < right.toNat
  | .le => if signed then left.toInt ≤ right.toInt else left.toNat ≤ right.toNat
  | .eq => left = right
  | .ne => left ≠ right
  | .gt => if signed then right.toInt < left.toInt else right.toNat < left.toNat
  | .ge => if signed then right.toInt ≤ left.toInt else right.toNat ≤ left.toNat

instance holdsDecidable (signed : Bool) (relation : Relation) (left right : Word) :
    Decidable (holds signed relation left right) := by
  cases relation <;> cases signed <;> unfold holds <;> infer_instance

/-- All six relations use the printed flags, with explicit operand swapping. -/
@[expose] def relationSelected (signed : Bool) (relation : Relation) (left right : Word) : Bool :=
  match relation with
  | .lt => selected signed true true right left
  | .le => selected signed true false left right
  | .eq => selected signed false false left right
  | .ne => selected signed false true left right
  | .gt => selected signed true true left right
  | .ge => selected signed true false right left

theorem flip_involution (word : Word) : flip (flip word) = word := by
  simp [flip, BitVec.xor_assoc]

theorem flip_injective (left right : Word) : flip left = flip right ↔ left = right := by
  constructor
  · intro equal
    have restored := congrArg flip equal
    simpa [flip_involution] using restored
  · exact congrArg flip

theorem one_bit_cases (bit : BitVec 1) : bit = 0 ∨ bit = 1 := by
  have bound := bit.isLt
  by_cases zero : bit.toNat = 0
  · left; apply BitVec.eq_of_toNat_eq; simpa using zero
  · right; apply BitVec.eq_of_toNat_eq; change bit.toNat = 1; change bit.toNat < 2 at bound; omega

theorem append_toNat (hi : BitVec 1) (lo : BitVec 31) :
    (hi ++ lo).toNat = hi.toNat * 2147483648 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

theorem flip_append (hi : BitVec 1) (lo : BitVec 31) :
    flip (hi ++ lo) = (hi ^^^ (1 : BitVec 1)) ++ lo := by
  have bit : signBit = (1 : BitVec 1) ++ (0 : BitVec 31) := by decide
  rw [flip, bit, BitVec.xor_append]
  simp

theorem flip_append_toNat (hi : BitVec 1) (lo : BitVec 31) :
    ((flip (hi ++ lo)).toNat : Int) = (hi ++ lo).toInt + 2147483648 := by
  rcases one_bit_cases hi with zero | one
  · subst hi
    rw [flip_append, append_toNat, BitVec.toInt_append]
    norm_num
    omega
  · subst hi
    rw [flip_append, append_toNat, BitVec.toInt_append]
    norm_num

theorem flip_toNat (word : Word) :
    ((flip word).toNat : Int) = word.toInt + 2147483648 := by
  have reconstructed : word.extractLsb' 31 1 ++ word.extractLsb' 0 31 = word :=
    BitVec.extractLsb'_append_extractLsb'
  have value := flip_append_toNat (word.extractLsb' 31 1) (word.extractLsb' 0 31)
  simpa only [reconstructed] using value

theorem flip_order (left right : Word) :
    (flip left).toNat < (flip right).toNat ↔ left.toInt < right.toInt := by
  have l := flip_toNat left
  have r := flip_toNat right
  omega

theorem normalized_eq (signed : Bool) (left right : Word) :
    normalized signed left = normalized signed right ↔ left = right := by
  cases signed <;> simp [normalized, flip_injective]

theorem difference_ne_zero (left right : Word) : left - right ≠ 0 ↔ left ≠ right := by
  simp [BitVec.sub_eq_iff_eq_add]

theorem raw_gt (signed : Bool) (left right : Word) :
    raw signed true left right = decide (holds signed .gt left right) := by
  cases signed <;> simp [raw, normalized, holds, flip_order]

theorem raw_ne (signed : Bool) (left right : Word) :
    raw signed false left right = decide (left ≠ right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [raw, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  rw [difference_ne_zero]
  exact (not_congr (normalized_eq signed right left)).trans ne_comm

theorem all_relations (signed : Bool) (relation : Relation) (left right : Word) :
    relationSelected signed relation left right = decide (holds signed relation left right) := by
  apply Bool.eq_iff_iff.mpr
  cases relation <;> cases signed <;>
    simp [relationSelected, selected, raw_gt, raw_ne, holds, not_lt]

theorem sbb_mask (condition : Bool) :
    (0 : Word) - (if condition then 1 else 0) = mask condition := by
  cases condition <;> simp [mask]

theorem complement_mask (condition : Bool) : ~~~ mask condition = mask (!condition) := by
  cases condition <;> simp [mask, BitVec.neg_one_eq_allOnes]

theorem and_mask (condition : Bool) (delta : Word) :
    mask condition &&& delta = if condition then delta else 0 := by
  cases condition with
  | false => simp [mask]
  | true =>
    change (-1 : Word) &&& delta = delta
    have full : (-1 : Word) = BitVec.allOnes 32 := by decide
    rw [full, BitVec.allOnes_and]

end SmcTuring.Appendix.BranchAlgebra
