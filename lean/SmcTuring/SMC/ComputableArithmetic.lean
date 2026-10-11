module
public import SmcTuring.SMC.ComputableJournal

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

theorem unzigzag_injective : Function.Injective unzigzag := by
  intro first second same
  have coded := congrArg zigzag same
  simpa only [zigzag_unzigzag] using coded

@[expose] def differenceCode (left right : Nat) : Nat :=
  if right ≤ left then 2 * (left - right) else 2 * (right - left - 1) + 1

theorem difference_decode (left right : Nat) : unzigzag (differenceCode left right) = (left : Int) - right := by
  unfold differenceCode
  split
  · change unzigzag (zigzag (Int.ofNat (left - right))) = _
    rw [unzigzag_zigzag]
    simp only [Int.ofNat_eq_natCast]
    omega
  · change unzigzag (zigzag (Int.negSucc (right - left - 1))) = _
    rw [unzigzag_zigzag]
    omega

theorem difference_primrec : Primrec₂ differenceCode := by
  have negativeMagnitude : Primrec (fun input : Nat × Nat => input.2 - input.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)
  exact Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      negativeMagnitude))

@[expose] def addCode (left right : Nat) : Nat :=
  if left % 2 = 0 then
    if right % 2 = 0 then 2 * (left / 2 + right / 2)
    else differenceCode (left / 2) (right / 2 + 1)
  else
    if right % 2 = 0 then differenceCode (right / 2) (left / 2 + 1)
    else 2 * (left / 2 + right / 2 + 1) + 1

theorem add_decode (left right : Nat) : unzigzag (addCode left right) = unzigzag left + unzigzag right := by
  unfold addCode
  split <;> rename_i leftSign
  · split <;> rename_i rightSign
    · have code := unzigzag_zigzag (Int.ofNat (left / 2 + right / 2))
      change unzigzag (2 * (left / 2 + right / 2)) = Int.ofNat (left / 2 + right / 2) at code
      rw [code]
      simp only [unzigzag, leftSign, rightSign, ite_true, Int.ofNat_eq_natCast]
      omega
    · rw [difference_decode]
      simp only [unzigzag, leftSign, rightSign, ite_true, ite_false, Int.ofNat_eq_natCast]
      omega
  · split <;> rename_i rightSign
    · rw [difference_decode]
      simp only [unzigzag, leftSign, rightSign, ite_true, ite_false, Int.ofNat_eq_natCast]
      omega
    · have code := unzigzag_zigzag (Int.negSucc (left / 2 + right / 2 + 1))
      change unzigzag (2 * (left / 2 + right / 2 + 1) + 1) = Int.negSucc (left / 2 + right / 2 + 1) at code
      rw [code]
      simp only [unzigzag, leftSign, rightSign, ite_false, Int.ofNat_eq_natCast]
      omega

theorem add_correct (left right : Int) : addCode (zigzag left) (zigzag right) = zigzag (left + right) := by
  apply unzigzag_injective
  rw [add_decode, unzigzag_zigzag, unzigzag_zigzag, unzigzag_zigzag]

theorem add_primrec : Primrec₂ addCode := by
  have leftHalf : Primrec (fun input : Nat × Nat => input.1 / 2) := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have rightHalf : Primrec (fun input : Nat × Nat => input.2 / 2) := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have leftSign : PrimrecPred (fun input : Nat × Nat => input.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have rightSign : PrimrecPred (fun input : Nat × Nat => input.2 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  have magnitude := Primrec.nat_add.comp leftHalf rightHalf
  exact Primrec.ite leftSign
    (Primrec.ite rightSign (Primrec.nat_mul.comp (Primrec.const 2) magnitude)
      (difference_primrec.comp leftHalf (Primrec.succ.comp rightHalf)))
    (Primrec.ite rightSign (difference_primrec.comp rightHalf (Primrec.succ.comp leftHalf))
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp magnitude))))

@[expose] def negateCode (word : Nat) : Nat :=
  if word % 2 = 0 then differenceCode 0 (word / 2) else 2 * (word / 2 + 1)

theorem negate_decode (word : Nat) : unzigzag (negateCode word) = - unzigzag word := by
  unfold negateCode
  split <;> rename_i sign
  · rw [difference_decode]
    simp [unzigzag, sign]
  · have code := unzigzag_zigzag (Int.ofNat (word / 2 + 1))
    change unzigzag (2 * (word / 2 + 1)) = Int.ofNat (word / 2 + 1) at code
    rw [code]
    simp only [unzigzag, sign, ite_false, Int.ofNat_eq_natCast]
    omega

theorem negate_correct (word : Int) : negateCode (zigzag word) = zigzag (-word) := by
  apply unzigzag_injective
  rw [negate_decode, unzigzag_zigzag, unzigzag_zigzag]

theorem negate_primrec : Primrec negateCode := by
  have half : Primrec (fun word : Nat => word / 2) := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (difference_primrec.comp (Primrec.const 0) half)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp half))

@[expose] def subtractCode (left right : Nat) : Nat := addCode left (negateCode right)

theorem subtract_decode (left right : Nat) : unzigzag (subtractCode left right) = unzigzag left - unzigzag right := by
  simp only [subtractCode, add_decode, negate_decode, sub_eq_add_neg]

theorem subtract_correct (left right : Int) : subtractCode (zigzag left) (zigzag right) = zigzag (left - right) := by
  apply unzigzag_injective
  rw [subtract_decode, unzigzag_zigzag, unzigzag_zigzag, unzigzag_zigzag]

theorem subtract_primrec : Primrec₂ subtractCode :=
  add_primrec.comp Primrec.fst (negate_primrec.comp Primrec.snd)

@[expose] def lessCode (left right : Nat) : Bool :=
  if left % 2 = 0 then
    if right % 2 = 0 then decide (left / 2 < right / 2) else false
  else if right % 2 = 0 then true else decide (right / 2 < left / 2)

theorem less_decode (left right : Nat) : lessCode left right = true ↔ unzigzag left < unzigzag right := by
  unfold lessCode
  split <;> rename_i leftSign
  all_goals
    split <;> rename_i rightSign
    all_goals
      simp only [unzigzag, leftSign, rightSign, ite_true, ite_false,
        decide_eq_true_eq, Bool.false_eq_true, Int.negSucc_eq, Int.ofNat_eq_natCast]
      constructor <;> intro hypothesis <;> first | trivial | omega

theorem less_correct (left right : Int) : lessCode (zigzag left) (zigzag right) = decide (left < right) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq, unzigzag_zigzag] using less_decode (zigzag left) (zigzag right)

theorem less_primrec : Primrec₂ lessCode := by
  have leftHalf : Primrec (fun input : Nat × Nat => input.1 / 2) := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have rightHalf : Primrec (fun input : Nat × Nat => input.2 / 2) := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have leftSign : PrimrecPred (fun input : Nat × Nat => input.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have rightSign : PrimrecPred (fun input : Nat × Nat => input.2 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  exact Primrec.ite leftSign
    (Primrec.ite rightSign (Primrec.nat_lt.decide.comp leftHalf rightHalf) (Primrec.const false))
    (Primrec.ite rightSign (Primrec.const true) (Primrec.nat_lt.decide.comp rightHalf leftHalf))

@[expose] def borrowCode (carry : Bool) : Nat := if carry then 2 else 0

theorem borrow_correct (carry : Bool) : borrowCode carry = zigzag (SMC.borrowWord carry) := by cases carry <;> rfl

theorem borrow_primrec : Primrec borrowCode := by
  exact (Primrec.cond Primrec.id (Primrec.const 2) (Primrec.const 0)).of_eq fun carry => by cases carry <;> rfl

@[expose] def subtractBorrowCode (word : Nat) (carry : Bool) : Nat := subtractCode word (borrowCode carry)

theorem subtract_borrow_correct (word : Int) (carry : Bool) :
    subtractBorrowCode (zigzag word) carry = zigzag (word - SMC.borrowWord carry) := by
  rw [subtractBorrowCode, borrow_correct, subtract_correct]

theorem subtract_borrow_primrec : Primrec₂ subtractBorrowCode :=
  subtract_primrec.comp Primrec.fst (borrow_primrec.comp Primrec.snd)

end SmcTuring.SMC.Effective
