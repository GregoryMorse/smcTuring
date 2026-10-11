module
public import SmcTuring.SMC.ComputableArithmetic
import all Init.Data.Nat.Bitwise.Basic

public section

namespace SmcTuring.SMC.Effective

/-- Every binary Boolean truth table is finite and primitive recursive. -/
theorem boolean_binary_primrec (operation : Bool → Bool → Bool) : Primrec₂ operation := by
  exact (Primrec.cond Primrec.fst
    (Primrec.cond Primrec.snd (Primrec.const (operation true true)) (Primrec.const (operation true false)))
    (Primrec.cond Primrec.snd (Primrec.const (operation false true)) (Primrec.const (operation false false)))).of_eq
      fun input => by rcases input with ⟨left, right⟩; cases left <;> cases right <;> rfl

/-- Only nonzero pairs need a recursive call, and both arguments are halved. -/
@[expose] def bitwiseChildren (input : Nat × Nat) : List (Nat × Nat) :=
  if input.1 = 0 then [] else if input.2 = 0 then [] else [(input.1 / 2, input.2 / 2)]

@[expose] def bitwiseCombine (operation : Bool → Bool → Bool) (input : Nat × Nat) (answers : List Nat) : Option Nat :=
  some (if input.1 = 0 then
    if operation false true then input.2 else 0
  else if input.2 = 0 then
    if operation true false then input.1 else 0
  else
    let previous := answers.head?.getD 0
    if operation (decide (input.1 % 2 = 1)) (decide (input.2 % 2 = 1)) then
      previous + previous + 1
    else previous + previous)

theorem bitwise_children_primrec : Primrec bitwiseChildren := by
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
          (Primrec.nat_div.comp Primrec.snd (Primrec.const 2))) (Primrec.const [])))

theorem bitwise_children_decrease (input child : Nat × Nat) (member : child ∈ bitwiseChildren input) :
    child.1 + child.2 < input.1 + input.2 := by
  unfold bitwiseChildren at member
  split at member <;> rename_i left
  · simp at member
  · split at member <;> rename_i right
    · simp at member
    · have same : child = (input.1 / 2, input.2 / 2) := by simpa using member
      subst child
      have leftLess := Nat.bitwise_rec_lemma left
      have rightLess := Nat.bitwise_rec_lemma right
      omega

theorem bitwise_combine_primrec (operation : Bool → Bool → Bool) : Primrec₂ (bitwiseCombine operation) := by
  have leftField : Primrec (fun input : (Nat × Nat) × List Nat => input.1.1) := Primrec.fst.comp Primrec.fst
  have rightField : Primrec (fun input : (Nat × Nat) × List Nat => input.1.2) := Primrec.snd.comp Primrec.fst
  have previous : Primrec (fun input : (Nat × Nat) × List Nat => input.2.head?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.snd) (Primrec.const 0)
  have doubled := Primrec.nat_add.comp previous previous
  have bit : Primrec (fun input : (Nat × Nat) × List Nat =>
      operation (decide (input.1.1 % 2 = 1)) (decide (input.1.2 % 2 = 1))) :=
    (boolean_binary_primrec operation).comp
      ((Primrec.eq.comp (Primrec.nat_mod.comp leftField (Primrec.const 2)) (Primrec.const 1)).decide)
      ((Primrec.eq.comp (Primrec.nat_mod.comp rightField (Primrec.const 2)) (Primrec.const 1)).decide)
  exact (Primrec.option_some.comp
    (Primrec.ite (Primrec.eq.comp leftField (Primrec.const 0))
      (Primrec.cond (Primrec.const (operation false true)) rightField (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp rightField (Primrec.const 0))
        (Primrec.cond (Primrec.const (operation true false)) leftField (Primrec.const 0))
        (Primrec.cond bit (Primrec.succ.comp doubled) doubled)))).of_eq
          fun input => by simp only [bitwiseCombine, Bool.cond_eq_ite]

theorem bitwise_combine_correct (operation : Bool → Bool → Bool) (input : Nat × Nat) :
    bitwiseCombine operation input ((bitwiseChildren input).map (fun pair => Nat.bitwise operation pair.1 pair.2)) =
      some (Nat.bitwise operation input.1 input.2) := by
  by_cases left : input.1 = 0
  · unfold bitwiseCombine
    rw [ite_eq_left left]
    conv_rhs => rw [Nat.bitwise]
    simp only [left, ite_true]
  · by_cases right : input.2 = 0
    · unfold bitwiseCombine
      rw [ite_eq_right left, ite_eq_left right]
      conv_rhs => rw [Nat.bitwise]
      simp only [left, right, ite_false, ite_true]
    · conv_rhs => rw [Nat.bitwise]
      simp only [left, right, ite_false, bitwiseChildren, bitwiseCombine,
        List.map_cons, List.map_nil, List.head?_cons, Option.getD_some]

/-- The actual Lean natural-number bitwise operation is primitive recursive.
The decreasing-call certificate covers arbitrary finite Boolean truth tables. -/
theorem nat_bitwise_primrec (operation : Bool → Bool → Bool) : Primrec₂ (Nat.bitwise operation) := by
  exact Primrec.nat_omega_rec' (fun input : Nat × Nat => Nat.bitwise operation input.1 input.2)
    Primrec.nat_add bitwise_children_primrec (bitwise_combine_primrec operation)
    bitwise_children_decrease (bitwise_combine_correct operation)

theorem nat_and_primrec : Primrec₂ Nat.land := nat_bitwise_primrec Bool.and

theorem nat_or_primrec : Primrec₂ Nat.lor := nat_bitwise_primrec Bool.or

theorem nat_xor_primrec : Primrec₂ Nat.xor := nat_bitwise_primrec (· != ·)

/-- Signed XOR on canonical natural codes. Negative integers are represented
by a complemented magnitude; the low code bit records that complement. -/
@[expose] def xorCode (left right : Nat) : Nat :=
  let magnitude := (left / 2) ^^^ (right / 2)
  if left % 2 = right % 2 then 2 * magnitude else 2 * magnitude + 1

@[expose] def andCode (left right : Nat) : Nat :=
  let common := (left / 2) &&& (right / 2)
  if left % 2 = 0 then
    if right % 2 = 0 then 2 * common else 2 * ((left / 2) ^^^ common)
  else if right % 2 = 0 then 2 * ((right / 2) ^^^ common)
  else 2 * ((left / 2) ||| (right / 2)) + 1

theorem xor_correct (left right : Int) :
    xorCode (Dolan.Encoding.zigzag left) (Dolan.Encoding.zigzag right) = Dolan.Encoding.zigzag (SMC.xorWord left right) := by
  have oddHalf (number : Nat) : (number * 2 + 1) / 2 = number := by omega
  cases left <;> cases right <;> simp [xorCode, Dolan.Encoding.zigzag, SMC.xorWord, Nat.mul_comm, oddHalf]

theorem and_correct (left right : Int) :
    andCode (Dolan.Encoding.zigzag left) (Dolan.Encoding.zigzag right) = Dolan.Encoding.zigzag (SMC.andWord left right) := by
  have oddHalf (number : Nat) : (number * 2 + 1) / 2 = number := by omega
  cases left <;> cases right <;> simp [andCode, Dolan.Encoding.zigzag, SMC.andWord, Nat.mul_comm, oddHalf]

theorem xor_decode (left right : Nat) :
    Dolan.Encoding.unzigzag (xorCode left right) = SMC.xorWord (Dolan.Encoding.unzigzag left) (Dolan.Encoding.unzigzag right) := by
  have encoded := xor_correct (Dolan.Encoding.unzigzag left) (Dolan.Encoding.unzigzag right)
  simp only [zigzag_unzigzag] at encoded
  rw [encoded, Dolan.Encoding.unzigzag_zigzag]

theorem and_decode (left right : Nat) :
    Dolan.Encoding.unzigzag (andCode left right) = SMC.andWord (Dolan.Encoding.unzigzag left) (Dolan.Encoding.unzigzag right) := by
  have encoded := and_correct (Dolan.Encoding.unzigzag left) (Dolan.Encoding.unzigzag right)
  simp only [zigzag_unzigzag] at encoded
  rw [encoded, Dolan.Encoding.unzigzag_zigzag]

theorem xor_primrec : Primrec₂ xorCode := by
  have leftHalf : Primrec (fun input : Nat × Nat => input.1 / 2) := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have rightHalf : Primrec (fun input : Nat × Nat => input.2 / 2) := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have doubled := Primrec.nat_mul.comp (Primrec.const 2) (nat_xor_primrec.comp leftHalf rightHalf)
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))) doubled (Primrec.succ.comp doubled)

theorem and_primrec : Primrec₂ andCode := by
  have leftHalf : Primrec (fun input : Nat × Nat => input.1 / 2) := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have rightHalf : Primrec (fun input : Nat × Nat => input.2 / 2) := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have leftSign : PrimrecPred (fun input : Nat × Nat => input.1 % 2 = 0) := Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have rightSign : PrimrecPred (fun input : Nat × Nat => input.2 % 2 = 0) := Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  have common := nat_and_primrec.comp leftHalf rightHalf
  exact Primrec.ite leftSign
    (Primrec.ite rightSign (Primrec.nat_mul.comp (Primrec.const 2) common)
      (Primrec.nat_mul.comp (Primrec.const 2) (nat_xor_primrec.comp leftHalf common)))
    (Primrec.ite rightSign (Primrec.nat_mul.comp (Primrec.const 2) (nat_xor_primrec.comp rightHalf common))
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (nat_or_primrec.comp leftHalf rightHalf))))

end SmcTuring.SMC.Effective
