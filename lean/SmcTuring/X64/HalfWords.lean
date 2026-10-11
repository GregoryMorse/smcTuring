module
public import SmcTuring.Native.Arithmetic
public import Mathlib.Tactic.NormNum

public section

namespace SmcTuring.X64.HalfWords

/-- Low-address and high-address 32-bit halves of a little-endian word.
This algebraic contract assumes distinct, nonoverlapping half-word fields;
it does not certify printed operand locations or arbitrary ISA operations. -/
@[expose] def low (word : BitVec 64) : BitVec 32 := word.extractLsb' 0 32
@[expose] def high (word : BitVec 64) : BitVec 32 := word.extractLsb' 32 32
@[expose] def pack (lo hi : BitVec 32) : BitVec 64 := hi ++ lo

/-- The printed USEWORDOP64 pattern uses the corresponding source half. -/
@[expose] def splitBinary (op : BitVec 32 → BitVec 32 → BitVec 32)
    (left right : BitVec 64) : BitVec 64 :=
  pack (op (low left) (low right)) (op (high left) (high right))

/-- The printed OP64 immediate form repeats the same 32-bit operand.
Its full-width mask is a repeated half, not generally a zero extension. -/
@[expose] def repeated (data : BitVec 32) : BitVec 64 := pack data data
@[expose] def broadcast (op : BitVec 32 → BitVec 32 → BitVec 32)
    (word : BitVec 64) (data : BitVec 32) : BitVec 64 :=
  pack (op (low word) data) (op (high word) data)
@[expose] def splitNot (word : BitVec 64) : BitVec 64 :=
  pack (~~~ low word) (~~~ high word)

/-- Correct high-half addition includes the low-half carry. -/
@[expose] def addCarry (left right : BitVec 64) : BitVec 64 :=
  pack (low left + low right)
    (high left + high right + (if (low left).uaddOverflow (low right) then 1 else 0))

/-- Correct high-half subtraction includes the low-half borrow. -/
@[expose] def subBorrow (left right : BitVec 64) : BitVec 64 :=
  pack (low left - low right)
    (high left - high right - (if (low left).usubOverflow (low right) then 1 else 0))

theorem low_pack (lo hi : BitVec 32) : low (pack lo hi) = lo := by
  exact BitVec.extractLsb'_append_eq_right

theorem high_pack (lo hi : BitVec 32) : high (pack lo hi) = hi := by
  exact BitVec.extractLsb'_append_eq_left

theorem pack_halves (word : BitVec 64) : pack (low word) (high word) = word := by
  exact BitVec.extractLsb'_append_extractLsb'

theorem split_xor (left right : BitVec 64) :
    splitBinary (fun x y => x ^^^ y) left right = left ^^^ right := by
  unfold splitBinary pack
  rw [← BitVec.xor_append]
  change pack (low left) (high left) ^^^ pack (low right) (high right) = _
  rw [pack_halves, pack_halves]

theorem split_and (left right : BitVec 64) :
    splitBinary (fun x y => x &&& y) left right = left &&& right := by
  unfold splitBinary pack
  rw [← BitVec.and_append]
  change pack (low left) (high left) &&& pack (low right) (high right) = _
  rw [pack_halves, pack_halves]

theorem split_or (left right : BitVec 64) :
    splitBinary (fun x y => x ||| y) left right = left ||| right := by
  unfold splitBinary pack
  rw [← BitVec.or_append]
  change pack (low left) (high left) ||| pack (low right) (high right) = _
  rw [pack_halves, pack_halves]

theorem split_not (word : BitVec 64) : splitNot word = ~~~ word := by
  unfold splitNot pack
  rw [← BitVec.not_append]
  change ~~~ pack (low word) (high word) = _
  rw [pack_halves]

theorem split_mov (left right : BitVec 64) :
    splitBinary (fun _ y => y) left right = right := by
  exact pack_halves right

theorem broadcast_as_repeated (op : BitVec 32 → BitVec 32 → BitVec 32)
    (word : BitVec 64) (data : BitVec 32) :
    broadcast op word data = splitBinary op word (repeated data) := by
  simp [broadcast, splitBinary, repeated, low_pack, high_pack]

theorem broadcast_xor (word : BitVec 64) (data : BitVec 32) :
    broadcast (fun x y => x ^^^ y) word data = word ^^^ repeated data := by
  rw [broadcast_as_repeated, split_xor]

theorem broadcast_and (word : BitVec 64) (data : BitVec 32) :
    broadcast (fun x y => x &&& y) word data = word &&& repeated data := by
  rw [broadcast_as_repeated, split_and]

theorem broadcast_or (word : BitVec 64) (data : BitVec 32) :
    broadcast (fun x y => x ||| y) word data = word ||| repeated data := by
  rw [broadcast_as_repeated, split_or]

theorem broadcast_mov (word : BitVec 64) (data : BitVec 32) :
    broadcast (fun _ y => y) word data = repeated data := by
  rfl

theorem pack_toNat (lo hi : BitVec 32) :
    (pack lo hi).toNat = hi.toNat * 4294967296 + lo.toNat := by
  rw [pack, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq]

theorem add_carry (left right : BitVec 64) : addCarry left right = left + right := by
  have ll := (low left).isLt
  have lr := (low right).isLt
  have hl := (high left).isLt
  have hr := (high right).isLt
  have leftValue := pack_toNat (low left) (high left)
  have rightValue := pack_toNat (low right) (high right)
  rw [pack_halves] at leftValue rightValue
  apply BitVec.eq_of_toNat_eq
  by_cases carry : (low left).uaddOverflow (low right) = true
  · simp only [addCarry, carry, ite_true, pack_toNat, BitVec.toNat_add]
    simp only [BitVec.uaddOverflow, decide_eq_true_eq] at carry
    norm_num [BitVec.toNat_ofNat] at *
    omega
  · have noCarry : (low left).uaddOverflow (low right) = false :=
      Bool.eq_false_iff.mpr carry
    simp only [addCarry, noCarry, Bool.false_eq_true, ite_false, pack_toNat,
      BitVec.toNat_add]
    simp only [BitVec.uaddOverflow, decide_eq_true_eq] at carry
    norm_num [BitVec.toNat_ofNat] at *
    omega

theorem sub_borrow (left right : BitVec 64) : subBorrow left right = left - right := by
  have ll := (low left).isLt
  have lr := (low right).isLt
  have hl := (high left).isLt
  have hr := (high right).isLt
  have leftValue := pack_toNat (low left) (high left)
  have rightValue := pack_toNat (low right) (high right)
  rw [pack_halves] at leftValue rightValue
  apply BitVec.eq_of_toNat_eq
  by_cases borrow : (low left).usubOverflow (low right) = true
  · simp only [subBorrow, borrow, ite_true, pack_toNat, BitVec.toNat_sub]
    simp only [BitVec.usubOverflow, decide_eq_true_eq] at borrow
    norm_num [BitVec.toNat_ofNat] at *
    omega
  · have noBorrow : (low left).usubOverflow (low right) = false :=
      Bool.eq_false_iff.mpr borrow
    simp only [subBorrow, noBorrow, Bool.false_eq_true, ite_false, pack_toNat,
      BitVec.toNat_sub]
    simp only [BitVec.usubOverflow, decide_eq_true_eq] at borrow
    norm_num [BitVec.toNat_ofNat] at *
    omega

theorem split_add_no_carry (left right : BitVec 64)
    (noCarry : (low left).uaddOverflow (low right) = false) :
    splitBinary (fun x y => x + y) left right = left + right := by
  rw [← add_carry]
  simp [splitBinary, addCarry, noCarry]

theorem split_sub_no_borrow (left right : BitVec 64)
    (noBorrow : (low left).usubOverflow (low right) = false) :
    splitBinary (fun x y => x - y) left right = left - right := by
  rw [← sub_borrow]
  simp [splitBinary, subBorrow, noBorrow]

/-- Omitting propagation loses the carry from 0xffffffff + 1. -/
theorem split_add_counterexample :
    splitBinary (fun x y => x + y) 4294967295 1 = 0 ∧
    (4294967295 : BitVec 64) + 1 = 4294967296 := by
  decide

/-- Omitting propagation loses the borrow from zero minus one. -/
theorem split_sub_counterexample :
    splitBinary (fun x y => x - y) 0 1 = 4294967295 ∧
    (0 : BitVec 64) - 1 = 18446744073709551615 := by
  decide

/-- Repeated immediate assignment of one is not 64-bit assignment of one. -/
theorem repeated_one_counterexample :
    repeated 1 = 4294967297 ∧ repeated 1 ≠ (1 : BitVec 64) := by
  decide

/-- The masks actually used for clearing and complementing do lift exactly. -/
theorem repeated_masks :
    repeated 0 = 0 ∧ repeated (~~~ (0 : BitVec 32)) = ~~~ (0 : BitVec 64) := by
  decide

end SmcTuring.X64.HalfWords
