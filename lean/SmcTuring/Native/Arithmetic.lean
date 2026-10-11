module
public import SmcTuring.Native.Layout

public section

namespace SmcTuring.Native.Arithmetic

/-- The unsigned borrow bit used by the selected SUB form. Other flags are
not observed by this guard; their complete CPU refinement is separate. -/
@[expose] def unsignedBorrow {mode : Mode} (left right : Word mode) : Bool :=
  decide (left.toNat < right.toNat)

/-- The selected SBB destination and immediate are both zero. -/
@[expose] def sbbZero (mode : Mode) (carry : Bool) : Word mode :=
  (0 : Word mode) - 0 - (if carry then 1 else 0)

@[expose] def maskSelect {mode : Mode} (continuation terminal mask : Word mode) : Word mode :=
  ((continuation ^^^ terminal) &&& mask) ^^^ continuation

@[expose] def selectAfterSub (mode : Mode) (candidate boundary continuation terminal : Word mode) : Word mode :=
  maskSelect continuation terminal (sbbZero mode (unsignedBorrow candidate boundary))

@[expose] def encodeNat (mode : Mode) (value : Nat) : Word mode :=
  BitVec.ofNat (8 * mode.wordBytes) value
@[expose] def offsetValue (mode : Mode) (choice : Bool) : Nat := if choice then mode.stride else 0
@[expose] def encodeOffset (mode : Mode) (choice : Bool) : Word mode := encodeNat mode (offsetValue mode choice)
@[expose] def heapWord (mode : Mode) (base cell : Nat) (second : Bool) : Word mode :=
  encodeNat mode (Layout.heapField mode base cell second)

/-- Borrow produces exactly the all-ones word; no borrow produces zero. -/
theorem sbb_zero_mask (mode : Mode) (carry : Bool) :
    sbbZero mode carry = if carry then BitVec.allOnes (8 * mode.wordBytes) else 0 := by
  cases carry <;> simp [sbbZero, BitVec.neg_one_eq_allOnes]

/-- This finite-width XOR/AND/XOR sequence selects arbitrary full words. -/
theorem xor_mask_select (mode : Mode) (continuation terminal : Word mode) (carry : Bool) :
    maskSelect continuation terminal (sbbZero mode carry) = if carry then terminal else continuation := by
  rw [sbb_zero_mask]
  cases carry with
  | false => simp [maskSelect]
  | true =>
    change (((continuation ^^^ terminal) &&& BitVec.allOnes (8 * mode.wordBytes)) ^^^ continuation) = terminal
    rw [BitVec.and_allOnes, BitVec.xor_comm continuation terminal, BitVec.xor_assoc]
    simp

theorem select_sub_borrow (mode : Mode) (candidate boundary continuation terminal : Word mode) :
    selectAfterSub mode candidate boundary continuation terminal =
      if candidate.toNat < boundary.toNat then terminal else continuation := by
  by_cases before : candidate.toNat < boundary.toNat <;>
    simp [selectAfterSub, unsignedBorrow, before, xor_mask_select]

/-- A capacity premise prevents modular encoding from identifying different addresses. -/
theorem encode_nat_toNat (mode : Mode) (value : Nat) (fits : value < 2 ^ (8 * mode.wordBytes)) :
    (encodeNat mode value).toNat = value := by
  simp [encodeNat, Nat.mod_eq_of_lt fits]

theorem borrow_encode_nat (mode : Mode) (left right : Nat)
    (leftFits : left < 2 ^ (8 * mode.wordBytes)) (rightFits : right < 2 ^ (8 * mode.wordBytes)) :
    unsignedBorrow (encodeNat mode left) (encodeNat mode right) = decide (left < right) := by
  unfold unsignedBorrow
  rw [encode_nat_toNat mode left leftFits, encode_nat_toNat mode right rightFits]

theorem offset_below_boundary (mode : Mode) (base : Nat) (choice : Bool) :
    offsetValue mode choice < Layout.heapBase mode base := by
  have low := Layout.boolean_offsets_below_boundary mode base
  cases choice <;> simp [offsetValue] <;> omega

theorem offset_borrow (mode : Mode) (base : Nat) (choice : Bool)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) :
    unsignedBorrow (encodeOffset mode choice) (encodeNat mode (Layout.heapBase mode base)) = true := by
  have low := offset_below_boundary mode base choice
  have fits := Nat.lt_trans low boundaryFits
  unfold encodeOffset
  rw [borrow_encode_nat mode _ _ fits boundaryFits]
  simp [low]

theorem heap_borrow (mode : Mode) (base cell : Nat) (second : Bool)
    (fieldFits : Layout.heapField mode base cell second < 2 ^ (8 * mode.wordBytes)) :
    unsignedBorrow (heapWord mode base cell second) (encodeNat mode (Layout.heapBase mode base)) = false := by
  have high := Layout.heap_at_or_above_boundary mode base cell second
  have boundaryFits := Nat.lt_of_le_of_lt high fieldFits
  unfold heapWord
  rw [borrow_encode_nat mode _ _ fieldFits boundaryFits]
  simp [Nat.not_lt_of_ge high]

theorem base_guard_accepts_heap (mode : Mode) (base cell : Nat) (second : Bool)
    (continuation terminal : Word mode)
    (fieldFits : Layout.heapField mode base cell second < 2 ^ (8 * mode.wordBytes)) :
    selectAfterSub mode (heapWord mode base cell second) (encodeNat mode (Layout.heapBase mode base))
      continuation terminal = continuation := by
  unfold selectAfterSub
  rw [heap_borrow mode base cell second fieldFits, xor_mask_select]
  rfl

theorem base_guard_rejects_offset (mode : Mode) (base : Nat) (choice : Bool)
    (continuation terminal : Word mode)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) :
    selectAfterSub mode (encodeOffset mode choice) (encodeNat mode (Layout.heapBase mode base))
      continuation terminal = terminal := by
  unfold selectAfterSub
  rw [offset_borrow mode base choice boundaryFits, xor_mask_select]
  rfl

/-- The offset guard exchanges the two selection targets. -/
theorem offset_guard_accepts_offset (mode : Mode) (base : Nat) (choice : Bool)
    (continuation terminal : Word mode)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) :
    selectAfterSub mode (encodeOffset mode choice) (encodeNat mode (Layout.heapBase mode base))
      terminal continuation = continuation := by
  exact base_guard_rejects_offset mode base choice terminal continuation boundaryFits

theorem offset_guard_rejects_heap (mode : Mode) (base cell : Nat) (second : Bool)
    (continuation terminal : Word mode)
    (fieldFits : Layout.heapField mode base cell second < 2 ^ (8 * mode.wordBytes)) :
    selectAfterSub mode (heapWord mode base cell second) (encodeNat mode (Layout.heapBase mode base))
      terminal continuation = terminal := by
  exact base_guard_accepts_heap mode base cell second terminal continuation fieldFits

/-- Whole-word native addition computes the selected adjacent operand field. -/
theorem indexed_heap_address (mode : Mode) (base cell : Nat) (choice : Bool) :
    heapWord mode base cell false + encodeOffset mode choice = heapWord mode base cell choice := by
  cases choice with
  | false => simp [heapWord, encodeOffset, offsetValue, encodeNat]
  | true =>
    change BitVec.ofNat (8 * mode.wordBytes) (Layout.heapField mode base cell false) +
      BitVec.ofNat (8 * mode.wordBytes) mode.stride =
      BitVec.ofNat (8 * mode.wordBytes) (Layout.heapField mode base cell true)
    rw [BitVec.ofNat_add_ofNat, Layout.heap_second_field]

/-- Under capacity the computed pointer is the actual natural address, without wrap. -/
theorem indexed_heap_address_toNat (mode : Mode) (base cell : Nat) (choice : Bool)
    (fieldFits : Layout.heapField mode base cell choice < 2 ^ (8 * mode.wordBytes)) :
    (heapWord mode base cell false + encodeOffset mode choice).toNat = Layout.heapField mode base cell choice := by
  rw [indexed_heap_address]
  exact encode_nat_toNat mode _ fieldFits

end SmcTuring.Native.Arithmetic
