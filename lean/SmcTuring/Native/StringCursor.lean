module
public import SmcTuring.Native.StringPlan
public import SmcTuring.Native.Arithmetic

public section
namespace SmcTuring.Native.StringCursor

structure Cursor (mode : Mode) where
  index : Word mode
  field : Word mode

@[expose] def exchange (mode : Mode) (cursor : Cursor mode) : Cursor mode := ⟨cursor.field, cursor.index⟩
@[expose] def advance (mode : Mode) (size : Nat) (cursor : Cursor mode) : Cursor mode := ⟨cursor.index + Arithmetic.encodeNat mode size, cursor.field⟩
@[expose] def subtract (mode : Mode) (size : Nat) (cursor : Cursor mode) : Cursor mode := ⟨cursor.index, cursor.field - Arithmetic.encodeNat mode size⟩
@[expose] def finish (mode : Mode) (size : Nat) (cursor : Cursor mode) : Cursor mode :=
  subtract mode size (exchange mode (advance mode size (exchange mode cursor)))
@[expose] def finalCarry (mode : Mode) (size : Nat) (cursor : Cursor mode) : Bool :=
  Arithmetic.unsignedBorrow (cursor.field + Arithmetic.encodeNat mode size) (Arithmetic.encodeNat mode size)

theorem exchange_twice (mode : Mode) (cursor : Cursor mode) : exchange mode (exchange mode cursor) = cursor := rfl

/-- Swapping with the declared cursor field and subtracting the MOVS byte count
restores both the original index register and pointer field, modulo its width. -/
theorem effect (mode : Mode) (size : Nat) (cursor : Cursor mode) : finish mode size cursor = cursor := by
  unfold finish subtract exchange advance
  have cancel := BitVec.add_sub_cancel cursor.field (Arithmetic.encodeNat mode size)
  rw [cancel]

theorem advanced_pointer (mode : Mode) (size : Nat) (cursor : Cursor mode) :
    (advance mode size (exchange mode cursor)).index = cursor.field + Arithmetic.encodeNat mode size := rfl

theorem restored_index (mode : Mode) (size : Nat) (cursor : Cursor mode) : (finish mode size cursor).index = cursor.index := by rw [effect]

theorem restored_field (mode : Mode) (size : Nat) (cursor : Cursor mode) : (finish mode size cursor).field = cursor.field := by rw [effect]

theorem encoded_sum (mode : Mode) (address size : Nat) :
    Arithmetic.encodeNat mode address + Arithmetic.encodeNat mode size = Arithmetic.encodeNat mode (address + size) :=
  BitVec.ofNat_add_ofNat address size

theorem advanced_toNat (mode : Mode) (size address : Nat) (cursor : Cursor mode)
    (initial : cursor.field = Arithmetic.encodeNat mode address) (fits : address + size < 2 ^ (8 * mode.wordBytes)) :
    (advance mode size (exchange mode cursor)).index.toNat = address + size := by
  rw [advanced_pointer, initial, encoded_sum, Arithmetic.encode_nat_toNat mode _ fits]

theorem no_borrow (mode : Mode) (size address : Nat) (cursor : Cursor mode)
    (initial : cursor.field = Arithmetic.encodeNat mode address) (fits : address + size < 2 ^ (8 * mode.wordBytes)) :
    finalCarry mode size cursor = false := by
  have sizeFits : size < 2 ^ (8 * mode.wordBytes) := by omega
  unfold finalCarry Arithmetic.unsignedBorrow
  rw [initial, encoded_sum, Arithmetic.encode_nat_toNat mode _ fits, Arithmetic.encode_nat_toNat mode _ sizeFits]
  simp

/-- Two independent declared cursor fields suffice; arbitrary old SI/DI values
are restored. The last SUB clears CF under the static nonwrapping bound. -/
theorem pair_correct (mode : Mode) (size source destination : Nat) (si di : Cursor mode)
    (sourceInitial : si.field = Arithmetic.encodeNat mode source) (destinationInitial : di.field = Arithmetic.encodeNat mode destination)
    (sourceFits : source + size < 2 ^ (8 * mode.wordBytes)) (destinationFits : destination + size < 2 ^ (8 * mode.wordBytes)) :
    (advance mode size (exchange mode si)).index.toNat = source + size ∧
    (advance mode size (exchange mode di)).index.toNat = destination + size ∧
    finish mode size si = si ∧ finish mode size di = di ∧ finalCarry mode size di = false :=
  ⟨advanced_toNat mode size source si sourceInitial sourceFits, advanced_toNat mode size destination di destinationInitial destinationFits,
    effect mode size si, effect mode size di, no_borrow mode size destination di destinationInitial destinationFits⟩

end SmcTuring.Native.StringCursor
