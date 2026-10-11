module
public import SmcTuring.Native.ByteMemory

public section

namespace SmcTuring.Native

/-- The native generator separates consecutive operand fields by two words. -/
@[expose] def Mode.stride (mode : Mode) : Nat := 2 * mode.wordBytes

namespace Layout

@[expose] def fieldAddress (mode : Mode) (base index : Nat) : Nat := base + mode.stride * index
@[expose] def templatePC (mode : Mode) (base index : Nat) : Nat :=
  fieldAddress mode base index - moffsOperandOffset mode

@[expose] def registerField (mode : Mode) (base : Nat) (register : Fin 13) : Nat :=
  fieldAddress mode base register.val
@[expose] def heapBase (mode : Mode) (base : Nat) : Nat := fieldAddress mode base 13
@[expose] def heapField (mode : Mode) (base cell : Nat) (second : Bool) : Nat :=
  fieldAddress mode base (13 + 2 * cell + if second then 1 else 0)

/-- Each owner starts before its operand; base reserves its opcode bytes. -/
theorem owner_field_address (mode : Mode) (base index : Nat)
    (enough : moffsOperandOffset mode ≤ base) :
    templatePC mode base index + moffsOperandOffset mode = fieldAddress mode base index := by
  have fits : moffsOperandOffset mode ≤ fieldAddress mode base index := by unfold fieldAddress; omega
  exact Nat.sub_add_cancel fits

/-- A field write cannot reach the next owner's opcode bytes. -/
theorem fields_and_owners_disjoint (mode : Mode) (base first second : Nat) (before : first < second) :
    fieldAddress mode base first + mode.wordBytes ≤ templatePC mode base second := by
  cases mode <;> simp [fieldAddress, templatePC, Mode.stride, Mode.wordBytes, moffsOperandOffset, wordPrefix] <;> omega

theorem field_address_injective (mode : Mode) (base : Nat) : Function.Injective (fieldAddress mode base) := by
  intro first second same
  cases mode <;> simp [fieldAddress, Mode.stride, Mode.wordBytes] at same <;> omega

/-- Operand alignment is inherited from the first field of the affine grid. -/
theorem field_alignment (mode : Mode) (base index : Nat) :
    fieldAddress mode base index % mode.wordBytes = base % mode.wordBytes := by
  cases mode <;> simp [fieldAddress, Mode.stride, Mode.wordBytes, Nat.add_mod, Nat.mul_mod]

/-- Register storage lies before the heap, including its complete word width. -/
theorem register_before_heap (mode : Mode) (base : Nat) (register : Fin 13) :
    registerField mode base register + mode.wordBytes ≤ heapBase mode base := by
  have small := register.isLt
  cases mode <;> simp [registerField, heapBase, fieldAddress, Mode.stride, Mode.wordBytes] <;> omega

/-- Heap pointer values are at or above the guard boundary. -/
theorem heap_at_or_above_boundary (mode : Mode) (base cell : Nat) (second : Bool) :
    heapBase mode base ≤ heapField mode base cell second := by
  cases mode <;> cases second <;> simp [heapBase, heapField, fieldAddress, Mode.stride, Mode.wordBytes] <;> omega

/-- Both Boolean offsets are strictly below the same native guard boundary. -/
theorem boolean_offsets_below_boundary (mode : Mode) (base : Nat) :
    0 < heapBase mode base ∧ mode.stride < heapBase mode base := by
  cases mode <;> simp [heapBase, fieldAddress, Mode.stride, Mode.wordBytes]

/-- Adjacent halves are different whole operand fields; offsets select the second. -/
theorem heap_second_field (mode : Mode) (base cell : Nat) :
    heapField mode base cell true = heapField mode base cell false + mode.stride := by
  cases mode <;> simp [heapField, fieldAddress, Mode.stride, Mode.wordBytes] <;> omega

/-- A finite prefix fits the address space only under an explicit capacity bound. -/
theorem finite_capacity (mode : Mode) (base count index : Nat) (inside : index < count)
    (capacity : base + mode.stride * count ≤ 2 ^ (8 * mode.wordBytes)) :
    fieldAddress mode base index + mode.wordBytes ≤ 2 ^ (8 * mode.wordBytes) := by
  cases mode <;> simp [fieldAddress, Mode.stride, Mode.wordBytes] at * <;> omega

/-- Word stores at distinct grid indices preserve all bytes of the other field. -/
theorem other_field_frame (mode : Mode) (memory : ByteMemory.Memory) (base first second : Nat)
    (different : first ≠ second) (value : Word mode) :
    ByteMemory.bytesAt (ByteMemory.putWord mode memory (fieldAddress mode base first) value)
        (fieldAddress mode base second) mode.wordBytes =
      ByteMemory.bytesAt memory (fieldAddress mode base second) mode.wordBytes := by
  apply ByteMemory.bytes_at_frame
  intro offset
  have small := offset.isLt
  simp only [LittleEndian.word_encode_length]
  unfold ByteMemory.Inside
  cases mode <;> simp [fieldAddress, Mode.stride, Mode.wordBytes] at * <;> omega

end Layout
end SmcTuring.Native
