module
public import SmcTuring.Native.Protected

public section

namespace SmcTuring.Native.GridImage

open LittleEndian

/-- Concrete repeating storage templates: MOFFS opcode, whole-word operand,
then padding. Natural addresses describe the sequential byte image; physical
finite-prefix realization still requires the mode's capacity bounds. -/
@[expose] def image (mode : Mode) (base : Nat) (values : Nat -> Word mode) : ByteMemory.Memory :=
  fun position =>
    let start := base - moffsOperandOffset mode
    if position < start then 0x90 else
    let relative := position - start
    let cell := relative / mode.stride
    let offset := relative % mode.stride
    if header : offset < moffsOperandOffset mode then
      (Protected.opcode mode)[offset]'(by cases mode <;> simpa [Protected.opcode, moffsOperandOffset] using header)
    else if data : offset < moffsOperandOffset mode + mode.wordBytes then
      (wordEncode mode.wordBytes (values cell))[offset - moffsOperandOffset mode]'(by rw [word_encode_length]; omega)
    else 0x90

theorem start_before (mode : Mode) (base cell offset : Nat) (enough : moffsOperandOffset mode <= base) :
    base - moffsOperandOffset mode <= Layout.templatePC mode base cell + offset := by
  cases mode <;> simp [Layout.templatePC, Layout.fieldAddress, Mode.stride, Mode.wordBytes,
    moffsOperandOffset, wordPrefix] at * <;> omega

theorem coordinate (mode : Mode) (base cell offset : Nat) (enough : moffsOperandOffset mode <= base) :
    Layout.templatePC mode base cell + offset - (base - moffsOperandOffset mode) = mode.stride * cell + offset := by
  cases mode <;> simp [Layout.templatePC, Layout.fieldAddress, Mode.stride, Mode.wordBytes,
    moffsOperandOffset, wordPrefix] at * <;> omega

theorem coordinate_div (mode : Mode) (cell offset : Nat) (bounded : offset < mode.stride) :
    (mode.stride * cell + offset) / mode.stride = cell := by
  cases mode <;> simp [Mode.stride, Mode.wordBytes] at * <;> omega

theorem coordinate_mod (mode : Mode) (cell offset : Nat) (bounded : offset < mode.stride) :
    (mode.stride * cell + offset) % mode.stride = offset := by
  cases mode <;> simp [Mode.stride, Mode.wordBytes] at * <;> omega

theorem prefix_bytes (mode : Mode) (base cell : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= base) :
    ByteMemory.bytesAt (image mode base values) (Layout.templatePC mode base cell) (moffsOperandOffset mode) =
      Protected.opcode mode := by
  apply List.ext_getElem
  case hl => simp [Protected.opcode, moffsOperandOffset]
  case h =>
    intro index left right
    have bounded : index < moffsOperandOffset mode := by simpa using left
    have strideBound : index < mode.stride := by
      cases mode <;> simp [moffsOperandOffset, wordPrefix, Mode.stride, Mode.wordBytes] at * <;> omega
    have before := start_before mode base cell index enough
    have coord := coordinate mode base cell index enough
    have remainder := coordinate_mod mode cell index strideBound
    simp [ByteMemory.bytesAt, image, Nat.not_lt.mpr before, coord, remainder, bounded]

theorem operand_bytes (mode : Mode) (base cell : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= base) :
    ByteMemory.bytesAt (image mode base values) (Layout.fieldAddress mode base cell) mode.wordBytes =
      wordEncode mode.wordBytes (values cell) := by
  apply List.ext_getElem
  case hl => simp
  case h =>
    intro index left right
    have bounded : index < mode.wordBytes := by simpa using left
    have strideBound : moffsOperandOffset mode + index < mode.stride := by
      cases mode <;> simp [moffsOperandOffset, wordPrefix, Mode.stride, Mode.wordBytes] at * <;> omega
    have before := start_before mode base cell (moffsOperandOffset mode + index) enough
    have coord := coordinate mode base cell (moffsOperandOffset mode + index) enough
    rw [<-Nat.add_assoc, Layout.owner_field_address mode base cell enough] at before coord
    have divided := coordinate_div mode cell (moffsOperandOffset mode + index) strideBound
    have remainder := coordinate_mod mode cell (moffsOperandOffset mode + index) strideBound
    have headerOutside : Not (moffsOperandOffset mode + index < moffsOperandOffset mode) := by omega
    have dataInside : moffsOperandOffset mode + index < moffsOperandOffset mode + mode.wordBytes := by omega
    simp [ByteMemory.bytesAt, image, Nat.not_lt.mpr before, coord, divided, remainder, headerOutside, dataInside]

/-- Protection is established by the concrete image definition, not supplied
as a code-owner or fetch oracle. -/
theorem initially_protected (mode : Mode) (base : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= base) : Protected.GridProtected mode base (image mode base values) :=
  fun cell => prefix_bytes mode base cell values enough

theorem initial_word (mode : Mode) (base cell : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= base) :
    Protected.wordAt mode (image mode base values) (Layout.fieldAddress mode base cell) = values cell := by
  have loaded : ByteMemory.readWord mode (image mode base values) (Layout.fieldAddress mode base cell) = some (values cell) := by
    unfold ByteMemory.readWord
    rw [operand_bytes mode base cell values enough, word_decode_encode]
  have total : ByteMemory.readWord mode (image mode base values) (Layout.fieldAddress mode base cell) =
      some (Protected.wordAt mode (image mode base values) (Layout.fieldAddress mode base cell)) := by
    simp [ByteMemory.readWord, wordDecode, Protected.wordAt]
  rw [total] at loaded
  exact Option.some.inj loaded

theorem initial_fetch (mode : Mode) (base cell : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= base) :
    Fetch.fetch mode (image mode base values) (Layout.templatePC mode base cell) = some (.moffs (values cell)) := by
  rw [Protected.grid_fetch_current mode base cell _ enough (initially_protected mode base values enough),
    initial_word mode base cell values enough]

end SmcTuring.Native.GridImage
