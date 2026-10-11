module
public import SmcTuring.Native.Encoding
public import Init.Data.List.OfFn

public section

namespace SmcTuring.Native.ByteMemory

open LittleEndian

abbrev Memory := Nat -> Byte

/-- Byte addresses of an operand field, before applying the CPU capacity bound. -/
@[expose] def Inside (address size position : Nat) : Prop := address ≤ position ∧ position < address + size

instance insideDecidable (address size position : Nat) : Decidable (Inside address size position) :=
  inferInstanceAs (Decidable (address ≤ position ∧ position < address + size))

/-- Store the whole encoded word, preserving every byte outside its field. -/
@[expose] def putBytes (memory : Memory) (address : Nat) (bytes : List Byte) : Memory :=
  fun position => if inside : Inside address bytes.length position then
    bytes[position - address]'(by unfold Inside at inside; omega) else memory position

/-- A finite instruction/operand window from the current unified byte memory. -/
@[expose] def bytesAt (memory : Memory) (address count : Nat) : List Byte :=
  List.ofFn (fun index : Fin count => memory (address + index.val))

@[simp] theorem bytes_at_length (memory : Memory) (address count : Nat) :
    (bytesAt memory address count).length = count := by simp [bytesAt]

/-- Every byte of the stored field is updated, including an unchanged-value store. -/
theorem put_at_index (memory : Memory) (address : Nat) (bytes : List Byte) (index : Fin bytes.length) :
    putBytes memory address bytes (address + index.val) = bytes[index.val] := by
  have inside : Inside address bytes.length (address + index.val) := by unfold Inside; omega
  simp [putBytes, inside]

/-- No other byte changes; in particular, adjacent opcode bytes are preserved. -/
theorem put_frame (memory : Memory) (address : Nat) (bytes : List Byte) (position : Nat)
    (outside : ¬Inside address bytes.length position) :
    putBytes memory address bytes position = memory position := by simp [putBytes, outside]

/-- Load/store correspondence is proved for the entire byte sequence. -/
@[simp] theorem bytes_at_put (memory : Memory) (address : Nat) (bytes : List Byte) :
    bytesAt (putBytes memory address bytes) address bytes.length = bytes := by
  change List.ofFn (fun index : Fin bytes.length => putBytes memory address bytes (address + index.val)) = bytes
  simpa only [put_at_index] using (List.ofFn_getElem (xs := bytes))

theorem bytes_at_frame (memory : Memory) (address : Nat) (bytes : List Byte) (observed count : Nat)
    (separate : ∀ index : Fin count, ¬Inside address bytes.length (observed + index.val)) :
    bytesAt (putBytes memory address bytes) observed count = bytesAt memory observed count := by
  apply congrArg List.ofFn
  funext index
  exact put_frame memory address bytes (observed + index.val) (separate index)

/-- Storing the bytes already present still issues a store, but leaves the
entire memory function unchanged. -/
theorem put_current (memory : Memory) (address : Nat) (bytes : List Byte)
    (current : bytesAt memory address bytes.length = bytes) :
    putBytes memory address bytes = memory := by
  funext position
  by_cases inside : Inside address bytes.length position
  · have bound : position - address < bytes.length := by unfold Inside at inside; omega
    have fetched := congrArg (fun values : List Byte => values[position - address]?) current
    have index : position - address < bytes.length := bound
    simp only [bytesAt, List.getElem?_ofFn, index, dite_true,
      List.getElem?_eq_getElem index, Option.some.injEq] at fetched
    have sum : address + (position - address) = position := by unfold Inside at inside; omega
    simpa only [putBytes, dite_eq_left inside, sum] using fetched.symm
  · exact put_frame memory address bytes position inside

/-- General operand patching: a same-width payload replacement retains the
leading and all outside bytes exactly. No disjoint-address oracle is used. -/
theorem patch_payload (memory : Memory) (address : Nat) (leading old fresh : List Byte)
    (sameWidth : old.length = fresh.length) :
    putBytes (putBytes memory address (leading ++ old)) (address + leading.length) fresh =
      putBytes memory address (leading ++ fresh) := by
  funext position
  by_cases before : position < address
  · have blockOutside : ¬Inside address (leading ++ old).length position := by unfold Inside; omega
    have freshOutside : ¬Inside address (leading ++ fresh).length position := by unfold Inside; omega
    have patchOutside : ¬Inside (address + leading.length) fresh.length position := by unfold Inside; omega
    rw [put_frame _ _ _ _ patchOutside, put_frame _ _ _ _ blockOutside, put_frame _ _ _ _ freshOutside]
  · have after : address ≤ position := by omega
    by_cases inPrefix : position < address + leading.length
    · have oldInside : Inside address (leading.length + old.length) position := by unfold Inside; omega
      have freshInside : Inside address (leading.length + fresh.length) position := by unfold Inside; omega
      have patchOutside : ¬Inside (address + leading.length) fresh.length position := by unfold Inside; omega
      have index : position - address < leading.length := by omega
      rw [put_frame _ _ _ _ patchOutside]
      simp [putBytes, oldInside, freshInside, List.getElem_append_left index]
    · by_cases inPayload : position < address + leading.length + fresh.length
      · have freshInside : Inside address (leading.length + fresh.length) position := by unfold Inside; omega
        have patchInside : Inside (address + leading.length) fresh.length position := by unfold Inside; omega
        have index : leading.length ≤ position - address := by omega
        simp [putBytes, freshInside, patchInside, List.getElem_append_right index, Nat.sub_sub]
      · have blockOutside : ¬Inside address (leading ++ old).length position := by simp only [Inside, List.length_append]; omega
        have freshOutside : ¬Inside address (leading ++ fresh).length position := by simp only [Inside, List.length_append]; omega
        have patchOutside : ¬Inside (address + leading.length) fresh.length position := by unfold Inside; omega
        rw [put_frame _ _ _ _ patchOutside, put_frame _ _ _ _ blockOutside, put_frame _ _ _ _ freshOutside]

/-- The abstract word store is realized by precisely mode.wordBytes byte stores. -/
@[expose] def putWord (mode : Mode) (memory : Memory) (address : Nat) (value : Word mode) : Memory :=
  putBytes memory address (wordEncode mode.wordBytes value)

@[expose] def readWord (mode : Mode) (memory : Memory) (address : Nat) : Option (Word mode) :=
  wordDecode mode.wordBytes (bytesAt memory address mode.wordBytes)

/-- Whole-word load/store round trip in unified byte memory. -/
theorem read_put_word (mode : Mode) (memory : Memory) (address : Nat) (value : Word mode) :
    readWord mode (putWord mode memory address value) address = some value := by
  unfold readWord putWord
  have loaded : bytesAt (putBytes memory address (wordEncode mode.wordBytes value)) address mode.wordBytes =
      wordEncode mode.wordBytes value := by
    simpa only [word_encode_length] using bytes_at_put memory address (wordEncode mode.wordBytes value)
  rw [loaded, word_decode_encode]

/-- Every native computational word write has a nonempty byte footprint. -/
theorem word_write_nonempty (mode : Mode) (value : Word mode) : wordEncode mode.wordBytes value ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  simp only [word_encode_length, List.length_nil] at length
  cases mode <;> cases length

/-- Updating the MOFFS address changes only its owned operand bytes. -/
theorem moffs_patch (mode : Mode) (memory : Memory) (pc : Nat) (old fresh : Word mode) :
    putWord mode (putBytes memory pc (encode mode (.moffs old))) (pc + moffsOperandOffset mode) fresh =
      putBytes memory pc (encode mode (.moffs fresh)) := by
  have sameWidth : (wordEncode mode.wordBytes old).length = (wordEncode mode.wordBytes fresh).length := by simp
  have location : pc + moffsOperandOffset mode = pc + (wordPrefix mode ++ [0xA3]).length := by
    simp [moffsOperandOffset]
  unfold putWord encode
  rw [location]
  exact patch_payload memory pc (wordPrefix mode ++ [0xA3]) (wordEncode mode.wordBytes old)
    (wordEncode mode.wordBytes fresh) sameWidth

/-- Current-byte fetch of an owned MOFFS instruction; fetch discipline is a
separate architectural premise when realizing this sequential memory model. -/
@[expose] def fetchMoffs (mode : Mode) (memory : Memory) (pc : Nat) : Option (Form mode) :=
  decode mode (bytesAt memory pc (moffsOperandOffset mode + mode.wordBytes))

theorem fetch_written_moffs (mode : Mode) (memory : Memory) (pc : Nat) (address : Word mode) :
    fetchMoffs mode (putBytes memory pc (encode mode (.moffs address))) pc = some (.moffs address) := by
  have length : (encode mode (.moffs address)).length = moffsOperandOffset mode + mode.wordBytes := by
    simp [instructionLength, moffsOperandOffset]
  unfold fetchMoffs
  rw [←length, bytes_at_put, form_roundtrip]

/-- The live byte operand is fetched after a patch, with the original opcode
and all outside memory preserved; the old payload cannot be silently reused. -/
theorem fetch_patched_moffs (mode : Mode) (memory : Memory) (pc : Nat) (old fresh : Word mode) :
    fetchMoffs mode
      (putWord mode (putBytes memory pc (encode mode (.moffs old))) (pc + moffsOperandOffset mode) fresh) pc =
      some (.moffs fresh) := by
  rw [moffs_patch, fetch_written_moffs]

end SmcTuring.Native.ByteMemory
