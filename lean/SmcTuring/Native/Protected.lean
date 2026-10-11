module
public import SmcTuring.Native.ReadCallee

public section

namespace SmcTuring.Native.Protected

open LittleEndian

@[expose] def opcode (mode : Mode) : List Byte := wordPrefix mode ++ [0xA3]

@[expose] def PrefixAt (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Prop :=
  ByteMemory.bytesAt memory pc (moffsOperandOffset mode) = opcode mode

@[expose] def wordAt (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) : Word mode :=
  BitVec.ofNat (8 * mode.wordBytes) (pack (ByteMemory.bytesAt memory address mode.wordBytes))

theorem bytes_at_append (memory : ByteMemory.Memory) (pc first second : Nat) :
    ByteMemory.bytesAt memory pc (first + second) =
      ByteMemory.bytesAt memory pc first ++ ByteMemory.bytesAt memory (pc + first) second := by
  simp [ByteMemory.bytesAt, List.ofFn_add, Nat.add_assoc]

theorem word_at_encoded (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) :
    wordEncode mode.wordBytes (wordAt mode memory address) = ByteMemory.bytesAt memory address mode.wordBytes := by
  apply word_encode_decode
  simp [wordDecode, wordAt]

theorem word_at_put (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) (value : Word mode) :
    wordAt mode (ByteMemory.putWord mode memory address value) address = value := by
  have loaded := ByteMemory.read_put_word mode memory address value
  have total : ByteMemory.readWord mode (ByteMemory.putWord mode memory address value) address =
      some (wordAt mode (ByteMemory.putWord mode memory address value) address) := by
    simp [ByteMemory.readWord, wordDecode, wordAt]
  rw [total] at loaded
  exact Option.some.inj loaded

/-- An intact MOFFS prefix and arbitrary current operand bytes determine a
complete encoding. No initial or cached operand value is used here. -/
theorem current_moffs (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat)
    (intact : PrefixAt mode memory pc) :
    ByteMemory.bytesAt memory pc (encode mode (.moffs (wordAt mode memory (pc + moffsOperandOffset mode)))).length =
      encode mode (.moffs (wordAt mode memory (pc + moffsOperandOffset mode))) := by
  have length : (encode mode (.moffs (wordAt mode memory (pc + moffsOperandOffset mode)))).length =
      moffsOperandOffset mode + mode.wordBytes := by simp [instructionLength, moffsOperandOffset]
  rw [length, bytes_at_append, intact]
  rw [<-word_at_encoded mode memory (pc + moffsOperandOffset mode)]
  rfl

theorem fetch_moffs (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat)
    (intact : PrefixAt mode memory pc) :
    Fetch.fetch mode memory pc = some (.moffs (wordAt mode memory (pc + moffsOperandOffset mode))) :=
  Fetch.fetch_current_encoding mode memory pc _ (current_moffs mode memory pc intact)

theorem prefix_frame (mode : Mode) (memory : ByteMemory.Memory) (pc address : Nat) (value : Word mode)
    (separate : forall index : Fin (moffsOperandOffset mode),
      Not (ByteMemory.Inside address mode.wordBytes (pc + index.val))) :
    PrefixAt mode (ByteMemory.putWord mode memory address value) pc = PrefixAt mode memory pc := by
  unfold PrefixAt
  have frame := ByteMemory.bytes_at_frame memory address (wordEncode mode.wordBytes value) pc
    (moffsOperandOffset mode) (by simpa using separate)
  simp only [ByteMemory.putWord, frame]

/-- A grid operand write cannot reach any owner's prefix, including its own. -/
theorem grid_prefix_separate (mode : Mode) (base written observed : Nat)
    (enough : moffsOperandOffset mode <= base) (index : Fin (moffsOperandOffset mode)) :
    Not (ByteMemory.Inside (Layout.fieldAddress mode base written) mode.wordBytes
      (Layout.templatePC mode base observed + index.val)) := by
  have small := index.isLt
  unfold ByteMemory.Inside
  cases mode <;> simp [Layout.fieldAddress, Layout.templatePC, Mode.stride, Mode.wordBytes,
    moffsOperandOffset, wordPrefix] at * <;> omega

@[expose] def GridProtected (mode : Mode) (base : Nat) (memory : ByteMemory.Memory) : Prop :=
  forall index, PrefixAt mode memory (Layout.templatePC mode base index)

theorem grid_store_protected (mode : Mode) (base written : Nat) (memory : ByteMemory.Memory) (value : Word mode)
    (enough : moffsOperandOffset mode <= base) (intact : GridProtected mode base memory) :
    GridProtected mode base (ByteMemory.putWord mode memory (Layout.fieldAddress mode base written) value) := by
  intro observed
  rw [prefix_frame mode memory (Layout.templatePC mode base observed) (Layout.fieldAddress mode base written)
    value (grid_prefix_separate mode base written observed enough)]
  exact intact observed

/-- Every grid word remains a currently decodable instruction operand after
any field store, with the just-written value at the selected owner. -/
theorem grid_fetch_written (mode : Mode) (base written : Nat) (memory : ByteMemory.Memory) (value : Word mode)
    (enough : moffsOperandOffset mode <= base) (intact : GridProtected mode base memory) :
    Fetch.fetch mode (ByteMemory.putWord mode memory (Layout.fieldAddress mode base written) value)
      (Layout.templatePC mode base written) = some (.moffs value) := by
  have after := grid_store_protected mode base written memory value enough intact
  rw [fetch_moffs mode _ _ (after written), Layout.owner_field_address mode base written enough,
    word_at_put]

theorem grid_fetch_current (mode : Mode) (base observed : Nat) (memory : ByteMemory.Memory)
    (enough : moffsOperandOffset mode <= base) (intact : GridProtected mode base memory) :
    Fetch.fetch mode memory (Layout.templatePC mode base observed) =
      some (.moffs (wordAt mode memory (Layout.fieldAddress mode base observed))) := by
  rw [fetch_moffs mode memory _ (intact observed), Layout.owner_field_address mode base observed enough]

/-- The native register load agrees with the natural-address operand load
only when the physical address is representable without wrapping. -/
theorem encoded_address_load (mode : Mode) (memory : ByteMemory.Memory) (address : Nat)
    (fits : address < 2 ^ (8 * mode.wordBytes)) :
    Execution.load mode memory (Arithmetic.encodeNat mode address) = wordAt mode memory address := by
  unfold Execution.load wordAt
  rw [Arithmetic.encode_nat_toNat mode address fits]


@[expose] def GridOwned (mode : Mode) (base : Nat) (address : Word mode) : Prop :=
  exists index, address.toNat = Layout.fieldAddress mode base index

/-- The selected instruction's actual word store preserves all grid opcodes. -/
theorem execute_grid_protected (mode : Mode) (base : Nat) (state : Execution.State mode) (form : Form mode)
    (enough : moffsOperandOffset mode <= base) (intact : GridProtected mode base state.memory)
    (owned : GridOwned mode base (Writes.address mode form state)) :
    GridProtected mode base (Execution.execute mode form state).memory := by
  cases owned with
  | intro index location =>
    rw [Writes.execute_memory, location]
    exact grid_store_protected mode base index state.memory _ enough intact

theorem run_grid_protected (mode : Mode) (base : Nat) (state : Execution.State mode) (forms : List (Form mode))
    (enough : moffsOperandOffset mode <= base) (intact : GridProtected mode base state.memory)
    (owned : Writes.OwnedRun mode (GridOwned mode base) forms state) :
    GridProtected mode base (Execution.runForms mode forms state).memory := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    change And (GridOwned mode base (Writes.address mode form state))
      (Writes.OwnedRun mode (GridOwned mode base) rest (Execution.execute mode form state)) at owned
    exact ih (Execution.execute mode form state)
      (execute_grid_protected mode base state form enough intact owned.1) owned.2

/-- Opcode protection persists along an actual automatically fetched trace. -/
theorem trace_grid_protected (mode : Mode) (base : Nat) (state result : Execution.State mode)
    (forms : List (Form mode)) (enough : moffsOperandOffset mode <= base)
    (intact : GridProtected mode base state.memory)
    (owned : Writes.OwnedRun mode (GridOwned mode base) forms state)
    (trace : Fetch.Trace mode state forms result) : GridProtected mode base result.memory := by
  rw [Fetch.trace_run_eq mode trace]
  exact run_grid_protected mode base state forms enough intact owned

end SmcTuring.Native.Protected
