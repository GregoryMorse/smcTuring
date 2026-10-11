module
public import SmcTuring.Native.Fetch

public section

namespace SmcTuring.Native.Writes

open Execution

/-- Rewriting the bytes just read restores the entire byte-memory function. -/
theorem put_bytes_back (memory : ByteMemory.Memory) (address count : Nat) :
    ByteMemory.putBytes memory address (ByteMemory.bytesAt memory address count) = memory := by
  funext position
  by_cases inside : ByteMemory.Inside address count position
  · have below : address <= position := inside.1
    simp [ByteMemory.putBytes, ByteMemory.bytesAt, inside, Nat.add_sub_of_le below]
  · simp [ByteMemory.putBytes, inside]

/-- A same-width overwrite eliminates the earlier field store, also when the
field intersects other fields. No disjointness premise is needed here. -/
theorem put_bytes_overwrite (memory : ByteMemory.Memory) (address : Nat) (old fresh : List LittleEndian.Byte)
    (sameWidth : old.length = fresh.length) :
    ByteMemory.putBytes (ByteMemory.putBytes memory address old) address fresh =
      ByteMemory.putBytes memory address fresh := by
  funext position
  by_cases inside : ByteMemory.Inside address fresh.length position
  · simp [ByteMemory.putBytes, inside]
  · have oldOutside : Not (ByteMemory.Inside address old.length position) := by simpa [sameWidth] using inside
    simp [ByteMemory.putBytes, inside, oldOutside]

theorem put_word_overwrite (mode : Mode) (memory : ByteMemory.Memory) (address : Nat) (old fresh : Word mode) :
    ByteMemory.putWord mode (ByteMemory.putWord mode memory address old) address fresh =
      ByteMemory.putWord mode memory address fresh := by
  exact put_bytes_overwrite memory address _ _ (by simp)

/-- Two stores with disjoint byte footprints commute. -/
theorem put_bytes_commute (memory : ByteMemory.Memory) (first second : Nat)
    (firstValue secondValue : List LittleEndian.Byte)
    (separate : forall position, ByteMemory.Inside first firstValue.length position ->
      Not (ByteMemory.Inside second secondValue.length position)) :
    ByteMemory.putBytes (ByteMemory.putBytes memory first firstValue) second secondValue =
      ByteMemory.putBytes (ByteMemory.putBytes memory second secondValue) first firstValue := by
  funext position
  by_cases firstInside : ByteMemory.Inside first firstValue.length position
  · have secondOutside := separate position firstInside
    simp [ByteMemory.putBytes, firstInside, secondOutside]
  · by_cases secondInside : ByteMemory.Inside second secondValue.length position <;>
      simp [ByteMemory.putBytes, firstInside, secondInside]

theorem put_words_commute (mode : Mode) (memory : ByteMemory.Memory) (first second : Nat)
    (firstValue secondValue : Word mode)
    (separate : forall index : Fin mode.wordBytes,
      Not (ByteMemory.Inside second mode.wordBytes (first + index.val))) :
    ByteMemory.putWord mode (ByteMemory.putWord mode memory first firstValue) second secondValue =
      ByteMemory.putWord mode (ByteMemory.putWord mode memory second secondValue) first firstValue := by
  apply put_bytes_commute
  intro position inside
  have within : ByteMemory.Inside first mode.wordBytes position := by simpa using inside
  have bound : position - first < mode.wordBytes := by rcases within with ⟨_, _⟩; omega
  have framed := separate ⟨position - first, bound⟩
  simpa [Nat.add_sub_of_le within.1] using framed

/-- Full little-endian load/store restoration, rather than a word-level oracle. -/
theorem put_word_back (mode : Mode) (memory : ByteMemory.Memory) (address : Word mode) :
    ByteMemory.putWord mode memory address.toNat (load mode memory address) = memory := by
  have encoded : LittleEndian.wordEncode mode.wordBytes (load mode memory address) =
      ByteMemory.bytesAt memory address.toNat mode.wordBytes :=
    LittleEndian.word_encode_decode mode.wordBytes _ _ (read_word_total mode memory address)
  unfold ByteMemory.putWord
  rw [encoded]
  exact put_bytes_back memory address.toNat mode.wordBytes

/-- A complete load from a separate field is unchanged by the byte store. -/
theorem load_frame (mode : Mode) (memory : ByteMemory.Memory) (written observed value : Word mode)
    (separate : forall index : Fin mode.wordBytes,
      Not (ByteMemory.Inside written.toNat mode.wordBytes (observed.toNat + index.val))) :
    load mode (ByteMemory.putWord mode memory written.toNat value) observed = load mode memory observed := by
  have framed := ByteMemory.bytes_at_frame memory written.toNat (LittleEndian.wordEncode mode.wordBytes value)
    observed.toNat mode.wordBytes (by simpa using separate)
  simpa only [load, ByteMemory.putWord] using
    congrArg (fun bytes => BitVec.ofNat (8 * mode.wordBytes) (LittleEndian.pack bytes)) framed

/-- The memory destination of each selected sequential instruction.
CALL's write is the decremented stack slot, not its transfer target. -/
@[expose] def address (mode : Mode) (form : Form mode) (state : State mode) : Word mode :=
  match form with
  | .moffs target => target
  | .memory .callIndirect _ => state.stack - Arithmetic.encodeNat mode mode.wordBytes
  | .memory _ displacement => memoryAddress mode (nextPC mode form state) displacement
  | .exchangeIndirect => state.accumulator
  | .callRelative _ => state.stack - Arithmetic.encodeNat mode mode.wordBytes

@[expose] def value (mode : Mode) (form : Form mode) (state : State mode) : Word mode :=
  match form with
  | .moffs _ => state.accumulator
  | .exchangeIndirect => state.accumulator
  | .callRelative _ => nextPC mode form state
  | .memory operation displacement =>
    let prior := load mode state.memory (memoryAddress mode (nextPC mode form state) displacement)
    match operation with
    | .exchangeAcc | .storeAcc => state.accumulator
    | .add => prior + state.accumulator
    | .subtract => prior - state.accumulator
    | .bitXor => prior ^^^ state.accumulator
    | .bitAnd => prior &&& state.accumulator
    | .exchangeStack | .storeStack => state.stack
    | .subtractBorrowZero => prior - (if state.carry then 1 else 0)
    | .callIndirect => nextPC mode form state

/-- Every selected instruction really performs one complete memory-word store.
An unchanged resulting memory still has that nonempty write footprint. -/
theorem execute_memory (mode : Mode) (form : Form mode) (state : State mode) :
    (execute mode form state).memory =
      ByteMemory.putWord mode state.memory (address mode form state).toNat (value mode form state) := by
  cases form with
  | moffs target => rfl
  | exchangeIndirect => rfl
  | callRelative displacement => rfl
  | memory operation displacement => cases operation <;> rfl

theorem execute_frame (mode : Mode) (form : Form mode) (state : State mode) (position : Nat)
    (outside : Not (ByteMemory.Inside (address mode form state).toNat mode.wordBytes position)) :
    (execute mode form state).memory position = state.memory position := by
  rw [execute_memory]
  exact ByteMemory.put_frame _ _ _ position (by simpa using outside)

theorem write_nonempty (mode : Mode) (form : Form mode) (state : State mode) :
    Not (LittleEndian.wordEncode mode.wordBytes (value mode form state) = []) :=
  ByteMemory.word_write_nonempty mode _

/-- An automatically fetched packet has the same complete word-store effect. -/
theorem fetched_write (mode : Mode) (form : Form mode) (state : State mode)
    (current : Fetch.fetch mode state.memory state.pc.toNat = some form) :
    (Fetch.step mode state).map State.memory =
      some (ByteMemory.putWord mode state.memory (address mode form state).toNat (value mode form state)) := by
  simp only [Fetch.step, current, Option.map_some, execute_memory]

/-- Every reached write destination is owned, following the actual effects.
Every selected form already has the nonempty word-write theorem above. -/
@[expose] def OwnedRun (mode : Mode) (owned : Word mode -> Prop) : List (Form mode) -> State mode -> Prop
  | [], _ => True
  | form :: rest, state => And (owned (address mode form state)) (OwnedRun mode owned rest (execute mode form state))

theorem owned_run_append (mode : Mode) (owned : Word mode -> Prop) (first second : List (Form mode)) (state : State mode) :
    OwnedRun mode owned (first ++ second) state =
      And (OwnedRun mode owned first state) (OwnedRun mode owned second (runForms mode first state)) := by
  induction first generalizing state with
  | nil => simp [OwnedRun, runForms]
  | cons form rest ih => simp [OwnedRun, runForms, ih, and_assoc]

end SmcTuring.Native.Writes
