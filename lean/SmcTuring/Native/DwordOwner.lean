module
public import SmcTuring.Native.TerminalMarker

public section
namespace SmcTuring.Native.DwordOwner
open LittleEndian

/-- Printed DEFDATA32: the current DWORD operand stores itself at offset six.
Its live value, rather than a cached zero initializer, is preserved. -/
@[expose] def form (mode : Mode) (pc : Nat) (value : DwordStore.Dword) : DwordStore.Form :=
  DwordStore.emit mode pc (pc + 6) value
@[expose] def bytes (mode : Mode) (pc : Nat) (value : DwordStore.Dword) : List Byte := DwordStore.encode (form mode pc value)
@[expose] def image (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (backing : ByteMemory.Memory) : ByteMemory.Memory :=
  ByteMemory.putBytes backing pc (bytes mode pc value)
@[expose] def finish (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode) : Execution.State mode :=
  DwordStore.execute mode (form mode pc value) state

theorem length (mode : Mode) (pc : Nat) (value : DwordStore.Dword) : (bytes mode pc value).length = 10 :=
  DwordStore.length _

theorem reach (pc : Nat) : Relocation.SignedDelta (pc + 10) (pc + 6) := by
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem displacement_x64 (pc : Nat) (value : DwordStore.Dword) : (form .x64 pc value).displacement = BitVec.ofInt 32 (-4) := by
  have delta : Relocation.delta (pc + 10) (pc + 6) = -4 := by unfold Relocation.delta; omega
  simp only [form, DwordStore.emit, Relocation.memoryDisp, Relocation.relative32, delta]

theorem target (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc) :
    DwordStore.address mode (form mode pc value) state = Arithmetic.encodeNat mode (pc + 6) :=
  DwordStore.emit_address mode pc (pc + 6) value state location (fun _ => reach pc)

theorem target_toNat (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (DwordStore.address mode (form mode pc value) state).toNat = pc + 6 := by
  rw [target mode pc value state location]
  exact Arithmetic.encode_nat_toNat mode _ (by omega)

theorem current_image (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode pc value backing) pc 10 = bytes mode pc value := by
  simpa only [image, length] using ByteMemory.bytes_at_put backing pc (bytes mode pc value)

/-- The current packet supplies the four live operand bytes written back;
initialization does not force later executions to reset the symbol to zero. -/
theorem current_immediate (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc 10 = bytes mode pc value) :
    ByteMemory.bytesAt memory (pc + 6) 4 = wordEncode 4 value := by
  apply List.ext_getElem
  · simp only [ByteMemory.bytes_at_length, word_encode_length]
  · intro index leftBound rightBound
    have below : index < 4 := by simpa only [ByteMemory.bytes_at_length] using leftBound
    have fetched := congrArg (fun values : List Byte => values[6 + index]?) current
    have packetBound : 6 + index < 10 := by omega
    have leading : ([0xc7, 0x05] ++ wordEncode 4 (form mode pc value).displacement).length = 6 := by
      simp only [List.length_append, List.length_cons, List.length_nil, word_encode_length]
    change (ByteMemory.bytesAt memory pc 10)[6 + index]? =
      (([0xc7, 0x05] ++ wordEncode 4 (form mode pc value).displacement) ++
        wordEncode 4 value)[6 + index]? at fetched
    rw [List.getElem?_append_right (by omega), leading] at fetched
    have valueBound : index < (wordEncode 4 value).length := by
      simpa only [word_encode_length] using below
    simp only [ByteMemory.bytesAt, List.getElem?_ofFn, packetBound, dite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem valueBound,
      Option.some.injEq] at fetched
    simpa only [ByteMemory.bytesAt, List.getElem_ofFn, Nat.add_assoc] using fetched

theorem memory_unchanged (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc value) :
    (finish mode pc value state).memory = state.memory := by
  change ByteMemory.putBytes state.memory
    (DwordStore.address mode (form mode pc value) state).toNat (wordEncode 4 value) = state.memory
  rw [target_toNat mode pc value state location capacity]
  apply ByteMemory.put_current
  simpa only [word_encode_length] using current_immediate mode pc value state.memory current

theorem next_position (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (finish mode pc value state).pc.toNat = pc + 10 := by
  have next : DwordStore.next mode state = Arithmetic.encodeNat mode (pc + 10) := by
    rw [DwordStore.next, location]; exact BitVec.ofNat_add_ofNat pc 10
  change (DwordStore.next mode state).toNat = _
  rw [next]
  exact Arithmetic.encode_nat_toNat mode _ capacity

theorem owned_write (pc position : Nat) (written : ByteMemory.Inside (pc + 6) 4 position) :
    ByteMemory.Inside pc 10 position := by unfold ByteMemory.Inside at *; omega

theorem pure (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (∀ position, ByteMemory.Inside (DwordStore.address mode (form mode pc value) state).toNat 4 position →
      ByteMemory.Inside pc 10 position) ∧
    ByteMemory.Inside (DwordStore.address mode (form mode pc value) state).toNat 4 (pc + 6) := by
  rw [target_toNat mode pc value state location capacity]
  exact ⟨owned_write pc, by unfold ByteMemory.Inside; omega⟩

/-- Positive live scalar owner: actual current-byte fetch/store, next PC,
full AX/SP/CF preservation, unchanged memory and a nonempty code-owned write. -/
theorem correct (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc value) :
    DwordStore.step mode state = some (finish mode pc value state) ∧
    (finish mode pc value state).pc.toNat = pc + 10 ∧
    (finish mode pc value state).accumulator = state.accumulator ∧
    (finish mode pc value state).stack = state.stack ∧
    (finish mode pc value state).carry = state.carry ∧
    (finish mode pc value state).memory = state.memory := by
  have position : state.pc.toNat = pc := by
    rw [location]; exact Arithmetic.encode_nat_toNat mode _ (by omega)
  exact ⟨DwordStore.step_encoding mode state (form mode pc value) (by simpa only [position, bytes] using current),
    next_position mode pc value state location capacity,
    (DwordStore.registers mode (form mode pc value) state).1,
    (DwordStore.registers mode (form mode pc value) state).2.1,
    (DwordStore.registers mode (form mode pc value) state).2.2,
    memory_unchanged mode pc value state location capacity current⟩

theorem reusable (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc value) :
    ByteMemory.bytesAt (finish mode pc value state).memory pc 10 = bytes mode pc value := by
  rw [memory_unchanged mode pc value state location capacity current]; exact current

theorem output_preserved (mode : Mode) (pc : Nat) (value : DwordStore.Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc value) (output count : Nat) :
    ByteMemory.bytesAt (finish mode pc value state).memory output count =
      ByteMemory.bytesAt state.memory output count := by
  rw [memory_unchanged mode pc value state location capacity current]

/-- Patching only the declared immediate produces the complete owner packet
with the new live symbol and the identical address/header. -/
theorem patch_value (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory)
    (old fresh : DwordStore.Dword)
    (current : ByteMemory.bytesAt memory pc 10 = bytes mode pc old) :
    ByteMemory.putWord .x86 memory (pc+6) fresh =
      ByteMemory.putBytes memory pc (bytes mode pc fresh) := by
  have kept := ByteMemory.put_current memory pc (bytes mode pc old)
    (by simpa only [length] using current)
  have patch := ByteMemory.patch_payload memory pc
    ([0xc7,0x05] ++ wordEncode 4 (form mode pc old).displacement)
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp only [word_encode_length])
  have leading : ([0xc7,0x05] ++ wordEncode 4 (form mode pc old).displacement).length = 6 := by simp
  change ByteMemory.putWord .x86 (ByteMemory.putBytes memory pc (bytes mode pc old)) _ fresh =
    ByteMemory.putBytes memory pc (bytes mode pc fresh) at patch
  rwa [leading,kept] at patch

theorem patched_current (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory)
    (old fresh : DwordStore.Dword)
    (current : ByteMemory.bytesAt memory pc 10 = bytes mode pc old) :
    ByteMemory.bytesAt (ByteMemory.putWord .x86 memory (pc+6) fresh) pc 10 = bytes mode pc fresh := by
  rw [patch_value mode pc memory old fresh current]
  simpa only [length] using ByteMemory.bytes_at_put memory pc (bytes mode pc fresh)

/-- The exact published scalar declaration correction emits zero initially;
the two Listing 8 consumers both name its complete DWORD field at +IMMOFFS. -/
theorem initial_zero (mode : Mode) (pc : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.readWord .x86 (image mode pc 0 backing) (pc+6) = some 0 := by
  have field := current_immediate mode pc 0 (image mode pc 0 backing) (current_image mode pc 0 backing)
  change wordDecode 4 (ByteMemory.bytesAt (image mode pc 0 backing) (pc+6) 4) = some 0
  rw [field,word_decode_encode]

end SmcTuring.Native.DwordOwner
