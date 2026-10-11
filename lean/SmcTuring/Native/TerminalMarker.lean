module
public import SmcTuring.Native.DwordStore

public section
namespace SmcTuring.Native.TerminalMarker
open LittleEndian

/-- Listing 2's corrected DWORD MOV writes its own immediate at offset six.
The pure computation ends at the following PC; the host observes this boundary. -/
@[expose] def form (mode : Mode) (pc : Nat) : DwordStore.Form :=
  DwordStore.emit mode pc (pc + 6) 0
@[expose] def bytes (mode : Mode) (pc : Nat) : List Byte := DwordStore.encode (form mode pc)
@[expose] def image (mode : Mode) (pc : Nat) (backing : ByteMemory.Memory) : ByteMemory.Memory :=
  ByteMemory.putBytes backing pc (bytes mode pc)
@[expose] def finish (mode : Mode) (pc : Nat) (state : Execution.State mode) : Execution.State mode :=
  DwordStore.execute mode (form mode pc) state

theorem length (mode : Mode) (pc : Nat) : (bytes mode pc).length = 10 :=
  DwordStore.length _

theorem reach (pc : Nat) : Relocation.SignedDelta (pc + 10) (pc + 6) := by
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem displacement_x64 (pc : Nat) : (form .x64 pc).displacement = BitVec.ofInt 32 (-4) := by
  have delta : Relocation.delta (pc + 10) (pc + 6) = -4 := by unfold Relocation.delta; omega
  simp only [form, DwordStore.emit, Relocation.memoryDisp, Relocation.relative32, delta]

theorem target (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc) :
    DwordStore.address mode (form mode pc) state = Arithmetic.encodeNat mode (pc + 6) :=
  DwordStore.emit_address mode pc (pc + 6) 0 state location (fun _ => reach pc)

theorem target_toNat (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (DwordStore.address mode (form mode pc) state).toNat = pc + 6 := by
  rw [target mode pc state location]
  exact Arithmetic.encode_nat_toNat mode _ (by omega)

theorem current_image (mode : Mode) (pc : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode pc backing) pc 10 = bytes mode pc := by
  simpa only [image, length] using ByteMemory.bytes_at_put backing pc (bytes mode pc)

/-- The current packet, rather than a remembered initializer, supplies the
four zero bytes which the terminal store writes back. -/
theorem current_immediate (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc 10 = bytes mode pc) :
    ByteMemory.bytesAt memory (pc + 6) 4 = wordEncode 4 (0 : BitVec 32) := by
  apply List.ext_getElem
  · simp only [ByteMemory.bytes_at_length, word_encode_length]
  · intro index leftBound rightBound
    have below : index < 4 := by simpa only [ByteMemory.bytes_at_length] using leftBound
    have fetched := congrArg (fun values : List Byte => values[6 + index]?) current
    have packetBound : 6 + index < 10 := by omega
    have leading : ([0xc7, 0x05] ++ wordEncode 4 (form mode pc).displacement).length = 6 := by
      simp only [List.length_append, List.length_cons, List.length_nil, word_encode_length]
    change (ByteMemory.bytesAt memory pc 10)[6 + index]? =
      (([0xc7, 0x05] ++ wordEncode 4 (form mode pc).displacement) ++
        wordEncode 4 (0 : BitVec 32))[6 + index]? at fetched
    rw [List.getElem?_append_right (by omega), leading] at fetched
    have valueBound : index < (wordEncode 4 (0 : BitVec 32)).length := by
      simpa only [word_encode_length] using below
    simp only [ByteMemory.bytesAt, List.getElem?_ofFn, packetBound, dite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem valueBound,
      Option.some.injEq] at fetched
    simpa only [ByteMemory.bytesAt, List.getElem_ofFn, Nat.add_assoc] using fetched

theorem memory_unchanged (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc) :
    (finish mode pc state).memory = state.memory := by
  change ByteMemory.putBytes state.memory
    (DwordStore.address mode (form mode pc) state).toNat (wordEncode 4 (0 : BitVec 32)) = state.memory
  rw [target_toNat mode pc state location capacity]
  apply ByteMemory.put_current
  simpa only [word_encode_length] using current_immediate mode pc state.memory current

theorem next_position (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (finish mode pc state).pc.toNat = pc + 10 := by
  have next : DwordStore.next mode state = Arithmetic.encodeNat mode (pc + 10) := by
    rw [DwordStore.next, location]; exact BitVec.ofNat_add_ofNat pc 10
  change (DwordStore.next mode state).toNat = _
  rw [next]
  exact Arithmetic.encode_nat_toNat mode _ capacity

theorem owned_write (pc position : Nat) (written : ByteMemory.Inside (pc + 6) 4 position) :
    ByteMemory.Inside pc 10 position := by unfold ByteMemory.Inside at *; omega

theorem pure (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes)) :
    (∀ position, ByteMemory.Inside (DwordStore.address mode (form mode pc) state).toNat 4 position →
      ByteMemory.Inside pc 10 position) ∧
    ByteMemory.Inside (DwordStore.address mode (form mode pc) state).toNat 4 (pc + 6) := by
  rw [target_toNat mode pc state location capacity]
  exact ⟨owned_write pc, by unfold ByteMemory.Inside; omega⟩

/-- Positive terminal observation: actual current-byte fetch/store, next PC,
AX/SP/CF preservation, unchanged whole memory and a nonempty code-owned write.
No architectural CPU stop is claimed for MOV. -/
theorem correct (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc) :
    DwordStore.step mode state = some (finish mode pc state) ∧
    (finish mode pc state).pc.toNat = pc + 10 ∧
    (finish mode pc state).accumulator = state.accumulator ∧
    (finish mode pc state).stack = state.stack ∧
    (finish mode pc state).carry = state.carry ∧
    (finish mode pc state).memory = state.memory := by
  have position : state.pc.toNat = pc := by
    rw [location]; exact Arithmetic.encode_nat_toNat mode _ (by omega)
  exact ⟨DwordStore.step_encoding mode state (form mode pc) (by simpa only [position, bytes] using current),
    next_position mode pc state location capacity,
    (DwordStore.registers mode (form mode pc) state).1,
    (DwordStore.registers mode (form mode pc) state).2.1,
    (DwordStore.registers mode (form mode pc) state).2.2,
    memory_unchanged mode pc state location capacity current⟩

theorem reusable (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc) :
    ByteMemory.bytesAt (finish mode pc state).memory pc 10 = bytes mode pc := by
  rw [memory_unchanged mode pc state location capacity current]; exact current

theorem output_preserved (mode : Mode) (pc : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (capacity : pc + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc 10 = bytes mode pc) (output count : Nat) :
    ByteMemory.bytesAt (finish mode pc state).memory output count =
      ByteMemory.bytesAt state.memory output count := by
  rw [memory_unchanged mode pc state location capacity current]

end SmcTuring.Native.TerminalMarker
