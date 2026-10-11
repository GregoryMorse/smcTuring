module
public import SmcTuring.Native.StringWindow

public section
namespace SmcTuring.Native.StringRestore
open StringExecution

@[expose] def forms (mode : Mode) (destination : Bool) (pc field size : Nat) : List (StringForm.Form mode) :=
  [StringOperands.exchange mode destination pc field,
    StringOperands.subtract mode (pc+StringCodec.exchangeSize mode) field size]
@[expose] def bytes (mode : Mode) (destination : Bool) (pc field size : Nat) : List LittleEndian.Byte :=
  StringCodec.exchangeBytes mode destination pc field++StringCodec.subBytes mode (pc+StringCodec.exchangeSize mode) field size
@[expose] def endpoint (mode : Mode) (pc size : Nat) : Nat := pc+StringCodec.exchangeSize mode+StringCodec.subSize mode size

theorem forms_encoding (mode : Mode) (destination : Bool) (pc field size : Nat) (fits : size < 2^31) :
    ((forms mode destination pc field size).map (StringForm.encode mode)).flatten = bytes mode destination pc field size := by
  simp only [forms,bytes,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    StringOperands.exchange_encoding,StringOperands.subtract_encoding mode _ _ _ fits]

theorem no_borrow (mode : Mode) (base size : Nat) (fits : base+size < 2^(8*mode.wordBytes)) :
    Arithmetic.unsignedBorrow (Arithmetic.encodeNat mode base+Arithmetic.encodeNat mode size) (Arithmetic.encodeNat mode size) = false :=
  StringCursor.no_borrow mode size base ⟨0,Arithmetic.encodeNat mode base⟩ rfl fits

theorem loaded_exchange (mode : Mode) (memory : ByteMemory.Memory) (field : Nat) (value : Word mode)
    (fits : field < 2^(8*mode.wordBytes)) :
    Execution.load mode (ByteMemory.putWord mode memory field value) (Arithmetic.encodeNat mode field) = value := by
  have exactLoad := Execution.load_put_word mode memory (Arithmetic.encodeNat mode field) value
  rw [Arithmetic.encode_nat_toNat mode field fits] at exactLoad
  exact exactLoad

/-- Actual restoring XCHG/SUB returns every bit of the saved SI and restores
its cursor pointer. The final carry is derived from the nonwrapping bound. -/
theorem source_effect (mode : Mode) (pc field size base : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (exchangeRange : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (subtractRange : mode = .x64 -> Relocation.SignedDelta (endpoint mode pc size) field)
    (fieldFits : field < 2^(8*mode.wordBytes)) (sizeFits : size < 2^31)
    (pointerFits : base+size < 2^(8*mode.wordBytes))
    (advanced : state.sourceIndex = Arithmetic.encodeNat mode base+Arithmetic.encodeNat mode size) :
    run mode (forms mode false pc field size) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (endpoint mode pc size)
        carry := false
        memory := ByteMemory.putWord mode state.principal.memory field (Arithmetic.encodeNat mode base)}
      sourceIndex := Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)} := by
  have exchanged := StringOperands.source_effect mode pc field state location exchangeRange fieldFits
  have nextLocation : (execute mode (StringOperands.exchange mode false pc field) state).principal.pc =
      Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) := by rw [exchanged]
  change execute mode (StringOperands.subtract mode (pc+StringCodec.exchangeSize mode) field size)
    (execute mode (StringOperands.exchange mode false pc field) state) = _
  rw [StringOperands.subtract_effect mode _ field size _ nextLocation subtractRange sizeFits,exchanged]
  simp only [loaded_exchange mode _ field _ fieldFits]
  rw [advanced,BitVec.add_sub_cancel,no_borrow mode base size pointerFits]
  unfold Execution.storeState
  rw [Arithmetic.encode_nat_toNat mode field fieldFits,Writes.put_word_overwrite]
  rfl

theorem destination_effect (mode : Mode) (pc field size base : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (exchangeRange : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (subtractRange : mode = .x64 -> Relocation.SignedDelta (endpoint mode pc size) field)
    (fieldFits : field < 2^(8*mode.wordBytes)) (sizeFits : size < 2^31)
    (pointerFits : base+size < 2^(8*mode.wordBytes))
    (advanced : state.destinationIndex = Arithmetic.encodeNat mode base+Arithmetic.encodeNat mode size) :
    run mode (forms mode true pc field size) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (endpoint mode pc size)
        carry := false
        memory := ByteMemory.putWord mode state.principal.memory field (Arithmetic.encodeNat mode base)}
      destinationIndex := Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)} := by
  have exchanged := StringOperands.destination_effect mode pc field state location exchangeRange fieldFits
  have nextLocation : (execute mode (StringOperands.exchange mode true pc field) state).principal.pc =
      Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) := by rw [exchanged]
  change execute mode (StringOperands.subtract mode (pc+StringCodec.exchangeSize mode) field size)
    (execute mode (StringOperands.exchange mode true pc field) state) = _
  rw [StringOperands.subtract_effect mode _ field size _ nextLocation subtractRange sizeFits,exchanged]
  simp only [loaded_exchange mode _ field _ fieldFits]
  rw [advanced,BitVec.add_sub_cancel,no_borrow mode base size pointerFits]
  unfold Execution.storeState
  rw [Arithmetic.encode_nat_toNat mode field fieldFits,Writes.put_word_overwrite]
  rfl

/-- Derive both restoration fetches from the original two-packet bytes. A
static complete-field/second-packet separation proves the tail bytes intact. -/
theorem trace (mode : Mode) (destination : Bool) (pc field size : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (exchangeRange : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (fieldFits : field < 2^(8*mode.wordBytes)) (sizeFits : size < 2^31)
    (codeFits : endpoint mode pc size < 2^(8*mode.wordBytes))
    (separate : ∀ index : Fin (StringCodec.subSize mode size),
      ¬ByteMemory.Inside field mode.wordBytes (pc+StringCodec.exchangeSize mode+index.val))
    (current : ByteMemory.bytesAt state.principal.memory pc (bytes mode destination pc field size).length = bytes mode destination pc field size) :
    Trace mode state (forms mode destination pc field size) (run mode (forms mode destination pc field size) state) := by
  have startFits : pc < 2^(8*mode.wordBytes) := by unfold endpoint at codeFits; omega
  have nextFits : pc+StringCodec.exchangeSize mode < 2^(8*mode.wordBytes) := by unfold endpoint at codeFits; omega
  have head : ByteMemory.bytesAt state.principal.memory pc (StringCodec.exchangeBytes mode destination pc field).length = StringCodec.exchangeBytes mode destination pc field := by
    simpa only [List.nil_append,List.length_nil,Nat.add_zero] using StringWindow.packet_window state.principal.memory pc []
      (StringCodec.exchangeBytes mode destination pc field) (StringCodec.subBytes mode (pc+StringCodec.exchangeSize mode) field size) current
  have fetched : StringForm.fetch mode state.principal.memory state.principal.pc.toNat = some (StringOperands.exchange mode destination pc field) := by
    rw [location,Arithmetic.encode_nat_toNat mode pc startFits]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [StringOperands.exchange_encoding]
    exact head
  let swapped := execute mode (StringOperands.exchange mode destination pc field) state
  have swappedPC : swapped.principal.pc = Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) := by
    cases destination
    · rw [show swapped = execute mode (StringOperands.exchange mode false pc field) state from rfl,
        StringOperands.source_effect mode pc field state location exchangeRange fieldFits]
    · rw [show swapped = execute mode (StringOperands.exchange mode true pc field) state from rfl,
        StringOperands.destination_effect mode pc field state location exchangeRange fieldFits]
  have swappedMemory : swapped.principal.memory = ByteMemory.putWord mode state.principal.memory field (if destination then state.destinationIndex else state.sourceIndex) := by
    cases destination
    · rw [show swapped = execute mode (StringOperands.exchange mode false pc field) state from rfl,
        StringOperands.source_effect mode pc field state location exchangeRange fieldFits]
      rfl
    · rw [show swapped = execute mode (StringOperands.exchange mode true pc field) state from rfl,
        StringOperands.destination_effect mode pc field state location exchangeRange fieldFits]
      rfl
  have tail : ByteMemory.bytesAt state.principal.memory (pc+StringCodec.exchangeSize mode) (StringCodec.subSize mode size) =
      StringCodec.subBytes mode (pc+StringCodec.exchangeSize mode) field size := by
    have original := StringWindow.packet_window state.principal.memory pc (StringCodec.exchangeBytes mode destination pc field)
      (StringCodec.subBytes mode (pc+StringCodec.exchangeSize mode) field size) [] (by simpa only [List.append_nil,bytes] using current)
    rw [StringCodec.exchange_length,StringCodec.sub_length] at original
    exact original
  have nextFetched : StringForm.fetch mode swapped.principal.memory swapped.principal.pc.toNat =
      some (StringOperands.subtract mode (pc+StringCodec.exchangeSize mode) field size) := by
    rw [swappedPC,Arithmetic.encode_nat_toNat mode _ nextFits]
    apply StringForm.fetch_current_encoding mode _ _ _ (by unfold StringOperands.subtract; split <;> trivial)
    rw [StringOperands.subtract_encoding mode _ _ size sizeFits,StringCodec.sub_length,swappedMemory]
    unfold ByteMemory.putWord
    rw [ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using separate),tail]
  exact .step fetched (.step nextFetched (.nil _))

end SmcTuring.Native.StringRestore
