module
public import SmcTuring.Native.GridImage

public section

namespace SmcTuring.Native.ControlImage

open LittleEndian

/-- Fixed packets include their address/displacement bytes. An owned packet
allows precisely its MOFFS address word to change after initialization. -/
inductive Packet (mode : Mode) where
  | fixed (form : Form mode)
  | owned (initial : Word mode)
  deriving DecidableEq

@[expose] def Packet.bytes (mode : Mode) : Packet mode -> List Byte
  | .fixed form => encode mode form
  | .owned value => encode mode (.moffs value)

structure Entry (mode : Mode) where
  pc : Nat
  packet : Packet mode
  deriving DecidableEq

@[expose] def Entry.bytes (mode : Mode) (entry : Entry mode) : List Byte := entry.packet.bytes mode

@[expose] def Apart (mode : Mode) (first second : Entry mode) : Prop :=
  Or (first.pc + (first.bytes mode).length <= second.pc)
    (second.pc + (second.bytes mode).length <= first.pc)

@[expose] def Separated (mode : Mode) (entries : List (Entry mode)) : Prop :=
  forall first, List.Mem first entries -> forall second, List.Mem second entries ->
    Not (first = second) -> Apart mode first second

/-- Finite byte initializer, overlaying actual encoded packet bytes on the
provided backing memory. Opcode/packet lookup is not an initializer input. -/
@[expose] def image (mode : Mode) : List (Entry mode) -> ByteMemory.Memory -> ByteMemory.Memory
  | [], memory => memory
  | entry :: rest, memory => ByteMemory.putBytes (image mode rest memory) entry.pc (entry.bytes mode)

theorem apart_symmetric (mode : Mode) (first second : Entry mode) (apart : Apart mode first second) :
    Apart mode second first := Or.symm apart

theorem apart_bytes (mode : Mode) (first second : Entry mode) (apart : Apart mode first second)
    (index : Fin (second.bytes mode).length) :
    Not (ByteMemory.Inside first.pc (first.bytes mode).length (second.pc + index.val)) := by
  have small := index.isLt
  rcases apart with before | after <;> unfold ByteMemory.Inside <;> omega

theorem separated_tail (mode : Mode) (head : Entry mode) (rest : List (Entry mode))
    (separate : Separated mode (head :: rest)) : Separated mode rest := by
  intro first member second memberSecond different
  exact separate first (List.Mem.tail head member) second (List.Mem.tail head memberSecond) different

/-- Every listed packet is initialized exactly, as bytes, from finite entries. -/
theorem image_packet (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (separate : Separated mode entries) (entry : Entry mode) (member : List.Mem entry entries) :
    ByteMemory.bytesAt (image mode entries memory) entry.pc (entry.bytes mode).length = entry.bytes mode := by
  induction entries with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : head = entry
    · subst head
      exact ByteMemory.bytes_at_put _ entry.pc (entry.bytes mode)
    · have inTail : List.Mem entry rest := by
        cases member with
        | head => exact False.elim (same rfl)
        | tail _ next => exact next
      have frame := ByteMemory.bytes_at_frame (image mode rest memory) head.pc (head.bytes mode)
        entry.pc (entry.bytes mode).length
        (apart_bytes mode head entry (separate head (List.Mem.head rest) entry member same))
      change ByteMemory.bytesAt (ByteMemory.putBytes (image mode rest memory) head.pc (head.bytes mode))
        entry.pc (entry.bytes mode).length = _
      rw [frame]
      exact ih (separated_tail mode head rest separate) inTail

@[expose] def PacketIntact (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Prop :=
  match entry.packet with
  | .fixed form => ByteMemory.bytesAt memory entry.pc (encode mode form).length = encode mode form
  | .owned _ => Protected.PrefixAt mode memory entry.pc

@[expose] def Intact (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory) : Prop :=
  forall entry, List.Mem entry entries -> PacketIntact mode entry memory

@[expose] def currentForm (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Form mode :=
  match entry.packet with
  | .fixed form => form
  | .owned _ => .moffs (Protected.wordAt mode memory (entry.pc + moffsOperandOffset mode))

theorem initialized_intact (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (separate : Separated mode entries) : Intact mode entries (image mode entries memory) := by
  intro entry member
  have packet := image_packet mode entries memory separate entry member
  cases kind : entry.packet with
  | fixed form => simpa only [PacketIntact, Entry.bytes, kind, Packet.bytes] using packet
  | owned value =>
    have shorter := Fetch.bytes_at_take (image mode entries memory) entry.pc
      (encode mode (.moffs value)).length (moffsOperandOffset mode) (by
        simp [instructionLength, moffsOperandOffset])
    have current : ByteMemory.bytesAt (image mode entries memory) entry.pc
        (encode mode (.moffs value)).length = encode mode (.moffs value) :=
      by simpa only [Entry.bytes, kind, Packet.bytes] using packet
    simp only [PacketIntact, kind]
    unfold Protected.PrefixAt Protected.opcode
    rw [<-shorter, current, moffs_opcode_bytes]

theorem fetch_current (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory)
    (intact : PacketIntact mode entry memory) :
    Fetch.fetch mode memory entry.pc = some (currentForm mode entry memory) := by
  cases kind : entry.packet with
  | fixed form =>
    simp only [currentForm, kind]
    exact Fetch.fetch_current_encoding mode memory entry.pc form (by simpa [PacketIntact, kind] using intact)
  | owned value =>
    simp only [currentForm, kind]
    exact Protected.fetch_moffs mode memory entry.pc (by simpa [PacketIntact, kind] using intact)

/-- Writable addresses are precisely operands of listed owned packets. -/
@[expose] def Owned (mode : Mode) (entries : List (Entry mode)) (address : Word mode) : Prop :=
  exists entry, And (List.Mem entry entries)
    (And (exists initial, entry.packet = .owned initial) (address.toNat = entry.pc + moffsOperandOffset mode))

theorem owned_packet_length (mode : Mode) (entry : Entry mode) (initial : Word mode)
    (kind : entry.packet = .owned initial) :
    (entry.bytes mode).length = moffsOperandOffset mode + mode.wordBytes := by
  simp [Entry.bytes, kind, Packet.bytes, instructionLength, moffsOperandOffset]

/-- An owned-word store preserves the full fixed packet or the owned opcode.
The mutable word itself is fetched live by currentForm. -/
theorem store_intact (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (separate : Separated mode entries) (intact : Intact mode entries memory) (address value : Word mode)
    (owned : Owned mode entries address) :
    Intact mode entries (ByteMemory.putWord mode memory address.toNat value) := by
  cases owned with
  | intro owner owns =>
    rcases owns with ⟨member, ⟨⟨initial, kind⟩, location⟩⟩
    intro observed observedMember
    have before := intact observed observedMember
    by_cases same : owner = observed
    · subst observed
      simp only [PacketIntact, kind]
      rw [Protected.prefix_frame mode memory owner.pc address.toNat value (by
        intro index
        have small := index.isLt
        rw [location]
        unfold ByteMemory.Inside
        omega)]
      simpa [PacketIntact, kind] using before
    · have apart := separate owner member observed observedMember same
      have ownerSize := owned_packet_length mode owner initial kind
      have frame : ByteMemory.bytesAt (ByteMemory.putWord mode memory address.toNat value)
          observed.pc (observed.bytes mode).length =
          ByteMemory.bytesAt memory observed.pc (observed.bytes mode).length := by
        apply ByteMemory.bytes_at_frame
        intro index
        have small := index.isLt
        simp only [word_encode_length]
        rw [location]
        rcases apart with left | right <;> rw [ownerSize] at * <;> unfold ByteMemory.Inside <;> omega
      cases observedKind : observed.packet with
      | fixed form =>
        simp only [PacketIntact, observedKind]
        have fixedFrame : ByteMemory.bytesAt (ByteMemory.putWord mode memory address.toNat value) observed.pc
            (encode mode form).length = ByteMemory.bytesAt memory observed.pc (encode mode form).length :=
          by simpa [Entry.bytes, observedKind, Packet.bytes] using frame
        rw [fixedFrame]
        simpa [PacketIntact, observedKind] using before
      | owned prior =>
        simp only [PacketIntact, observedKind]
        apply (Protected.prefix_frame mode memory observed.pc address.toNat value (by
          intro index
          have small := index.isLt
          rw [location]
          have observedSize := owned_packet_length mode observed prior observedKind
          rcases apart with left | right <;> rw [ownerSize, observedSize] at * <;>
            unfold ByteMemory.Inside <;> omega)).mpr
        simpa [PacketIntact, observedKind] using before

theorem execute_intact (mode : Mode) (entries : List (Entry mode)) (state : Execution.State mode) (form : Form mode)
    (separate : Separated mode entries) (intact : Intact mode entries state.memory)
    (owned : Owned mode entries (Writes.address mode form state)) :
    Intact mode entries (Execution.execute mode form state).memory := by
  rw [Writes.execute_memory]
  exact store_intact mode entries state.memory separate intact _ _ owned

/-- External operand fields, such as the separately placed heap grid, have no
byte overlap with any packet of this control fragment. -/
@[expose] def External (mode : Mode) (entries : List (Entry mode)) (address : Word mode) : Prop :=
  forall entry, List.Mem entry entries -> forall index : Fin (entry.bytes mode).length,
    Not (ByteMemory.Inside address.toNat mode.wordBytes (entry.pc + index.val))

theorem external_store_intact (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (intact : Intact mode entries memory) (address value : Word mode) (external : External mode entries address) :
    Intact mode entries (ByteMemory.putWord mode memory address.toNat value) := by
  intro entry member
  have before := intact entry member
  have frame := ByteMemory.bytes_at_frame memory address.toNat (wordEncode mode.wordBytes value)
    entry.pc (entry.bytes mode).length (by simpa using external entry member)
  cases kind : entry.packet with
  | fixed form =>
    simp only [PacketIntact, kind]
    have fixedFrame : ByteMemory.bytesAt (ByteMemory.putWord mode memory address.toNat value) entry.pc
        (encode mode form).length = ByteMemory.bytesAt memory entry.pc (encode mode form).length :=
      by simpa [ByteMemory.putWord, Entry.bytes, kind, Packet.bytes] using frame
    rw [fixedFrame]
    simpa [PacketIntact, kind] using before
  | owned initial =>
    simp only [PacketIntact, kind]
    rw [Protected.prefix_frame mode memory entry.pc address.toNat value (by
      intro index
      have small := index.isLt
      have length := owned_packet_length mode entry initial kind
      have extended : index.val < (entry.bytes mode).length := by rw [length]; omega
      exact external entry member ⟨index.val, extended⟩)]
    simpa [PacketIntact, kind] using before

@[expose] def Allowed (mode : Mode) (entries : List (Entry mode)) (address : Word mode) : Prop :=
  Or (Owned mode entries address) (External mode entries address)

theorem allowed_store_intact (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (separate : Separated mode entries) (intact : Intact mode entries memory) (address value : Word mode)
    (allowed : Allowed mode entries address) :
    Intact mode entries (ByteMemory.putWord mode memory address.toNat value) := by
  cases allowed with
  | inl owned => exact store_intact mode entries memory separate intact address value owned
  | inr external => exact external_store_intact mode entries memory intact address value external

theorem execute_allowed_intact (mode : Mode) (entries : List (Entry mode)) (state : Execution.State mode) (form : Form mode)
    (separate : Separated mode entries) (intact : Intact mode entries state.memory)
    (allowed : Allowed mode entries (Writes.address mode form state)) :
    Intact mode entries (Execution.execute mode form state).memory := by
  rw [Writes.execute_memory]
  exact allowed_store_intact mode entries state.memory separate intact _ _ allowed

theorem run_allowed_intact (mode : Mode) (entries : List (Entry mode)) (state : Execution.State mode) (forms : List (Form mode))
    (separate : Separated mode entries) (intact : Intact mode entries state.memory)
    (allowed : Writes.OwnedRun mode (Allowed mode entries) forms state) :
    Intact mode entries (Execution.runForms mode forms state).memory := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    change And (Allowed mode entries (Writes.address mode form state))
      (Writes.OwnedRun mode (Allowed mode entries) rest (Execution.execute mode form state)) at allowed
    exact ih (Execution.execute mode form state) (execute_allowed_intact mode entries state form separate intact allowed.1) allowed.2

theorem run_intact (mode : Mode) (entries : List (Entry mode)) (state : Execution.State mode) (forms : List (Form mode))
    (separate : Separated mode entries) (intact : Intact mode entries state.memory)
    (owned : Writes.OwnedRun mode (Owned mode entries) forms state) :
    Intact mode entries (Execution.runForms mode forms state).memory := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    change And (Owned mode entries (Writes.address mode form state))
      (Writes.OwnedRun mode (Owned mode entries) rest (Execution.execute mode form state)) at owned
    exact ih (Execution.execute mode form state) (execute_intact mode entries state form separate intact owned.1) owned.2

theorem trace_intact (mode : Mode) (entries : List (Entry mode)) (state result : Execution.State mode)
    (forms : List (Form mode)) (separate : Separated mode entries) (intact : Intact mode entries state.memory)
    (owned : Writes.OwnedRun mode (Owned mode entries) forms state) (trace : Fetch.Trace mode state forms result) :
    Intact mode entries result.memory := by
  rw [Fetch.trace_run_eq mode trace]
  exact run_intact mode entries state forms separate intact owned

end SmcTuring.Native.ControlImage
