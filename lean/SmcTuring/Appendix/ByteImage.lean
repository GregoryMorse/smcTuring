module
public import SmcTuring.Appendix.FieldRefinement

public section

namespace SmcTuring.Appendix.ByteImage

open ByteCode

abbrev Memory := Native.ByteMemory.Memory
abbrev Word := BitVec 32

@[expose] def wordAt (memory : Memory) (position : Nat) : Word :=
  BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt memory position 4))

theorem word_at_total (memory : Memory) (position : Nat) :
    Native.LittleEndian.wordDecode 4 (Native.ByteMemory.bytesAt memory position 4) = some (wordAt memory position) := by
  simp [Native.LittleEndian.wordDecode, wordAt]

theorem word_at_window (memory : Memory) (position : Nat) (value : Word)
    (window : Native.ByteMemory.bytesAt memory position 4 = Native.LittleEndian.wordEncode 4 value) :
    wordAt memory position = value := by
  apply Option.some.inj
  rw [←word_at_total, window, Native.LittleEndian.word_decode_encode]

theorem word_at_read_field (state : ByteExecution.State) (position : Nat)
    (fits : position + 4 ≤ 2 ^ 32) : wordAt state.memory position = FieldRefinement.readField state position := by
  unfold wordAt FieldRefinement.readField ByteExecution.prior Native.Execution.load
  change BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt state.memory position 4)) =
    BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt state.memory (FieldRefinement.address position).toNat 4))
  rw [FieldRefinement.address_toNat position fits]

theorem bytes_at_drop (memory : Memory) (pc count offset : Nat) :
    (Native.ByteMemory.bytesAt memory pc (offset + count)).drop offset =
      Native.ByteMemory.bytesAt memory (pc + offset) count := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp [Native.ByteMemory.bytesAt, Nat.add_comm, Nat.add_left_comm]

/-- Extract a complete operand from an actual encoded current packet. -/
theorem payload_window (memory : Memory) (pc : Nat) (leading trailing : List Native.LittleEndian.Byte)
    (value : Word)
    (current : Native.ByteMemory.bytesAt memory pc
      (leading ++ Native.LittleEndian.wordEncode 4 value ++ trailing).length =
        leading ++ Native.LittleEndian.wordEncode 4 value ++ trailing) :
    Native.ByteMemory.bytesAt memory (pc + leading.length) 4 = Native.LittleEndian.wordEncode 4 value := by
  have headerWindow := Native.Fetch.bytes_at_take memory pc
    (leading ++ Native.LittleEndian.wordEncode 4 value ++ trailing).length (leading.length + 4) (by simp)
  rw [current] at headerWindow
  have trimmed : (leading ++ Native.LittleEndian.wordEncode 4 value ++ trailing).take (leading.length + 4) =
      leading ++ Native.LittleEndian.wordEncode 4 value := by
    have length : (leading ++ Native.LittleEndian.wordEncode 4 value).length = leading.length + 4 := by simp
    rw [←length, List.take_append_length]
  rw [trimmed] at headerWindow
  have dropped := congrArg (List.drop leading.length) headerWindow
  rw [bytes_at_drop] at dropped
  simpa only [List.drop_append_length] using dropped.symm

/-- Fixed forms retain every byte. The other constructors expose only the
listed real four-byte operand fields; DEFSTACK may own both disjoint fields. -/
inductive Packet where
  | fixed (form : Form)
  | immediate (op : ImmediateOp) (address initial : Word)
  | both (op : ImmediateOp) (initialAddress initialValue : Word)
  | relative (initial : Word)
  deriving DecidableEq

@[expose] def Packet.initial : Packet → Form
  | .fixed form => form
  | .immediate op address value | .both op address value => .immediate op address value
  | .relative displacement => .callRelative displacement

@[expose] def Packet.offsets : Packet → List Nat
  | .fixed _ => []
  | .immediate _ _ _ => [6]
  | .both _ _ _ => [2, 6]
  | .relative _ => [1]

structure Entry where
  pc : Nat
  packet : Packet
  deriving DecidableEq

@[expose] def Entry.bytes (entry : Entry) : List Native.LittleEndian.Byte := encode entry.packet.initial
@[expose] def Entry.fields (entry : Entry) : List Nat := entry.packet.offsets.map (entry.pc + ·)

@[expose] def current (entry : Entry) (memory : Memory) : Form :=
  match entry.packet with
  | .fixed form => form
  | .immediate op address _ => .immediate op address (wordAt memory (entry.pc + 6))
  | .both op _ _ => .immediate op (wordAt memory (entry.pc + 2)) (wordAt memory (entry.pc + 6))
  | .relative _ => .callRelative (wordAt memory (entry.pc + 1))

/-- Exact current bytes, with finite witnesses solely for the mutable operands.
These witnesses are never substituted for live loads in `current` or `fetch`. -/
@[expose] def PacketIntact (entry : Entry) (memory : Memory) : Prop :=
  match entry.packet with
  | .fixed form => Native.ByteMemory.bytesAt memory entry.pc (encode form).length = encode form
  | .immediate op address _ => ∃ value : Word,
      Native.ByteMemory.bytesAt memory entry.pc (encode (.immediate op address value)).length =
        encode (.immediate op address value)
  | .both op _ _ => ∃ address value : Word,
      Native.ByteMemory.bytesAt memory entry.pc (encode (.immediate op address value)).length =
        encode (.immediate op address value)
  | .relative _ => ∃ value : Word,
      Native.ByteMemory.bytesAt memory entry.pc (encode (.callRelative value)).length = encode (.callRelative value)

@[expose] def Intact (entries : List Entry) (memory : Memory) : Prop :=
  ∀ entry ∈ entries, PacketIntact entry memory

@[expose] def Apart (first second : Entry) : Prop :=
  first.pc + first.bytes.length ≤ second.pc ∨ second.pc + second.bytes.length ≤ first.pc

@[expose] def Separated (entries : List Entry) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries, first ≠ second → Apart first second

@[expose] def Owned (entries : List Entry) (position : Nat) : Prop :=
  ∃ entry ∈ entries, position ∈ entry.fields

@[expose] def image : List Entry → Memory → Memory
  | [], memory => memory
  | entry :: rest, memory => Native.ByteMemory.putBytes (image rest memory) entry.pc entry.bytes

theorem initial_length (entry : Entry) : entry.bytes.length = instructionLength entry.packet.initial := encode_length _

theorem current_length (entry : Entry) (memory : Memory) :
    (encode (current entry memory)).length = entry.bytes.length := by
  cases kind : entry.packet <;> simp [current, Entry.bytes, Packet.initial, kind, encode_length, instructionLength]

theorem immediate_words (memory : Memory) (pc : Nat) (op : ImmediateOp) (address value : Word)
    (currentBytes : Native.ByteMemory.bytesAt memory pc (encode (.immediate op address value)).length =
      encode (.immediate op address value)) :
    wordAt memory (pc + 2) = address ∧ wordAt memory (pc + 6) = value := by
  constructor
  · apply word_at_window
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      payload_window memory pc [op.tag.1, op.tag.2] (Native.LittleEndian.wordEncode 4 value) address currentBytes
  · apply word_at_window
    have prefixLength : ([op.tag.1, op.tag.2] ++ Native.LittleEndian.wordEncode 4 address).length = 6 := by simp
    simpa only [prefixLength] using payload_window memory pc
      ([op.tag.1, op.tag.2] ++ Native.LittleEndian.wordEncode 4 address) [] value (by
        simpa only [encode, List.append_nil] using currentBytes)

theorem relative_word (memory : Memory) (pc : Nat) (value : Word)
    (currentBytes : Native.ByteMemory.bytesAt memory pc (encode (.callRelative value)).length = encode (.callRelative value)) :
    wordAt memory (pc + 1) = value := by
  apply word_at_window
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
    payload_window memory pc [0xe8] [] value (by simpa only [encode, List.append_nil] using currentBytes)

theorem intact_current (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory) :
    Native.ByteMemory.bytesAt memory entry.pc (encode (current entry memory)).length = encode (current entry memory) := by
  cases kind : entry.packet with
  | fixed form => simpa only [PacketIntact, current, kind] using intact
  | immediate op address initial =>
    simp only [PacketIntact, kind] at intact
    rcases intact with ⟨value, bytes⟩
    have words := immediate_words memory entry.pc op address value bytes
    simpa only [current, kind, words.2] using bytes
  | both op address initial =>
    simp only [PacketIntact, kind] at intact
    rcases intact with ⟨address, value, bytes⟩
    have words := immediate_words memory entry.pc op address value bytes
    simpa only [current, kind, words.1, words.2] using bytes
  | relative initial =>
    simp only [PacketIntact, kind] at intact
    rcases intact with ⟨value, bytes⟩
    have word := relative_word memory entry.pc value bytes
    simpa only [current, kind, word] using bytes

theorem fetch_current (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory) :
    fetch memory entry.pc = some (current entry memory) :=
  fetch_current_encoding memory entry.pc _ (intact_current entry memory intact)

theorem initialized_packet (entry : Entry) (memory : Memory)
    (bytes : Native.ByteMemory.bytesAt memory entry.pc entry.bytes.length = entry.bytes) : PacketIntact entry memory := by
  cases kind : entry.packet
  all_goals simp only [PacketIntact, kind]
  case fixed form => simpa only [Entry.bytes, Packet.initial, kind] using bytes
  case immediate op address value => exact ⟨value, by simpa only [Entry.bytes, Packet.initial, kind] using bytes⟩
  case both op address value => exact ⟨address, value, by simpa only [Entry.bytes, Packet.initial, kind] using bytes⟩
  case relative value => exact ⟨value, by simpa only [Entry.bytes, Packet.initial, kind] using bytes⟩

/-- A patch to a packet's own mutable word retains its exact selected form.
Address and immediate patches of the dual owner preserve each other. -/
theorem patch_owner (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory)
    (position : Nat) (member : position ∈ entry.fields) (value : Word) :
    PacketIntact entry (Native.ByteMemory.putWord .x86 memory position value) := by
  cases kind : entry.packet with
  | fixed form => simp [Entry.fields, kind, Packet.offsets] at member
  | immediate op address initial =>
    simp only [Entry.fields, kind, Packet.offsets, List.map_cons, List.map_nil, List.mem_singleton] at member
    subst position
    simp only [PacketIntact, kind] at intact ⊢
    rcases intact with ⟨old, bytes⟩
    have back : Native.ByteMemory.putBytes memory entry.pc (encode (.immediate op address old)) = memory := by
      rw [←bytes]; exact Native.Writes.put_bytes_back memory entry.pc _
    refine ⟨value, ?_⟩
    rw [←back, immediate_patch]
    exact Native.ByteMemory.bytes_at_put _ _ _
  | both op initialAddress initialValue =>
    simp only [Entry.fields, kind, Packet.offsets, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [PacketIntact, kind] at intact ⊢
    rcases intact with ⟨address, old, bytes⟩
    have back : Native.ByteMemory.putBytes memory entry.pc (encode (.immediate op address old)) = memory := by
      rw [←bytes]; exact Native.Writes.put_bytes_back memory entry.pc _
    rcases member with equal | equal <;> subst position
    · refine ⟨value, old, ?_⟩
      rw [←back, address_patch]
      exact Native.ByteMemory.bytes_at_put _ _ _
    · refine ⟨address, value, ?_⟩
      rw [←back, immediate_patch]
      exact Native.ByteMemory.bytes_at_put _ _ _
  | relative initial =>
    simp only [Entry.fields, kind, Packet.offsets, List.map_cons, List.map_nil, List.mem_singleton] at member
    subst position
    simp only [PacketIntact, kind] at intact ⊢
    rcases intact with ⟨old, bytes⟩
    have back : Native.ByteMemory.putBytes memory entry.pc (encode (.callRelative old)) = memory := by
      rw [←bytes]; exact Native.Writes.put_bytes_back memory entry.pc _
    refine ⟨value, ?_⟩
    rw [←back, call_patch]
    exact Native.ByteMemory.bytes_at_put _ _ _

theorem owned_field_inside (entry : Entry) (position : Nat) (member : position ∈ entry.fields) :
    entry.pc ≤ position ∧ position + 4 ≤ entry.pc + entry.bytes.length := by
  cases kind : entry.packet <;>
    simp_all [Entry.fields, Packet.offsets, Entry.bytes, Packet.initial, encode_length, instructionLength]
  all_goals omega

theorem separated_tail (head : Entry) (rest : List Entry) (separate : Separated (head :: rest)) : Separated rest := by
  intro first member second secondMember distinct
  exact separate first (by simp [member]) second (by simp [secondMember]) distinct

theorem apart_bytes (first second : Entry) (apart : Apart first second) (index : Fin second.bytes.length) :
    ¬Native.ByteMemory.Inside first.pc first.bytes.length (second.pc + index.val) := by
  have bound := index.isLt
  rcases apart with before | after <;> unfold Native.ByteMemory.Inside <;> omega

theorem image_packet (entries : List Entry) (memory : Memory) (separate : Separated entries)
    (entry : Entry) (member : entry ∈ entries) :
    Native.ByteMemory.bytesAt (image entries memory) entry.pc entry.bytes.length = entry.bytes := by
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    by_cases same : head = entry
    · subst head; exact Native.ByteMemory.bytes_at_put _ _ _
    · have tailMember : entry ∈ rest := by simpa [Ne.symm same] using member
      rw [image, Native.ByteMemory.bytes_at_frame _ _ _ _ _
        (apart_bytes head entry (separate head (by simp) entry member same))]
      exact ih (separated_tail head rest separate) tailMember

theorem initialized_intact (entries : List Entry) (memory : Memory) (separate : Separated entries) :
    Intact entries (image entries memory) :=
  fun entry member => initialized_packet entry _ (image_packet entries memory separate entry member)

theorem frame_packet (entry : Entry) (first second : Memory)
    (bytes : Native.ByteMemory.bytesAt first entry.pc entry.bytes.length = Native.ByteMemory.bytesAt second entry.pc entry.bytes.length)
    (intact : PacketIntact entry first) : PacketIntact entry second := by
  cases kind : entry.packet <;>
    simp only [PacketIntact, Entry.bytes, Packet.initial, kind, encode_length, instructionLength] at bytes intact ⊢
  · exact bytes.symm.trans intact
  · rcases intact with ⟨value, before⟩
    exact ⟨value, bytes.symm.trans before⟩
  · rcases intact with ⟨address, value, before⟩
    exact ⟨address, value, bytes.symm.trans before⟩
  · rcases intact with ⟨value, before⟩
    exact ⟨value, bytes.symm.trans before⟩

/-- Any owned-word write preserves every packet of the same evolving image. -/
theorem store_intact (entries : List Entry) (memory : Memory) (separate : Separated entries)
    (intact : Intact entries memory) (position : Nat) (value : Word) (owned : Owned entries position) :
    Intact entries (Native.ByteMemory.putWord .x86 memory position value) := by
  rcases owned with ⟨owner, member, field⟩
  intro observed observedMember
  by_cases same : owner = observed
  · subst observed; exact patch_owner owner memory (intact owner member) position field value
  · apply frame_packet observed memory _ _ (intact observed observedMember)
    symm
    apply Native.ByteMemory.bytes_at_frame
    intro index
    have small := index.isLt
    have bounds := owned_field_inside owner position field
    have apart := separate owner member observed observedMember same
    simp only [Native.LittleEndian.word_encode_length, Native.Mode.wordBytes]
    rcases apart with before | after <;> unfold Native.ByteMemory.Inside <;> omega

theorem execute_intact (entries : List Entry) (native : ByteExecution.State) (form : Form)
    (separate : Separated entries) (intact : Intact entries native.memory)
    (owned : Owned entries (ByteExecution.destination form native).toNat) :
    Intact entries (ByteExecution.execute form native).memory := by
  rw [ByteExecution.execute_memory]
  exact store_intact entries native.memory separate intact _ _ owned

end SmcTuring.Appendix.ByteImage
