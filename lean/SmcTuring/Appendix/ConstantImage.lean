module
public import SmcTuring.Appendix.ConstantByteExecution
public import SmcTuring.Appendix.MultiplyPacking

public section
namespace SmcTuring.Appendix.ConstantImage

open ConstantByteCode
open ByteImage (wordAt)
abbrev Memory := Native.ByteMemory.Memory

/-- Reuse all checked branch/multiplication owners, including the ADD imm32,
and add fixed variable-count SHLs. Their address/header/count bytes are protected. -/
inductive Packet where
  | common (packet : MultiplyImage.Packet)
  | fixed (form : Form)
  deriving DecidableEq

@[expose] def Packet.initial : Packet → Form
  | .common packet => .common packet.initial
  | .fixed form => form
@[expose] def Packet.offsets : Packet → List Nat
  | .common packet => packet.offsets
  | .fixed _ => []

structure Entry where
  pc : Nat
  packet : Packet
  deriving DecidableEq

@[expose] def Entry.bytes (entry : Entry) : List Native.LittleEndian.Byte := encode entry.packet.initial
@[expose] def Entry.fields (entry : Entry) : List Nat := entry.packet.offsets.map (entry.pc + ·)

@[expose] def current (entry : Entry) (memory : Memory) : Form :=
  match entry.packet with
  | .common packet => .common (MultiplyImage.current ⟨entry.pc, packet⟩ memory)
  | .fixed form => form
@[expose] def PacketIntact (entry : Entry) (memory : Memory) : Prop :=
  match entry.packet with
  | .common packet => MultiplyImage.PacketIntact ⟨entry.pc, packet⟩ memory
  | .fixed form => Native.ByteMemory.bytesAt memory entry.pc (encode form).length = encode form
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
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.current_length ⟨pc, packet⟩ memory
  | fixed form => rfl
theorem intact_current (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory) :
    Native.ByteMemory.bytesAt memory entry.pc (encode (current entry memory)).length =
      encode (current entry memory) := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.intact_current ⟨pc, packet⟩ memory intact
  | fixed form => exact intact
theorem fetch_current (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory) :
    fetch memory entry.pc = some (current entry memory) :=
  fetch_current_encoding memory entry.pc _ (intact_current entry memory intact)

theorem initialized_packet (entry : Entry) (memory : Memory)
    (bytes : Native.ByteMemory.bytesAt memory entry.pc entry.bytes.length = entry.bytes) : PacketIntact entry memory := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.initialized_packet ⟨pc, packet⟩ memory bytes
  | fixed form => exact bytes
theorem patch_owner (entry : Entry) (memory : Memory) (intact : PacketIntact entry memory)
    (position : Nat) (member : position ∈ entry.fields) (value : Word) :
    PacketIntact entry (Native.ByteMemory.putWord .x86 memory position value) := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.patch_owner ⟨pc, packet⟩ memory intact position member value
  | fixed form => simp [Entry.fields, Packet.offsets] at member
theorem owned_field_inside (entry : Entry) (position : Nat) (member : position ∈ entry.fields) :
    entry.pc ≤ position ∧ position + 4 ≤ entry.pc + entry.bytes.length := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.owned_field_inside ⟨pc, packet⟩ position member
  | fixed form => simp [Entry.fields, Packet.offsets] at member
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
    (bytes : Native.ByteMemory.bytesAt first entry.pc entry.bytes.length =
      Native.ByteMemory.bytesAt second entry.pc entry.bytes.length)
    (intact : PacketIntact entry first) : PacketIntact entry second := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyImage.frame_packet ⟨pc, packet⟩ first second bytes intact
  | fixed form => exact bytes.symm.trans intact
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

theorem execute_intact (entries : List Entry) (native : ConstantByteExecution.State) (form : Form)
    (separate : Separated entries) (intact : Intact entries native.memory)
    (owned : Owned entries (ConstantByteExecution.destination form native).toNat) :
    Intact entries (ConstantByteExecution.execute form native).memory := by
  rw [ConstantByteExecution.execute_memory]
  exact store_intact entries native.memory separate intact _ _ owned


end SmcTuring.Appendix.ConstantImage
