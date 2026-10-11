module
public import SmcTuring.Appendix.DivisionImage
public import SmcTuring.Appendix.MultiplyPacking

public section

namespace SmcTuring.Appendix.DivisionPacking

open DivisionImage

@[expose] def size (packets : List Packet) : Nat := (packets.map (fun packet => (DivisionByteCode.encode packet.initial).length)).sum
@[expose] def place : Nat → List Packet → List Entry
  | _, [] => []
  | start, packet :: rest => ⟨start, packet⟩ :: place (start + (DivisionByteCode.encode packet.initial).length) rest

theorem size_cons (packet : Packet) (rest : List Packet) :
    size (packet :: rest) = (DivisionByteCode.encode packet.initial).length + size rest := rfl

theorem size_append (first second : List Packet) : size (first ++ second) = size first + size second := by
  simp [size]

theorem place_append (first second : List Packet) (start : Nat) :
    place start (first ++ second) = place start first ++ place (start + size first) second := by
  induction first generalizing start with
  | nil => simp [place, size]
  | cons packet rest ih => simp [place, size_cons, ih, Nat.add_assoc]

theorem placed_lower (packets : List Packet) (start : Nat) (entry : Entry) (member : entry ∈ place start packets) :
    start ≤ entry.pc := by
  induction packets generalizing start with
  | nil => simp [place] at member
  | cons packet rest ih =>
    simp only [place, List.mem_cons] at member
    rcases member with equal | inTail
    · subst entry; exact Nat.le_refl start
    · exact Nat.le_trans (Nat.le_add_right start _) (ih _ inTail)

theorem placed_upper (packets : List Packet) (start : Nat) (entry : Entry) (member : entry ∈ place start packets) :
    entry.pc + entry.bytes.length ≤ start + size packets := by
  induction packets generalizing start with
  | nil => simp [place] at member
  | cons packet rest ih =>
    simp only [place, List.mem_cons] at member
    rcases member with equal | inTail
    · subst entry; simp [Entry.bytes, size_cons]
    · simpa only [size_cons, Nat.add_assoc] using ih _ inTail

theorem placed_separated (packets : List Packet) (start : Nat) : Separated (place start packets) := by
  induction packets generalizing start with
  | nil => intro entry member; simp [place] at member
  | cons packet rest ih =>
    intro first member second secondMember different
    simp only [place, List.mem_cons] at member secondMember
    rcases member with equal | firstTail
    · subst first
      rcases secondMember with equal | secondTail
      · subst second; exact False.elim (different rfl)
      · exact Or.inl (placed_lower rest _ second secondTail)
    · rcases secondMember with equal | secondTail
      · subst second; exact Or.inr (placed_lower rest _ first firstTail)
      · exact ih _ first firstTail second secondTail different

theorem initial_intact (packets : List Packet) (start : Nat) (memory : Memory) :
    Intact (place start packets) (image (place start packets) memory) :=
  initialized_intact _ memory (placed_separated packets start)

theorem initial_fetch (packets : List Packet) (start : Nat) (memory : Memory)
    (entry : Entry) (member : entry ∈ place start packets) :
    DivisionByteCode.fetch (image (place start packets) memory) entry.pc =
      some (current entry (image (place start packets) memory)) :=
  fetch_current entry _ (initial_intact packets start memory entry member)

@[expose] def fields (entries : List Entry) : List Nat := entries.flatMap Entry.fields

theorem fields_append (first second : List Entry) :
    fields (first ++ second) = fields first ++ fields second := by simp only [fields, List.flatMap_append]

theorem fields_owned (entries : List Entry) (position : Nat) : position ∈ fields entries ↔ Owned entries position := by
  simp only [fields, List.mem_flatMap, Owned]

theorem same_owner_separate (entry : Entry) (first second : Nat)
    (firstIn : first ∈ entry.fields) (secondIn : second ∈ entry.fields) (different : first ≠ second) :
    first + 4 ≤ second ∨ second + 4 ≤ first := by
  rcases entry with ⟨pc, packet⟩
  cases packet with
  | common packet => exact MultiplyPacking.same_owner_separate ⟨pc, packet⟩ first second firstIn secondIn different
  | fixed form => simp [Entry.fields, Packet.offsets] at firstIn
  | subtractImmediate address value =>
    simp only [Entry.fields, Packet.offsets, List.map_cons, List.map_nil, List.mem_singleton] at firstIn secondIn
    exact False.elim (different (firstIn.trans secondIn.symm))

theorem owned_separate (entries : List Entry) (separate : Separated entries) (first second : Nat)
    (firstOwned : Owned entries first) (secondOwned : Owned entries second) (different : first ≠ second) :
    first + 4 ≤ second ∨ second + 4 ≤ first := by
  rcases firstOwned with ⟨firstOwner, firstMember, firstField⟩
  rcases secondOwned with ⟨secondOwner, secondMember, secondField⟩
  by_cases same : firstOwner = secondOwner
  · subst secondOwner; exact same_owner_separate firstOwner first second firstField secondField different
  · have firstBounds := owned_field_inside firstOwner first firstField
    have secondBounds := owned_field_inside secondOwner second secondField
    have apart := separate firstOwner firstMember secondOwner secondMember same
    rcases apart with before | after <;> omega

/-- The finite-word layout is derived from actual operand ownership and packet
placement. Its only resource premise bounds complete encoded packet extents. -/
theorem field_layout (entries : List Entry) (separate : Separated entries)
    (capacity : ∀ entry ∈ entries, entry.pc + entry.bytes.length ≤ 2 ^ 32) :
    FieldRefinement.Layout (fields entries) := by
  constructor
  · intro field member
    rcases (fields_owned entries field).mp member with ⟨owner, ownerMember, fieldMember⟩
    have bounds := owned_field_inside owner field fieldMember
    have fit := capacity owner ownerMember
    omega
  · intro first firstMember second secondMember different
    exact owned_separate entries separate first second
      ((fields_owned entries first).mp firstMember) ((fields_owned entries second).mp secondMember) different

theorem placed_field_layout (packets : List Packet) (start : Nat)
    (capacity : start + size packets ≤ 2 ^ 32) : FieldRefinement.Layout (fields (place start packets)) := by
  apply field_layout _ (placed_separated packets start)
  intro entry member
  exact Nat.le_trans (placed_upper packets start entry member) capacity

theorem image_frame (packets : List Packet) (start : Nat) (memory : Memory) (position : Nat)
    (outside : position < start ∨ start + size packets ≤ position) :
    image (place start packets) memory position = memory position := by
  induction packets generalizing start with
  | nil => rfl
  | cons packet rest ih =>
    have headOutside : ¬Native.ByteMemory.Inside start (DivisionByteCode.encode packet.initial).length position := by
      rw [size_cons] at outside
      rcases outside with before | after <;> unfold Native.ByteMemory.Inside <;> omega
    have tailOutside : position < start + (DivisionByteCode.encode packet.initial).length ∨
        start + (DivisionByteCode.encode packet.initial).length + size rest ≤ position := by
      rw [size_cons] at outside
      rcases outside with before | after
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    change Native.ByteMemory.putBytes (image (place (start + (DivisionByteCode.encode packet.initial).length) rest) memory)
      start (DivisionByteCode.encode packet.initial) position = memory position
    rw [Native.ByteMemory.put_frame _ _ _ _ headOutside]
    exact ih _ tailOutside

end SmcTuring.Appendix.DivisionPacking
