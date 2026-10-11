module
public import SmcTuring.Native.ReaderImage
public import SmcTuring.Native.Relocation
public import SmcTuring.Native.SpacedCombinedImage

public section

namespace SmcTuring.Native.Fragment

open ControlImage

theorem size_append (mode : Mode) (first second : List (Packet mode)) :
    ControlPacking.size mode (first ++ second) = ControlPacking.size mode first + ControlPacking.size mode second := by
  simp [ControlPacking.size]

theorem place_append (mode : Mode) (start : Nat) (first second : List (Packet mode)) :
    ControlPacking.place mode start (first ++ second) = ControlPacking.place mode start first ++
      ControlPacking.place mode (start + ControlPacking.size mode first) second := by
  induction first generalizing start with
  | nil => simp [ControlPacking.place, ControlPacking.size]
  | cons head tail ih =>
    simp [ControlPacking.place, ControlPacking.size, ih, Nat.add_assoc]

/-- A fragment view names only finite computed entries in the complete image.
It is not a predicate on decoded packets or an instruction-fetch callback. -/
@[expose] def Within (mode : Mode) (fragment : List (Entry mode)) (whole : List (Entry mode)) : Prop :=
  forall entry, List.Mem entry fragment -> List.Mem entry whole

theorem prefix_within (mode : Mode) (start : Nat) (first second : List (Packet mode)) :
    Within mode (ControlPacking.place mode start first) (ControlPacking.place mode start (first ++ second)) := by
  intro entry member
  rw [place_append]
  exact List.mem_append_left _ member

theorem suffix_within (mode : Mode) (start : Nat) (first second : List (Packet mode)) :
    Within mode (ControlPacking.place mode (start + ControlPacking.size mode first) second)
      (ControlPacking.place mode start (first ++ second)) := by
  intro entry member
  rw [place_append]
  exact List.mem_append_right _ member

theorem within_trans (mode : Mode) (first second third : List (Entry mode))
    (left : Within mode first second) (right : Within mode second third) : Within mode first third :=
  fun entry member => right entry (left entry member)

theorem intact_view (mode : Mode) (first second : List (Entry mode)) (memory : ByteMemory.Memory)
    (within : Within mode first second) (intact : Intact mode second memory) : Intact mode first memory :=
  fun entry member => intact entry (within entry member)

theorem owned_view (mode : Mode) (first second : List (Entry mode)) (address : Word mode)
    (within : Within mode first second) (owned : Owned mode first address) : Owned mode second address := by
  rcases owned with ⟨entry, member, kind, location⟩
  exact ⟨entry, within entry member, kind, location⟩

/-- A finite owned packet initializes its actual operand word exactly. The
metadata value is recovered from the constructed byte image, not assumed as
an initial-memory load equation. -/
theorem initialized_owned_word (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin gridBase : Nat)
    (values : Nat -> Word mode) (entry : Entry mode)
    (member : List.Mem entry (SpacedPacking.place mode origin whole)) (initial address : Word mode)
    (kind : entry.packet = .owned initial) (location : address.toNat = entry.pc + moffsOperandOffset mode) :
    Execution.load mode (SpacedCombinedImage.image mode whole origin gridBase values) address = initial := by
  have bytes := SpacedPacking.initial_packet mode whole origin (GridImage.image mode gridBase values) entry member
  have current : ByteMemory.bytesAt (SpacedCombinedImage.image mode whole origin gridBase values) entry.pc
      (encode mode (.moffs initial)).length = encode mode (.moffs initial) := by
    simpa only [SpacedCombinedImage.image, Entry.bytes, kind, Packet.bytes] using bytes
  have encoded := Fetch.fetch_current_encoding mode (SpacedCombinedImage.image mode whole origin gridBase values) entry.pc (.moffs initial) current
  have intact := SpacedPacking.initially_intact mode whole origin (GridImage.image mode gridBase values) entry member
  have live := Protected.fetch_moffs mode (SpacedCombinedImage.image mode whole origin gridBase values) entry.pc
    (by simpa only [SpacedCombinedImage.image, PacketIntact, kind] using intact)
  rw [<-location] at live
  exact Form.moffs.inj (Option.some.inj (live.symm.trans encoded))

/-- An owned field either is the observed owner's field or is byte-disjoint
from the owner's complete packet. This also covers pointers into other readers
and scalar metadata, beyond the register/heap grid. -/
theorem owned_packet_safe (mode : Mode) (packets : List (SpacedPacking.Piece mode)) (start gridBase : Nat)
    (observed : Entry mode) (member : List.Mem observed (SpacedPacking.place mode start packets))
    (label address : Word mode) (labelLocation : label.toNat = observed.pc + moffsOperandOffset mode)
    (gap : start + SpacedPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (owned : SpacedCombinedImage.Owned mode packets start gridBase address) :
    Or (address = label) (forall index : Fin (observed.bytes mode).length,
      Not (ByteMemory.Inside address.toNat mode.wordBytes (observed.pc + index.val))) := by
  cases owned with
  | inl control =>
    rcases control with ⟨owner, ownerMember, ⟨initial, kind⟩, location⟩
    by_cases same : owner = observed
    · apply Or.inl
      apply BitVec.eq_of_toNat_eq
      rw [location, same, labelLocation]
    · apply Or.inr
      intro index inside
      have separate := apart_bytes mode owner observed
        (SpacedPacking.placed_separated mode packets start owner ownerMember observed member same) index
      apply separate
      have length := owned_packet_length mode owner initial kind
      unfold ByteMemory.Inside at *
      rw [location] at inside
      omega
  | inr grid =>
    apply Or.inr
    apply SpacedPacking.above_external mode packets start address _ observed member
    rcases grid with ⟨cell, location⟩
    rw [location]
    unfold Layout.fieldAddress
    omega

theorem owned_fields_separate (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin gridBase : Nat)
    (first second : Word mode)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (firstOwned : SpacedCombinedImage.Owned mode whole origin gridBase first)
    (secondOwned : SpacedCombinedImage.Owned mode whole origin gridBase second) (different : Not (first = second)) :
    forall index : Fin mode.wordBytes, Not (ByteMemory.Inside second.toNat mode.wordBytes (first.toNat + index.val)) := by
  cases firstOwned with
  | inl control =>
    rcases control with ⟨entry, member, ⟨initial, kind⟩, location⟩
    have safe := owned_packet_safe mode whole origin gridBase entry member first second location gap secondOwned
    rcases safe with same | separate
    · exact False.elim (different same.symm)
    · intro index
      let observed : Fin (entry.bytes mode).length :=
        ⟨moffsOperandOffset mode + index.val, by rw [owned_packet_length mode entry initial kind]; have small := index.isLt; omega⟩
      rw [location]
      simpa only [observed, Nat.add_assoc] using separate observed
  | inr grid =>
    rcases grid with ⟨firstCell, firstLocation⟩
    cases secondOwned with
    | inl control =>
      rcases control with ⟨entry, member, ⟨initial, kind⟩, location⟩
      have bound := SpacedPacking.placed_upper mode whole origin entry member
      rw [owned_packet_length mode entry initial kind] at bound
      intro index inside
      rw [firstLocation, location] at inside
      unfold ByteMemory.Inside Layout.fieldAddress at inside
      omega
    | inr grid =>
      rcases grid with ⟨secondCell, secondLocation⟩
      have distinct : Not (firstCell = secondCell) := by
        intro same
        apply different
        apply BitVec.eq_of_toNat_eq
        rw [firstLocation, secondLocation, same]
      intro index inside
      rw [firstLocation, secondLocation] at inside
      have small := index.isLt
      unfold ByteMemory.Inside at inside
      cases mode <;> simp [Layout.fieldAddress, Mode.stride, Mode.wordBytes] at * <;> omega

end SmcTuring.Native.Fragment
