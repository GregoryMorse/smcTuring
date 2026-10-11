module
public import SmcTuring.Appendix.MultiplyPacking

public section

namespace SmcTuring.Appendix.MultiplyRegions

open MultiplyImage

/-- A contiguous pure packet block. Bytes in gaps belong to arbitrary backing
memory; no gap is fabricated as a pure instruction or executed by this block. -/
structure Region where
  start : Nat
  packets : List Packet
@[expose] def Region.finish (region : Region) : Nat := region.start + MultiplyPacking.size region.packets
@[expose] def Region.entries (region : Region) : List Entry := MultiplyPacking.place region.start region.packets
@[expose] def entries (regions : List Region) : List Entry := regions.flatMap Region.entries
@[expose] def Ordered (regions : List Region) : Prop :=
  regions.Pairwise (fun first second => first.finish ≤ second.start)

theorem member (regions : List Region) (entry : Entry) :
    entry ∈ entries regions ↔ ∃ region ∈ regions, entry ∈ region.entries := by
  simp only [entries, List.mem_flatMap]

theorem entry_bounds (region : Region) (entry : Entry) (member : entry ∈ region.entries) :
    region.start ≤ entry.pc ∧ entry.pc + entry.bytes.length ≤ region.finish :=
  ⟨MultiplyPacking.placed_lower _ _ _ member, MultiplyPacking.placed_upper _ _ _ member⟩

theorem separated_append (first second : List Entry) (left : Separated first) (right : Separated second)
    (before : ∀ a ∈ first, ∀ b ∈ second, a.pc + a.bytes.length ≤ b.pc) :
    Separated (first ++ second) := by
  intro a aMember b bMember distinct
  simp only [List.mem_append] at aMember bMember
  rcases aMember with aLeft | aRight
  · rcases bMember with bLeft | bRight
    · exact left a aLeft b bLeft distinct
    · exact Or.inl (before a aLeft b bRight)
  · rcases bMember with bLeft | bRight
    · exact Or.inr (before b bLeft a aRight)
    · exact right a aRight b bRight distinct

theorem separated (regions : List Region) (ordered : Ordered regions) : Separated (entries regions) := by
  induction regions with
  | nil => intro entry member; simp [entries] at member
  | cons region rest ih =>
    have order : (∀ later ∈ rest, region.finish ≤ later.start) ∧ Ordered rest := by
      simpa only [Ordered, List.pairwise_cons] using ordered
    change Separated (region.entries ++ entries rest)
    apply separated_append _ _ (MultiplyPacking.placed_separated _ _) (ih order.2)
    intro first firstMember second secondMember
    rcases (member rest second).mp secondMember with ⟨later, laterMember, inLater⟩
    have firstBounds := entry_bounds region first firstMember
    have secondBounds := entry_bounds later second inLater
    exact Nat.le_trans (Nat.le_trans firstBounds.2 (order.1 later laterMember)) secondBounds.1

theorem capacity (regions : List Region) (bounds : ∀ region ∈ regions, region.finish ≤ 2 ^ 32) :
    ∀ entry ∈ entries regions, entry.pc + entry.bytes.length ≤ 2 ^ 32 := by
  intro entry inImage
  rcases (member regions entry).mp inImage with ⟨region, inRegions, inRegion⟩
  exact Nat.le_trans (entry_bounds region entry inRegion).2 (bounds region inRegions)

theorem field_layout (regions : List Region) (ordered : Ordered regions)
    (bounds : ∀ region ∈ regions, region.finish ≤ 2 ^ 32) :
    FieldRefinement.Layout (MultiplyPacking.fields (entries regions)) :=
  MultiplyPacking.field_layout _ (separated regions ordered) (capacity regions bounds)

theorem initial_intact (regions : List Region) (backing : Memory) (ordered : Ordered regions) :
    Intact (entries regions) (image (entries regions) backing) :=
  initialized_intact _ backing (separated regions ordered)

theorem image_append (first second : List Entry) (backing : Memory) :
    image (first ++ second) backing = image first (image second backing) := by
  induction first with
  | nil => rfl
  | cons entry rest ih => simp only [List.cons_append, image, ih]

theorem image_frame (regions : List Region) (backing : Memory) (position : Nat)
    (outside : ∀ region ∈ regions, position < region.start ∨ region.finish ≤ position) :
    image (entries regions) backing position = backing position := by
  induction regions with
  | nil => rfl
  | cons region rest ih =>
    change image (region.entries ++ entries rest) backing position = backing position
    rw [image_append]
    change image (MultiplyPacking.place region.start region.packets) (image (entries rest) backing) position = backing position
    rw [MultiplyPacking.image_frame _ _ _ position (outside region (by simp))]
    exact ih (fun later member => outside later (by simp [member]))

theorem outside_owned (regions : List Region) (position : Nat)
    (outside : ∀ region ∈ regions, position < region.start ∨ region.finish ≤ position)
    (field : Nat) (owned : Owned (entries regions) field) : ¬Native.ByteMemory.Inside field 4 position := by
  rcases owned with ⟨owner, inEntries, inOwner⟩
  rcases (member regions owner).mp inEntries with ⟨region, inRegions, inRegion⟩
  have block := entry_bounds region owner inRegion
  have word := owned_field_inside owner field inOwner
  have exterior := outside region inRegions
  unfold Native.ByteMemory.Inside
  omega

end SmcTuring.Appendix.MultiplyRegions
