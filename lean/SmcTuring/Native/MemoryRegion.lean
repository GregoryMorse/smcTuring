module
public import SmcTuring.Native.Writes

public section

namespace SmcTuring.Native.MemoryRegion

open LittleEndian Execution

/-- A finite loaded byte interval. An empty or reversed interval contains no bytes. -/
structure Region where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

@[expose] def Region.size (region : Region) : Nat := region.upper - region.lower

@[expose] def Region.Contains (region : Region) (address count : Nat) : Prop :=
  region.lower ≤ address ∧ address + count ≤ region.upper

instance (region : Region) (address count : Nat) : Decidable (region.Contains address count) :=
  inferInstanceAs (Decidable (region.lower ≤ address ∧ address + count ≤ region.upper))

/-- Agreement is required only on loaded bytes; exterior completions may differ. -/
@[expose] def Agree (region : Region) (left right : ByteMemory.Memory) : Prop :=
  ∀ position, region.lower ≤ position → position < region.upper → left position = right position

theorem agree_refl (region : Region) (memory : ByteMemory.Memory) : Agree region memory memory :=
  fun _ _ _ => rfl

theorem agree_symm (region : Region) {left right : ByteMemory.Memory} (same : Agree region left right) :
    Agree region right left := fun position lower upper => (same position lower upper).symm

theorem agree_trans (region : Region) {first second third : ByteMemory.Memory}
    (leading : Agree region first second) (trailing : Agree region second third) :
    Agree region first third := fun position lower upper =>
  (leading position lower upper).trans (trailing position lower upper)

theorem contains_byte (region : Region) (address count : Nat) (contained : region.Contains address count)
    (index : Fin count) : region.lower ≤ address + index.val ∧ address + index.val < region.upper := by
  rcases contained with ⟨lower, upper⟩
  have bound := index.isLt
  omega

/-- No unloaded byte participates in a contained instruction or data window. -/
theorem bytes_agree (region : Region) {left right : ByteMemory.Memory} (same : Agree region left right)
    (address count : Nat) (contained : region.Contains address count) :
    ByteMemory.bytesAt left address count = ByteMemory.bytesAt right address count := by
  apply congrArg List.ofFn
  funext index
  exact same _ (contains_byte region address count contained index).1
    (contains_byte region address count contained index).2

theorem load_agree (mode : Mode) (region : Region) {left right : ByteMemory.Memory}
    (same : Agree region left right) (address : Word mode) (contained : region.Contains address.toNat mode.wordBytes) :
    load mode left address = load mode right address := by
  unfold load
  rw [bytes_agree region same address.toNat mode.wordBytes contained]

/-- Identical writes preserve loaded-byte agreement even if they overlap fields. -/
theorem put_bytes_agree (region : Region) {left right : ByteMemory.Memory} (same : Agree region left right)
    (address : Nat) (bytes : List Byte) :
    Agree region (ByteMemory.putBytes left address bytes) (ByteMemory.putBytes right address bytes) := by
  intro position lower upper
  by_cases inside : ByteMemory.Inside address bytes.length position
  · simp only [ByteMemory.putBytes, dite_eq_left inside]
  · simp only [ByteMemory.putBytes, dite_eq_right inside]
    exact same position lower upper

theorem put_word_agree (mode : Mode) (region : Region) {left right : ByteMemory.Memory}
    (same : Agree region left right) (address : Nat) (value : Word mode) :
    Agree region (ByteMemory.putWord mode left address value) (ByteMemory.putWord mode right address value) :=
  put_bytes_agree region same address _

/-- A contained whole-word store never changes any byte outside the loaded region. -/
theorem put_word_outside (mode : Mode) (region : Region) (memory : ByteMemory.Memory)
    (address : Nat) (value : Word mode) (contained : region.Contains address mode.wordBytes)
    (position : Nat) (outside : ¬(region.lower ≤ position ∧ position < region.upper)) :
    ByteMemory.putWord mode memory address value position = memory position := by
  apply ByteMemory.put_frame
  simp only [word_encode_length]
  intro inside
  rcases contained with ⟨lower, upper⟩
  rcases inside with ⟨start, finish⟩
  apply outside
  constructor <;> omega

/-- Exactly region.size bytes, indexed by a finite type. No exterior memory is stored. -/
abbrev Image (region : Region) := Fin region.size → Byte

@[expose] def snapshot (region : Region) (memory : ByteMemory.Memory) : Image region :=
  fun index => memory (region.lower + index.val)

/-- Zero is an arbitrary completion, used only to execute the existing byte model.
The refinement below proves independence from this choice for contained accesses. -/
@[expose] def expand (region : Region) (image : Image region) : ByteMemory.Memory :=
  fun position => if inside : ByteMemory.Inside region.lower region.size position then
    image ⟨position - region.lower, by unfold ByteMemory.Inside at inside; omega⟩ else 0

theorem expanded_snapshot_agrees (region : Region) (memory : ByteMemory.Memory) :
    Agree region (expand region (snapshot region memory)) memory := by
  intro position lower upper
  have inside : ByteMemory.Inside region.lower region.size position := by
    unfold ByteMemory.Inside Region.size
    omega
  simp only [expand, dite_eq_left inside, snapshot]
  rw [Nat.add_sub_of_le lower]

theorem snapshot_expand (region : Region) (image : Image region) :
    snapshot region (expand region image) = image := by
  funext index
  have bound := index.isLt
  have inside : ByteMemory.Inside region.lower region.size (region.lower + index.val) := by
    unfold ByteMemory.Inside
    omega
  simp only [snapshot, expand, dite_eq_left inside, Nat.add_sub_cancel_left]

/-- A finite update writes a full word, then retains only the loaded bytes. -/
@[expose] def store (mode : Mode) (region : Region) (image : Image region)
    (address : Nat) (value : Word mode) : Image region :=
  snapshot region (ByteMemory.putWord mode (expand region image) address value)

theorem store_agrees (mode : Mode) (region : Region) (image : Image region)
    (memory : ByteMemory.Memory) (same : Agree region (expand region image) memory)
    (address : Nat) (value : Word mode) :
    Agree region (expand region (store mode region image address value))
      (ByteMemory.putWord mode memory address value) :=
  agree_trans region (expanded_snapshot_agrees region _)
    (put_word_agree mode region same address value)

end SmcTuring.Native.MemoryRegion
