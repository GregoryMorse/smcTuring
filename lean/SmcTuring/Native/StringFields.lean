module
public import SmcTuring.Native.StringCursor

public section
namespace SmcTuring.Native.StringFields
open ByteMemory Execution

/-- A source/template and destination/template do not intersect the two complete
cursor words. These static byte ranges justify keeping cursor fields separate
from the MOVS data; source/destination and cursor pairs are also disjoint. -/
structure Layout where
  source : Nat
  destination : Nat
  size : Nat
  sourceField : Nat
  destinationField : Nat

@[expose] def Separate (mode : Mode) (layout : Layout) : Prop :=
  StringCopy.Apart layout.source layout.destination layout.size ∧
  StringCopy.Apart layout.sourceField layout.destinationField mode.wordBytes ∧
  (forall index : Fin layout.size, ¬Inside layout.sourceField mode.wordBytes (layout.source + index.val)) ∧
  (forall index : Fin layout.size, ¬Inside layout.destinationField mode.wordBytes (layout.source + index.val)) ∧
  (forall index : Fin mode.wordBytes, ¬Inside layout.destination layout.size (layout.sourceField + index.val)) ∧
  (forall index : Fin mode.wordBytes, ¬Inside layout.destination layout.size (layout.destinationField + index.val))

@[expose] def prepared (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) : Memory :=
  putWord mode (putWord mode memory layout.sourceField si) layout.destinationField di
@[expose] def copied (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) : Memory :=
  putBytes (prepared mode layout memory si di) layout.destination
    (bytesAt (prepared mode layout memory si di) layout.source layout.size)
@[expose] def restored (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) : Memory :=
  putWord mode (putWord mode (copied mode layout memory si di) layout.sourceField
    (Protected.wordAt mode memory layout.sourceField)) layout.destinationField (Protected.wordAt mode memory layout.destinationField)

theorem prepared_source (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) :
    bytesAt (prepared mode layout memory si di) layout.source layout.size = bytesAt memory layout.source layout.size := by
  unfold prepared putWord
  rw [bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using separate.2.2.2.1),
    bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using separate.2.2.1)]

theorem copied_effect (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) :
    copied mode layout memory si di = putBytes (prepared mode layout memory si di) layout.destination (bytesAt memory layout.source layout.size) := by
  unfold copied
  rw [prepared_source mode layout memory si di separate]

theorem cursor_outside (mode : Mode) (layout : Layout) (separate : Separate mode layout) (index : Fin mode.wordBytes) :
    ¬Inside layout.destinationField mode.wordBytes (layout.sourceField + index.val) :=
  StringCopy.source_outside layout.sourceField layout.destinationField mode.wordBytes separate.2.1 index

/-- Commuting a template-byte store with a cursor-word store uses complete
byte footprints, not word alignment or an assumption that MOVS saved the data. -/
theorem copy_word_commute (mode : Mode) (memory : Memory) (destination field : Nat) (bytes : List LittleEndian.Byte) (value : Word mode)
    (separate : forall index : Fin mode.wordBytes, ¬Inside destination bytes.length (field + index.val)) :
    putWord mode (putBytes memory destination bytes) field value = putBytes (putWord mode memory field value) destination bytes := by
  apply Eq.symm
  apply Writes.put_bytes_commute
  intro position inside
  have within : Inside field mode.wordBytes position := by simpa using inside
  have small : position - field < mode.wordBytes := by rcases within with ⟨_,_⟩; omega
  have kept := separate ⟨position-field,small⟩
  simpa [Nat.add_sub_of_le within.1] using kept

theorem restored_fields (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) :
    putWord mode (putWord mode (prepared mode layout memory si di) layout.sourceField (Protected.wordAt mode memory layout.sourceField))
      layout.destinationField (Protected.wordAt mode memory layout.destinationField) = memory := by
  unfold prepared
  rw [Writes.put_words_commute mode _ layout.destinationField layout.sourceField _ _ (by
    intro index
    have small := index.isLt
    have apart := separate.2.1
    unfold StringCopy.Apart at apart
    unfold Inside
    rcases apart with left | right <;> omega), Writes.put_word_overwrite]
  have sourceBack : putWord mode memory layout.sourceField (Protected.wordAt mode memory layout.sourceField) = memory := by
    unfold putWord
    rw [Protected.word_at_encoded]
    exact Writes.put_bytes_back memory layout.sourceField mode.wordBytes
  have destinationBack : putWord mode memory layout.destinationField (Protected.wordAt mode memory layout.destinationField) = memory := by
    unfold putWord
    rw [Protected.word_at_encoded]
    exact Writes.put_bytes_back memory layout.destinationField mode.wordBytes
  rw [Writes.put_word_overwrite mode memory layout.sourceField si (Protected.wordAt mode memory layout.sourceField), sourceBack, destinationBack]


/-- Full byte memory after saving index values, MOVS and restoring both declared
cursor fields equals only the intended original-source-to-destination store. -/
theorem effect (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) :
    restored mode layout memory si di = putBytes memory layout.destination (bytesAt memory layout.source layout.size) := by
  unfold restored
  rw [copied_effect mode layout memory si di separate,
    copy_word_commute mode _ _ _ _ _ (by simpa only [bytes_at_length] using separate.2.2.2.2.1),
    copy_word_commute mode _ _ _ _ _ (by simpa only [bytes_at_length] using separate.2.2.2.2.2),
    restored_fields mode layout memory si di separate]

theorem destination_value (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) :
    bytesAt (restored mode layout memory si di) layout.destination layout.size = bytesAt memory layout.source layout.size := by
  rw [effect mode layout memory si di separate]
  simpa only [bytes_at_length] using bytes_at_put memory layout.destination (bytesAt memory layout.source layout.size)

theorem frame (mode : Mode) (layout : Layout) (memory : Memory) (si di : Word mode) (separate : Separate mode layout) (position : Nat)
    (outside : ¬Inside layout.destination layout.size position) : restored mode layout memory si di position = memory position := by
  rw [effect mode layout memory si di separate]
  exact put_frame _ _ _ _ (by simpa using outside)

end SmcTuring.Native.StringFields
