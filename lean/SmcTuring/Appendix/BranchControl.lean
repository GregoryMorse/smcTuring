module
public import SmcTuring.Appendix.BranchPrefix
public import SmcTuring.Appendix.ByteControl
public import SmcTuring.Appendix.ByteLinear

public section

namespace SmcTuring.Appendix.BranchControl

open ByteImage BranchLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation
@[expose] def pointer (base : Nat) : ByteControl.Word := FieldRefinement.address (base + 6)
@[expose] def address (base : Nat) : ByteControl.Word := FieldRefinement.address (base + 2)
@[expose] def displacement (base : Nat) (signed : Bool) (relation : Relation) : ByteControl.Word :=
  FieldRefinement.address (fields base signed relation).displacement

theorem full_layout (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) : FieldRefinement.Layout (ownedFields base signed relation) := by
  have layout := BytePacking.placed_field_layout (packets base signed relation x y) base
    ((image_end base signed relation x y).trans_le capacity)
  change FieldRefinement.Layout (BytePacking.fields (entries base signed relation x y)) at layout
  rw [image_fields] at layout
  exact layout

theorem field_owned (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (field : Nat) (member : field ∈ ownedFields base signed relation) : Owned (entries base signed relation x y) field := by
  apply (BytePacking.fields_owned _ field).mp
  rwa [image_fields]

theorem slot_apart (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) : ByteControl.Apart (pointer base) (address base) := by
  have layout := full_layout base signed relation x y capacity
  have pMember : base + 6 ∈ ownedFields base signed relation := by simp [ownedFields]
  have aMember : base + 2 ∈ ownedFields base signed relation := by simp [ownedFields]
  intro index
  exact FieldRefinement.layout_outside layout (base + 2) (base + 6) aMember pMember (by omega) index

theorem call_apart (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) : ByteControl.Apart (displacement base signed relation) (pointer base) := by
  have layout := full_layout base signed relation x y capacity
  have pMember : base + 6 ∈ ownedFields base signed relation := by simp [ownedFields]
  have cMember : (fields base signed relation).displacement ∈ ownedFields base signed relation := by simp [ownedFields]
  intro index
  exact FieldRefinement.layout_outside layout (base + 6) (fields base signed relation).displacement pMember cMember (by
      simp only [fields, callPC, prefixEnd, andPC, prefixStart]
      omega) index

theorem slot_alias (base : Nat) : BitVec.sub (pointer base) 4 = address base := by
  have sum : pointer base = BitVec.add (address base) 4 := by
    change BitVec.ofNat 32 (base + 6) = BitVec.ofNat 32 (base + 2) + BitVec.ofNat 32 4
    rw [BitVec.ofNat_add_ofNat]
  rw [sum]
  exact BitVec.add_sub_cancel _ _

theorem pointer_nonwrap (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) : 4 ≤ (pointer base).toNat := by
  have fit := (full_layout base signed relation x y capacity).fits (base + 6) (by simp [ownedFields])
  change 4 ≤ (FieldRefinement.address (base + 6)).toNat
  rw [FieldRefinement.address_toNat _ fit]
  omega

theorem stack_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    (⟨base, BranchLayout.stack base⟩ : Entry) ∈ entries base signed relation x y := by
  simp only [entries, packets, BytePacking.place_append, List.mem_append]
  left; left; left; left; left
  simp [BytePacking.place]

theorem initial_stack (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    ByteControl.load state.memory (pointer base) = pointer base ∧
      ByteControl.load state.memory (address base) = pointer base := by
  have layout := full_layout base signed relation x y capacity
  have bytes := image_packet _ backing (BytePacking.placed_separated _ _) _ (stack_placed base signed relation x y)
  change Native.ByteMemory.bytesAt (image (entries base signed relation x y) backing) base
    (ByteCode.encode (.immediate .store (pointer base) (pointer base))).length =
    ByteCode.encode (.immediate .store (pointer base) (pointer base)) at bytes
  rw [←initial] at bytes
  have words := immediate_words _ _ _ _ _ bytes
  constructor
  · change FieldRefinement.readField state (base + 6) = pointer base
    rw [←word_at_read_field state (base + 6) (layout.fits _ (by simp [ownedFields]))]
    exact words.2
  · change FieldRefinement.readField state (base + 2) = pointer base
    rw [←word_at_read_field state (base + 2) (layout.fits _ (by simp [ownedFields]))]
    exact words.1

theorem prefix_load_frame (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32) (field : Nat)
    (before : field + 4 ≤ andPC base signed relation) (fit : field + 4 ≤ 2 ^ 32) :
    ByteControl.load (FieldRefinement.run (program base signed relation) state).memory (FieldRefinement.address field) =
      ByteControl.load state.memory (FieldRefinement.address field) := by
  change BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4)) =
    BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4))
  rw [FieldRefinement.address_toNat field fit]
  congr 1
  congr 1
  unfold Native.ByteMemory.bytesAt
  congr 1
  funext index
  apply BranchPrefix.byte_frame base signed relation x y state capacity
  intro scratch member
  have small := index.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [fields, xorPC, callPC, prefixEnd, Native.ByteMemory.Inside] <;> omega

theorem prefix_stack (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    ByteControl.load (FieldRefinement.run (program base signed relation) state).memory (pointer base) = pointer base ∧
      ByteControl.load (FieldRefinement.run (program base signed relation) state).memory (address base) = pointer base := by
  have layout := full_layout base signed relation x y capacity
  have leadingBound : 61 ≤ leading signed relation := by unfold leading; omega
  have pFrame := prefix_load_frame base signed relation x y state capacity (base + 6)
    (by simp only [andPC, prefixStart]; omega) (layout.fits _ (by simp [ownedFields]))
  have aFrame := prefix_load_frame base signed relation x y state capacity (base + 2)
    (by simp only [andPC, prefixStart]; omega) (layout.fits _ (by simp [ownedFields]))
  change _ = _ ∧ _ = _
  rw [show ByteControl.load (FieldRefinement.run (program base signed relation) state).memory (pointer base) =
    ByteControl.load state.memory (pointer base) from pFrame,
    show ByteControl.load (FieldRefinement.run (program base signed relation) state).memory (address base) =
    ByteControl.load state.memory (address base) from aFrame]
  exact initial_stack base signed relation x y backing state capacity initial

end SmcTuring.Appendix.BranchControl
