module
public import SmcTuring.Appendix.SpacedPrefix
public import SmcTuring.Appendix.ByteControl
public import SmcTuring.Appendix.ByteLinear

public section

namespace SmcTuring.Appendix.SpacedControl

open ByteImage SpacedLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation
@[expose] def pointer (sites : Sites) : ByteControl.Word := FieldRefinement.address (sites.stack + 6)
@[expose] def address (sites : Sites) : ByteControl.Word := FieldRefinement.address (sites.stack + 2)
@[expose] def displacement (sites : Sites) (signed : Bool) (relation : Relation) : ByteControl.Word :=
  FieldRefinement.address (fields sites signed relation).displacement

theorem slot_apart (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : ByteControl.Apart (pointer sites) (address sites) := by
  have layout := full_layout sites signed relation x y valid
  have pMember : sites.stack + 6 ∈ ownedFields sites signed relation := by simp [ownedFields]
  have aMember : sites.stack + 2 ∈ ownedFields sites signed relation := by simp [ownedFields]
  intro index
  exact FieldRefinement.layout_outside layout (sites.stack + 2) (sites.stack + 6) aMember pMember (by omega) index

theorem call_apart (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : ByteControl.Apart (displacement sites signed relation) (pointer sites) := by
  have layout := full_layout sites signed relation x y valid
  have pMember : sites.stack + 6 ∈ ownedFields sites signed relation := by simp [ownedFields]
  have apart := valid.stackCore
  have cMember : (fields sites signed relation).displacement ∈ ownedFields sites signed relation := by simp [ownedFields]
  intro index
  exact FieldRefinement.layout_outside layout (sites.stack + 6) (fields sites signed relation).displacement pMember cMember (by
      simp only [fields, callPC, prefixEnd, andPC, fallPC] at *
      omega) index

theorem slot_alias (sites : Sites) : BitVec.sub (pointer sites) 4 = address sites := by
  have sum : pointer sites = BitVec.add (address sites) 4 := by
    change BitVec.ofNat 32 (sites.stack + 6) = BitVec.ofNat 32 (sites.stack + 2) + BitVec.ofNat 32 4
    rw [BitVec.ofNat_add_ofNat]
  rw [sum]
  exact BitVec.add_sub_cancel _ _

theorem pointer_nonwrap (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : 4 ≤ (pointer sites).toNat := by
  have fit := (full_layout sites signed relation x y valid).fits (sites.stack + 6) (by simp [ownedFields])
  change 4 ≤ (FieldRefinement.address (sites.stack + 6)).toNat
  rw [FieldRefinement.address_toNat _ fit]
  omega

theorem initial_stack (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    ByteControl.load state.memory (pointer sites) = pointer sites ∧
      ByteControl.load state.memory (address sites) = pointer sites := by
  have layout := full_layout sites signed relation x y valid
  have bytes := image_packet _ backing (separated sites signed relation x y valid) _ (stack_placed sites signed relation x y)
  change Native.ByteMemory.bytesAt (image (entries sites signed relation x y) backing) sites.stack
    (ByteCode.encode (.immediate .store (pointer sites) (pointer sites))).length =
    ByteCode.encode (.immediate .store (pointer sites) (pointer sites)) at bytes
  rw [←initial] at bytes
  have words := immediate_words _ _ _ _ _ bytes
  constructor
  · change FieldRefinement.readField state (sites.stack + 6) = pointer sites
    rw [←word_at_read_field state (sites.stack + 6) (layout.fits _ (by simp [ownedFields]))]
    exact words.2
  · change FieldRefinement.readField state (sites.stack + 2) = pointer sites
    rw [←word_at_read_field state (sites.stack + 2) (layout.fits _ (by simp [ownedFields]))]
    exact words.1

theorem prefix_load_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (valid : Valid sites signed relation) (field : Nat)
    (before : field + 4 ≤ andPC sites signed relation) (fit : field + 4 ≤ 2 ^ 32) :
    ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (FieldRefinement.address field) =
      ByteControl.load state.memory (FieldRefinement.address field) := by
  change BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4)) =
    BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4))
  rw [FieldRefinement.address_toNat field fit]
  congr 1
  congr 1
  unfold Native.ByteMemory.bytesAt
  congr 1
  funext index
  apply SpacedPrefix.byte_frame sites signed relation x y state valid
  intro scratch member
  have small := index.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [fields, xorPC, callPC, prefixEnd, Native.ByteMemory.Inside] <;> omega

/-- Complete metadata words may lie before or after the branch core.
The actual prefix restores all byte windows outside its three scratch fields. -/
theorem prefix_disjoint_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (valid : Valid sites signed relation) (field : Nat)
    (apart : field + 4 ≤ sites.start ∨ fallPC sites signed relation + 30 ≤ field)
    (fit : field + 4 ≤ 2 ^ 32) :
    ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (FieldRefinement.address field) =
      ByteControl.load state.memory (FieldRefinement.address field) := by
  change BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4)) =
    BitVec.ofNat 32 (Native.LittleEndian.pack (Native.ByteMemory.bytesAt _ (FieldRefinement.address field).toNat 4))
  rw [FieldRefinement.address_toNat field fit]
  congr 1
  congr 1
  unfold Native.ByteMemory.bytesAt
  congr 1
  funext index
  apply SpacedPrefix.byte_frame sites signed relation x y state valid
  intro scratch member
  have small := index.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [fields, xorPC, callPC, prefixEnd, andPC, fallPC, Native.ByteMemory.Inside] at * <;> omega

theorem prefix_stack (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (pointer sites) = pointer sites ∧
      ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (address sites) = pointer sites := by
  have layout := full_layout sites signed relation x y valid
  have apart := valid.stackCore
  have pFrame := prefix_disjoint_frame sites signed relation x y state valid (sites.stack + 6)
    (by omega) (layout.fits _ (by simp [ownedFields]))
  have aFrame := prefix_disjoint_frame sites signed relation x y state valid (sites.stack + 2)
    (by omega) (layout.fits _ (by simp [ownedFields]))
  change _ = _ ∧ _ = _
  rw [show ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (pointer sites) =
    ByteControl.load state.memory (pointer sites) from pFrame,
    show ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory (address sites) =
    ByteControl.load state.memory (address sites) from aFrame]
  exact initial_stack sites signed relation x y backing state valid initial

end SmcTuring.Appendix.SpacedControl
