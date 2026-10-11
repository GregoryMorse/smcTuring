module
public import SmcTuring.Appendix.MultiplyPackets
public import SmcTuring.Appendix.MultiplyRegions

public section
namespace SmcTuring.Appendix.MultiplyLayout

open MultiplyImage MultiplyByteCode
abbrev Placement := MultiplyPackets.Placement
abbrev Instruction := MultiplyWords.Instruction

/-- Exactly the data instructions with a current own-immediate read own +6.
The source operand of AND/XOR/ADD/copy and each SELF word will be linked to this
real field by the computed placement, rather than a future execution premise. -/
@[expose] def dataPacket : Instruction → Packet
  | .selected (.andField field _) => .common (.immediate .bitAnd (FieldRefinement.address field) 0x80000000)
  | .selected (.xorField field _) => .common (.immediate .bitXor (FieldRefinement.address field) 0x80000000)
  | .selfStore field => .common (.immediate .store (FieldRefinement.address field) 0x80000000)
  | .copyFrom field _ => .common (.immediate .store (FieldRefinement.address field) 0x80000000)
  | .addFrom field _ => .addImmediate (FieldRefinement.address field) 0x80000000
  | instruction => .fixed (MultiplyPackets.literal instruction (fun _ => 0x80000000))

@[expose] def dataPackets (place : Placement) (block : MultiplyBlocks.Block) : List Packet :=
  (MultiplyBlocks.words (MultiplyPackets.layout place) block).map dataPacket

@[expose] def tailPackets (place : Placement) (displacement : Word) (mutable : Bool) : List Packet :=
  [.fixed (.common (.memory .exchangeStack (FieldRefinement.address (place.stackInstruction + 6)))),
   if mutable then .common (.relative displacement) else .fixed (.common (.callRelative displacement))]

@[expose] def restorePackets (place : Placement) : List Packet :=
  (MultiplyPackets.restoreForms place).map Packet.fixed

@[expose] def purePackets (place : Placement) : List Packet :=
  dataPackets place .initial ++ tailPackets place 0 false ++ restorePackets place ++
    dataPackets place .guard ++ tailPackets place 0 true ++ restorePackets place ++
    dataPackets place .body ++ tailPackets place (MultiplyBlocks.backDelta (MultiplyPackets.layout place)) false ++
    restorePackets place ++ dataPackets place .finish

@[expose] def regions (place : Placement) (x y : Word) : List MultiplyRegions.Region :=
  [⟨place.origin, purePackets place⟩,
   ⟨place.inputX, [.common (.immediate .store (FieldRefinement.address (place.inputX + 6)) x)]⟩,
   ⟨place.inputY, [.common (.immediate .store (FieldRefinement.address (place.inputY + 6)) y)]⟩,
   ⟨place.result, [.common (.immediate .store (FieldRefinement.address (place.result + 6)) 0)]⟩,
   ⟨place.stackInstruction, [.common (.both .store
     (FieldRefinement.address (place.stackInstruction + 6))
     (FieldRefinement.address (place.stackInstruction + 6)))]⟩]

@[expose] def entries (place : Placement) (x y : Word) : List Entry :=
  MultiplyRegions.entries (regions place x y)

/-- The printed order permits arbitrary host gaps. All five complete regions
and their DWORD owners fit before the fixed x86 capacity bound. -/
structure Admissible (place : Placement) : Prop where
  pureBefore : place.origin + 382 ≤ place.inputX
  xBefore : place.inputX + 10 ≤ place.inputY
  yBefore : place.inputY + 10 ≤ place.result
  resultBefore : place.result + 10 ≤ place.stackInstruction
  capacity : place.stackInstruction + 10 ≤ 2 ^ 32

@[expose] def ownedFields (place : Placement) : List Nat :=
  [place.origin + 136, place.origin + 146, place.origin + 157,
   place.origin + 252, place.origin + 275, place.origin + 285,
   place.origin + 295, place.origin + 311, place.origin + 378,
   place.inputX + 6, place.inputY + 6, place.result + 6,
   place.stackInstruction + 2, place.stackInstruction + 6]

theorem data_initial (instruction : Instruction) :
    (dataPacket instruction).initial = MultiplyPackets.literal instruction (fun _ => 0x80000000) := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | _ => rfl

theorem data_initials (place : Placement) (block : MultiplyBlocks.Block) :
    (dataPackets place block).map Packet.initial = MultiplyPackets.dataForms place block := by
  simp only [dataPackets, MultiplyPackets.dataForms, List.map_map, Function.comp_def, data_initial]

theorem tail_initials (place : Placement) (displacement : Word) (mutable : Bool) :
    (tailPackets place displacement mutable).map Packet.initial = MultiplyPackets.tailForms place displacement := by
  cases mutable <;> rfl

theorem restore_initials (place : Placement) :
    (restorePackets place).map Packet.initial = MultiplyPackets.restoreForms place := rfl

theorem pure_initials (place : Placement) :
    (purePackets place).map Packet.initial = MultiplyPackets.packets place := by
  simp only [purePackets, MultiplyPackets.packets, List.map_append, data_initials, tail_initials, restore_initials]

theorem pure_size (place : Placement) : MultiplyPacking.size (purePackets place) = 382 := by
  unfold MultiplyPacking.size
  have lengths : (purePackets place).map (fun packet => (encode packet.initial).length) =
      ((purePackets place).map Packet.initial).map instructionLength := by
    simp only [List.map_map, Function.comp_def, encode_length]
  rw [lengths, pure_initials]
  exact MultiplyPackets.packet_span place

theorem data_size (place : Placement) (block : MultiplyBlocks.Block) :
    MultiplyPacking.size (dataPackets place block) = match block with
      | .initial => 44 | .guard => 65 | .body => 130 | .finish => 20 := by
  have lengths : MultiplyPacking.size (dataPackets place block) =
      (((dataPackets place block).map Packet.initial).map instructionLength).sum := by
    simp only [MultiplyPacking.size, List.map_map, Function.comp_def, encode_length]
  rw [lengths, data_initials, MultiplyPackets.data_lengths_block]
  cases block <;> rfl

theorem tail_size (place : Placement) (displacement : Word) (mutable : Bool) :
    MultiplyPacking.size (tailPackets place displacement mutable) = 11 := by
  cases mutable <;> rfl

theorem restore_size (place : Placement) : MultiplyPacking.size (restorePackets place) = 30 := rfl

theorem data_fields (place : Placement) (block : MultiplyBlocks.Block) (start : Nat) :
    MultiplyPacking.fields (MultiplyPacking.place start (dataPackets place block)) = match block with
      | .initial => []
      | .guard => [start + 51, start + 61]
      | .body => [start + 61, start + 84, start + 94, start + 104, start + 120]
      | .finish => [start + 16] := by
  cases block <;> simp only [dataPackets, MultiplyBlocks.words, MultiplyWords.initialProgram,
    MultiplyWords.copyProgram, MultiplyWords.guard, MultiplyWords.body, MultiplyWords.finish,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    MultiplyPacking.place, MultiplyPacking.fields, List.flatMap_cons, List.flatMap_nil,
    dataPacket, Packet.initial, ByteImage.Packet.initial, encode_length, instructionLength,
    MultiplyPackets.literal, ByteCode.instructionLength, ByteCode.MemoryOp.trailer,
    Entry.fields, Packet.offsets, ByteImage.Packet.offsets, List.length_cons, List.length_nil,
    Nat.add_assoc, Nat.reduceAdd, List.append_nil]

theorem tail_fields (place : Placement) (displacement : Word) (mutable : Bool) (start : Nat) :
    MultiplyPacking.fields (MultiplyPacking.place start (tailPackets place displacement mutable)) =
      if mutable then [start + 7] else [] := by
  cases mutable <;> simp only [tailPackets, Bool.false_eq_true, ite_false, ite_true,
    MultiplyPacking.place, MultiplyPacking.fields, List.flatMap_cons, List.flatMap_nil,
    Packet.initial, encode_length, instructionLength,
    ByteCode.instructionLength, ByteCode.MemoryOp.trailer, Entry.fields, Packet.offsets,
    ByteImage.Packet.offsets, List.map_cons, List.map_nil, List.length_nil, Nat.add_assoc,
    Nat.reduceAdd, List.nil_append, List.append_nil]

theorem restore_fields (place : Placement) (start : Nat) :
    MultiplyPacking.fields (MultiplyPacking.place start (restorePackets place)) = [] := by
  simp only [restorePackets, MultiplyPackets.restoreForms, ByteControl.restoreForms,
    List.map_cons, List.map_nil, MultiplyPacking.place, MultiplyPacking.fields,
    List.flatMap_cons, List.flatMap_nil, Entry.fields, Packet.offsets, List.nil_append]

theorem ordered (place : Placement) (x y : Word) (valid : Admissible place) :
    MultiplyRegions.Ordered (regions place x y) := by
  rcases valid with ⟨h0,h1,h2,h3,_⟩
  unfold MultiplyRegions.Ordered regions
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))))
  · intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp only [MultiplyRegions.Region.finish, pure_size]
    all_goals omega
  · intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals change place.inputX + 10 ≤ _
    all_goals try dsimp only
    all_goals omega
  · intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals change place.inputY + 10 ≤ _
    all_goals try dsimp only
    all_goals omega
  · intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst region
    change place.result + 10 ≤ place.stackInstruction
    exact h3
  · intro region member
    simp only [List.not_mem_nil] at member

theorem capacity (place : Placement) (x y : Word) (valid : Admissible place) :
    ∀ region ∈ regions place x y, region.finish ≤ 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  intro region member
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [MultiplyRegions.Region.finish, pure_size]
  all_goals simp [MultiplyPacking.size, Packet.initial, ByteImage.Packet.initial, encode_length, instructionLength, ByteCode.instructionLength]
  all_goals omega

theorem separated (place : Placement) (x y : Word) (valid : Admissible place) :
    Separated (entries place x y) := MultiplyRegions.separated _ (ordered place x y valid)

theorem field_layout (place : Placement) (x y : Word) (valid : Admissible place) :
    FieldRefinement.Layout (MultiplyPacking.fields (entries place x y)) :=
  MultiplyRegions.field_layout _ (ordered place x y valid) (capacity place x y valid)

theorem initial_intact (place : Placement) (x y : Word) (backing : Native.ByteMemory.Memory) (valid : Admissible place) :
    Intact (entries place x y) (image (entries place x y) backing) :=
  MultiplyRegions.initial_intact _ backing (ordered place x y valid)

theorem initial_fetch (place : Placement) (x y : Word) (backing : Native.ByteMemory.Memory) (valid : Admissible place)
    (entry : Entry) (member : entry ∈ entries place x y) :
    fetch (image (entries place x y) backing) entry.pc =
      some (current entry (image (entries place x y) backing)) :=
  fetch_current entry _ (initial_intact place x y backing valid entry member)

theorem pure_fields (place : Placement) :
    MultiplyPacking.fields (MultiplyPacking.place place.origin (purePackets place)) =
      [place.origin + 136, place.origin + 146, place.origin + 157,
       place.origin + 252, place.origin + 275, place.origin + 285,
       place.origin + 295, place.origin + 311, place.origin + 378] := by
  simp only [purePackets, MultiplyPacking.place_append, MultiplyPacking.fields_append,
    MultiplyPacking.size_append, data_size, tail_size, restore_size, data_fields, tail_fields,
    restore_fields, Bool.false_eq_true, ite_true, ite_false, List.nil_append, List.cons_append,
    List.append_nil, Nat.add_assoc, Nat.reduceAdd]

theorem image_fields (place : Placement) (x y : Word) :
    MultiplyPacking.fields (entries place x y) = ownedFields place := by
  simp only [entries, regions, MultiplyRegions.entries, MultiplyRegions.Region.entries,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, MultiplyPacking.fields_append, pure_fields]
  simp only [MultiplyPacking.place, MultiplyPacking.fields, Entry.fields, Packet.offsets,
    ByteImage.Packet.offsets, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, ownedFields]

theorem slot_owned (place : Placement) (x y : Word) (slot : MultiplyWords.Slot) :
    Owned (entries place x y) (MultiplyPackets.fields place slot) := by
  apply (MultiplyPacking.fields_owned _ _).mp
  rw [image_fields]
  cases slot <;> simp [ownedFields, MultiplyPackets.fields]

theorem pointer_owned (place : Placement) (x y : Word) :
    Owned (entries place x y) (place.stackInstruction + 6) := by
  apply (MultiplyPacking.fields_owned _ _).mp
  rw [image_fields]
  simp [ownedFields]

theorem address_owned (place : Placement) (x y : Word) :
    Owned (entries place x y) (place.stackInstruction + 2) := by
  apply (MultiplyPacking.fields_owned _ _).mp
  rw [image_fields]
  simp [ownedFields]

theorem slot_fits (place : Placement) (x y : Word) (valid : Admissible place) (slot : MultiplyWords.Slot) :
    MultiplyPackets.fields place slot + 4 ≤ 2 ^ 32 :=
  (field_layout place x y valid).fits _ ((MultiplyPacking.fields_owned _ _).mpr (slot_owned place x y slot))

theorem owned_patch_intact (place : Placement) (x y : Word) (valid : Admissible place)
    (memory : Native.ByteMemory.Memory) (intact : Intact (entries place x y) memory)
    (slot : MultiplyWords.Slot) (value : Word) :
    Intact (entries place x y) (Native.ByteMemory.putWord .x86 memory (MultiplyPackets.fields place slot) value) :=
  store_intact _ memory (separated place x y valid) intact _ value (slot_owned place x y slot)

end SmcTuring.Appendix.MultiplyLayout
