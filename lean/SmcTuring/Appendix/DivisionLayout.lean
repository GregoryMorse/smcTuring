module
public import SmcTuring.Appendix.DivisionPackets
public import SmcTuring.Appendix.DivisionRegions
public import SmcTuring.Appendix.MultiplyLayout

public section
namespace SmcTuring.Appendix.DivisionLayout

open DivisionImage DivisionByteCode
abbrev Placement := DivisionPackets.Placement
abbrev Instruction := DivisionWords.Instruction

/-- Original own-immediate packets. Extra SUB fields own the full imm32;
fixed instructions retain their complete opcode/address/count bytes. -/
@[expose] def dataPacket : Instruction → Packet
  | .simple instruction => .common (MultiplyLayout.dataPacket instruction)
  | .subtractFrom field _ => .subtractImmediate (FieldRefinement.address field) 0x80000000
  | instruction => .fixed (DivisionPackets.literal instruction (fun _ => 0x80000000))

@[expose] def dataPackets (place : Placement) (block : DivisionBlocks.Block) : List Packet :=
  (DivisionBlocks.words (DivisionPackets.layout place) block).map dataPacket

@[expose] def tailPackets (place : Placement) (displacement : Word) (mutable : Bool) : List Packet :=
  [.fixed (.common (.common (.memory .exchangeStack (FieldRefinement.address (place.stackInstruction + 6))))),
   if mutable then .common (.common (.relative displacement)) else .fixed (.common (.common (.callRelative displacement)))]

@[expose] def restorePackets (place : Placement) : List Packet :=
  (DivisionPackets.restoreForms place).map Packet.fixed

@[expose] def purePackets (place : Placement) : List Packet :=
  dataPackets place .initial ++ tailPackets place 0 false ++ restorePackets place ++
    dataPackets place .guard ++ tailPackets place 0 true ++ restorePackets place ++
    dataPackets place .body ++ tailPackets place (DivisionBlocks.backDelta (DivisionPackets.layout place)) false ++
    restorePackets place ++ dataPackets place .finish

@[expose] def regions (place : Placement) (x y : Word) : List DivisionRegions.Region :=
  [⟨place.origin, purePackets place⟩,
   ⟨place.inputX, [.common (.common (.immediate .store (FieldRefinement.address (place.inputX + 6)) x))]⟩,
   ⟨place.inputY, [.common (.common (.immediate .store (FieldRefinement.address (place.inputY + 6)) y))]⟩,
   ⟨place.result, [.common (.common (.immediate .store (FieldRefinement.address (place.result + 6)) 0))]⟩,
   ⟨place.stackInstruction, [.common (.common (.both .store
     (FieldRefinement.address (place.stackInstruction + 6))
     (FieldRefinement.address (place.stackInstruction + 6))))]⟩]

@[expose] def entries (place : Placement) (x y : Word) : List Entry :=
  DivisionRegions.entries (regions place x y)

@[expose] def pureSpan (place : Placement) : Nat :=
  DivisionPackets.initialSpan place + 365 + if place.signed then 73 else 30

/-- Five complete original regions fit the x86 capacity. Host gaps may be
arbitrary. Unused logical slots are distinct scratch-free view coordinates. -/
structure Admissible (place : Placement) : Prop where
  pureBefore : place.origin + pureSpan place ≤ place.inputX
  xBefore : place.inputX + 10 ≤ place.inputY
  yBefore : place.inputY + 10 ≤ place.result
  resultBefore : place.result + 10 ≤ place.stackInstruction
  capacity : place.stackInstruction + 10 ≤ 2 ^ 32
  unusedAfter : place.stackInstruction + 10 ≤ place.unused

@[expose] def initialOffsets (place : Placement) : List Nat :=
  if place.signed then
    (if place.mod then [47,128,138,219,229,276] else [62,85,166,176,257,267,314])
  else [65]

@[expose] def pureOffsets (place : Placement) : List Nat :=
  initialOffsets place ++
    [92,102,113,197,214,224,244,261,294,304,314,381,391].map (DivisionPackets.initialSpan place + ·) ++
    (if place.signed then [424,434].map (DivisionPackets.initialSpan place + ·) else [])

@[expose] def ownedFields (place : Placement) : List Nat :=
  (pureOffsets place).map (place.origin + ·) ++
    [place.inputX + 6, place.inputY + 6, place.result + 6,
     place.stackInstruction + 2, place.stackInstruction + 6]

@[expose] def ActiveSlot (place : Placement) : DivisionWords.Slot → Prop
  | .signY => place.signed = true ∧ place.mod = false
  | .signX | .resultSign | .xMask | .xDouble | .yMask | .yDouble | .outputDouble => place.signed = true
  | _ => True

theorem data_initial (instruction : Instruction) :
    (dataPacket instruction).initial = DivisionPackets.literal instruction (fun _ => 0x80000000) := by
  cases instruction with
  | simple instruction => exact congrArg Form.common (MultiplyLayout.data_initial instruction)
  | _ => rfl

theorem data_initials (place : Placement) (block : DivisionBlocks.Block) :
    (dataPackets place block).map Packet.initial = DivisionPackets.dataForms place block := by
  simp only [dataPackets, DivisionPackets.dataForms, List.map_map, Function.comp_def, data_initial]

theorem tail_initials (place : Placement) (displacement : Word) (mutable : Bool) :
    (tailPackets place displacement mutable).map Packet.initial = DivisionPackets.tailForms place displacement := by
  cases mutable <;> rfl

theorem restore_initials (place : Placement) :
    (restorePackets place).map Packet.initial = DivisionPackets.restoreForms place := rfl

theorem pure_initials (place : Placement) :
    (purePackets place).map Packet.initial = DivisionPackets.packets place := by
  simp only [purePackets, DivisionPackets.packets, List.map_append, data_initials, tail_initials, restore_initials]

theorem pure_size (place : Placement) : DivisionPacking.size (purePackets place) = pureSpan place := by
  unfold DivisionPacking.size
  have lengths : (purePackets place).map (fun packet => (encode packet.initial).length) =
      ((purePackets place).map Packet.initial).map instructionLength := by
    simp only [List.map_map, Function.comp_def, encode_length]
  rw [lengths, pure_initials]
  exact DivisionPackets.packet_span place

theorem data_size (place : Placement) (block : DivisionBlocks.Block) :
    DivisionPacking.size (dataPackets place block) = match block with
      | .initial => DivisionPackets.initialSpan place | .guard => 65 | .body => 177
      | .finish => if place.signed then 73 else 30 := by
  have lengths : DivisionPacking.size (dataPackets place block) =
      (((dataPackets place block).map Packet.initial).map instructionLength).sum := by
    simp only [DivisionPacking.size, List.map_map, Function.comp_def, encode_length]
  rw [lengths, data_initials]
  have size := DivisionPackets.data_span place block
  change DivisionPackets.span (DivisionPackets.dataForms place block) = _
  rw [size]
  have stages := DivisionBlocks.literal_lengths (DivisionPackets.layout place)
  cases block with
  | initial => exact stages.1
  | guard => exact stages.2.1
  | body => exact stages.2.2.1
  | finish => exact stages.2.2.2

theorem tail_size (place : Placement) (displacement : Word) (mutable : Bool) :
    DivisionPacking.size (tailPackets place displacement mutable) = 11 := by
  cases mutable <;> rfl

theorem restore_size (place : Placement) : DivisionPacking.size (restorePackets place) = 30 := rfl

theorem data_fields (place : Placement) (block : DivisionBlocks.Block) (start : Nat) :
    DivisionPacking.fields (DivisionPacking.place start (dataPackets place block)) = match block with
      | .initial => (initialOffsets place).map (start + ·)
      | .guard => [start + 51, start + 61]
      | .body => [start+50,start+67,start+77,start+97,start+114,start+147,start+157,start+167]
      | .finish => [start+16,start+26] ++ (if place.signed then [start+59,start+69] else []) := by
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp [dataPackets, DivisionBlocks.words, DivisionPackets.layout, DivisionWords.initializeData,
      DivisionWords.signPrefix, DivisionWords.sample, DivisionWords.normalize, DivisionWords.copy,
      MultiplyWords.copyProgram, DivisionGuard.program, MultiplyWords.guard, DivisionGuard.guardFields,
      DivisionGuard.binding, DivisionWords.body, DivisionWords.finishData, DivisionWords.selected,
      DivisionPacking.place, DivisionPacking.fields, dataPacket, MultiplyLayout.dataPacket,
      Packet.initial, MultiplyImage.Packet.initial, MultiplyImage.Packet.initial, ByteImage.Packet.initial, encode_length,
      instructionLength, MultiplyByteCode.instructionLength, DivisionPackets.literal, MultiplyPackets.literal,
      MultiplyByteCode.instructionLength, ByteCode.instructionLength, ByteCode.MemoryOp.trailer, Entry.fields, Packet.offsets,
      MultiplyImage.Packet.offsets, ByteImage.Packet.offsets, Nat.add_assoc, initialOffsets, signed, mod]

theorem tail_fields (place : Placement) (displacement : Word) (mutable : Bool) (start : Nat) :
    DivisionPacking.fields (DivisionPacking.place start (tailPackets place displacement mutable)) =
      if mutable then [start + 7] else [] := by
  cases mutable <;> simp only [tailPackets, Bool.false_eq_true, ite_false, ite_true,
    DivisionPacking.place, DivisionPacking.fields, List.flatMap_cons, List.flatMap_nil,
    Packet.initial, encode_length, instructionLength,
    MultiplyByteCode.instructionLength, ByteCode.instructionLength, ByteCode.MemoryOp.trailer, Entry.fields, Packet.offsets,
    MultiplyImage.Packet.offsets, ByteImage.Packet.offsets, List.map_cons, List.map_nil, List.length_nil, Nat.add_assoc,
    Nat.reduceAdd, List.nil_append, List.append_nil]

theorem restore_fields (place : Placement) (start : Nat) :
    DivisionPacking.fields (DivisionPacking.place start (restorePackets place)) = [] := by
  simp only [restorePackets, DivisionPackets.restoreForms, ByteControl.restoreForms,
    List.map_cons, List.map_nil, DivisionPacking.place, DivisionPacking.fields,
    List.flatMap_cons, List.flatMap_nil, Entry.fields, Packet.offsets, List.nil_append]

theorem ordered (place : Placement) (x y : Word) (valid : Admissible place) :
    DivisionRegions.Ordered (regions place x y) := by
  rcases valid with ⟨h0,h1,h2,h3,_,_⟩
  unfold DivisionRegions.Ordered regions
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))))
  · intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp only [DivisionRegions.Region.finish, pure_size]
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
  rcases valid with ⟨h0,h1,h2,h3,h4,_⟩
  intro region member
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [DivisionRegions.Region.finish, pure_size]
  all_goals simp [DivisionPacking.size, Packet.initial, MultiplyImage.Packet.initial, ByteImage.Packet.initial, encode_length, instructionLength, MultiplyByteCode.instructionLength, ByteCode.instructionLength]
  all_goals omega

theorem separated (place : Placement) (x y : Word) (valid : Admissible place) :
    Separated (entries place x y) := DivisionRegions.separated _ (ordered place x y valid)

theorem field_layout (place : Placement) (x y : Word) (valid : Admissible place) :
    FieldRefinement.Layout (DivisionPacking.fields (entries place x y)) :=
  DivisionRegions.field_layout _ (ordered place x y valid) (capacity place x y valid)

theorem initial_intact (place : Placement) (x y : Word) (backing : Native.ByteMemory.Memory) (valid : Admissible place) :
    Intact (entries place x y) (image (entries place x y) backing) :=
  DivisionRegions.initial_intact _ backing (ordered place x y valid)

theorem initial_fetch (place : Placement) (x y : Word) (backing : Native.ByteMemory.Memory) (valid : Admissible place)
    (entry : Entry) (member : entry ∈ entries place x y) :
    fetch (image (entries place x y) backing) entry.pc =
      some (current entry (image (entries place x y) backing)) :=
  fetch_current entry _ (initial_intact place x y backing valid entry member)

theorem pure_fields (place : Placement) :
    DivisionPacking.fields (DivisionPacking.place place.origin (purePackets place)) =
      (pureOffsets place).map (place.origin + ·) := by
  simp only [purePackets, DivisionPacking.place_append, DivisionPacking.fields_append,
    DivisionPacking.size_append, data_size, tail_size, restore_size, data_fields, tail_fields,
    restore_fields, Bool.false_eq_true, ite_true, ite_false]
  cases signed : place.signed <;> cases mod : place.mod <;>
    simp [pureOffsets, initialOffsets, DivisionPackets.initialSpan, signed, mod, Nat.add_assoc]

theorem image_fields (place : Placement) (x y : Word) :
    DivisionPacking.fields (entries place x y) = ownedFields place := by
  simp only [entries, regions, DivisionRegions.entries, DivisionRegions.Region.entries,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, DivisionPacking.fields_append, pure_fields]
  simp only [DivisionPacking.place, DivisionPacking.fields, Entry.fields, Packet.offsets,
    MultiplyImage.Packet.offsets, ByteImage.Packet.offsets, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, ownedFields]

theorem slot_owned (place : Placement) (x y : Word) (slot : DivisionWords.Slot)
    (active : ActiveSlot place slot) :
    Owned (entries place x y) (DivisionPackets.fields place slot) := by
  apply (DivisionPacking.fields_owned _ _).mp
  rw [image_fields]
  cases signed : place.signed <;> cases mod : place.mod <;> cases slot <;>
    simp_all [ownedFields, pureOffsets, initialOffsets, ActiveSlot, DivisionPackets.fields,
      DivisionPackets.initialSpan, DivisionPackets.signSpan, Nat.add_assoc, Nat.add_sub_assoc]

theorem pointer_owned (place : Placement) (x y : Word) :
    Owned (entries place x y) (place.stackInstruction + 6) := by
  apply (DivisionPacking.fields_owned _ _).mp
  rw [image_fields]
  simp [ownedFields]

theorem address_owned (place : Placement) (x y : Word) :
    Owned (entries place x y) (place.stackInstruction + 2) := by
  apply (DivisionPacking.fields_owned _ _).mp
  rw [image_fields]
  simp [ownedFields]

theorem slot_fits (place : Placement) (x y : Word) (valid : Admissible place) (slot : DivisionWords.Slot) (active : ActiveSlot place slot) :
    DivisionPackets.fields place slot + 4 ≤ 2 ^ 32 :=
  (field_layout place x y valid).fits _ ((DivisionPacking.fields_owned _ _).mpr (slot_owned place x y slot active))

theorem owned_patch_intact (place : Placement) (x y : Word) (valid : Admissible place)
    (memory : Native.ByteMemory.Memory) (intact : Intact (entries place x y) memory)
    (slot : DivisionWords.Slot) (active : ActiveSlot place slot) (value : Word) :
    Intact (entries place x y) (Native.ByteMemory.putWord .x86 memory (DivisionPackets.fields place slot) value) :=
  store_intact _ memory (separated place x y valid) intact _ value (slot_owned place x y slot active)

theorem written_active (place : Placement) (block : DivisionBlocks.Block) (slot : DivisionWords.Slot)
    (written : slot ∈ DivisionBlocks.written (DivisionPackets.layout place) block) :
    ActiveSlot place slot := by
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;> cases slot <;>
    simp_all [ActiveSlot, DivisionBlocks.written, DivisionPackets.layout,
      DivisionStages.initialWritten, DivisionStages.finishWritten, DivisionGuard.written,
      DivisionBody.written]

end SmcTuring.Appendix.DivisionLayout
