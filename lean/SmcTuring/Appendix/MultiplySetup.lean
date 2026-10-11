module
public import SmcTuring.Appendix.MultiplyData
public import SmcTuring.Appendix.MultiplyLinear

public section
namespace SmcTuring.Appendix.MultiplySetup

open MultiplyImage
abbrev Placement := MultiplyPackets.Placement
abbrev State := MultiplyByteExecution.State
abbrev Word := MultiplyByteCode.Word
abbrev Block := MultiplyBlocks.Block

@[expose] def pointer (place : Placement) : ByteControl.Word := FieldRefinement.address (place.stackInstruction + 6)
@[expose] def address (place : Placement) : ByteControl.Word := FieldRefinement.address (place.stackInstruction + 2)
@[expose] def callField (place : Placement) (block : Block) : Nat := MultiplyBlocks.callWord (MultiplyPackets.layout place) block
@[expose] def displacement (place : Placement) (block : Block) : ByteControl.Word := FieldRefinement.address (callField place block)
@[expose] def tailStart (place : Placement) : Block → Nat
  | .initial => place.origin + 44
  | .guard => place.origin + 150
  | .body => place.origin + 321
  | .finish => place.origin + 382
@[expose] def callPC (place : Placement) (block : Block) : Nat := tailStart place block + 6
@[expose] def callInitial (place : Placement) : Block → Word
  | .body => MultiplyBlocks.backDelta (MultiplyPackets.layout place)
  | _ => 0

inductive Continuation where
  | guard | body | exit
  deriving DecidableEq
@[expose] def continuationStart (place : Placement) : Continuation → Nat
  | .guard => place.origin + 55
  | .body => place.origin + 161
  | .exit => place.origin + 332

/-- Boundary values that are initialized once and proved preserved by data and
control execution. Neither a future trace nor future fetch is a premise. -/
structure Ready (place : Placement) (state : State) : Prop where
  top : ByteControl.load state.memory (pointer place) = pointer place
  addressValue : ByteControl.load state.memory (address place) = pointer place

theorem call_field_position (place : Placement) (block : Block) (active : block ≠ .finish) :
    callField place block = callPC place block + 1 := by
  cases block <;> simp_all [callField, MultiplyBlocks.callWord, MultiplyPackets.layout,
    MultiplyPackets.fields, callPC, tailStart, Nat.add_assoc]

theorem tail_placed (place : Placement) (x y : Word) (block : Block) (active : block ≠ .finish) :
    ∀ entry ∈ MultiplyPacking.place (tailStart place block)
      (MultiplyLayout.tailPackets place (callInitial place block) (block == .guard)),
      entry ∈ MultiplyLayout.entries place x y := by
  intro entry member
  apply (MultiplyRegions.member (MultiplyLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, MultiplyLayout.purePackets place⟩, by simp [MultiplyLayout.regions], ?_⟩
  change entry ∈ MultiplyPacking.place place.origin (MultiplyLayout.purePackets place)
  simp only [MultiplyLayout.purePackets, MultiplyPacking.place_append, MultiplyPacking.size_append,
    MultiplyLayout.data_size, MultiplyLayout.tail_size, MultiplyLayout.restore_size,
    Nat.reduceAdd, List.mem_append]
  cases block <;> simp_all only [ne_eq, not_true_eq_false, tailStart, callInitial,
    beq_self_eq_true, reduceCtorEq]
  all_goals tauto

theorem continuation_placed (place : Placement) (x y : Word) (kind : Continuation) :
    ∀ entry ∈ MultiplyPacking.place (continuationStart place kind) (MultiplyLayout.restorePackets place),
      entry ∈ MultiplyLayout.entries place x y := by
  intro entry member
  apply (MultiplyRegions.member (MultiplyLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, MultiplyLayout.purePackets place⟩, by simp [MultiplyLayout.regions], ?_⟩
  change entry ∈ MultiplyPacking.place place.origin (MultiplyLayout.purePackets place)
  simp only [MultiplyLayout.purePackets, MultiplyPacking.place_append, MultiplyPacking.size_append,
    MultiplyLayout.data_size, MultiplyLayout.tail_size, MultiplyLayout.restore_size,
    Nat.reduceAdd, List.mem_append]
  cases kind <;> simp only [continuationStart] at member
  all_goals tauto

theorem tail_fits (place : Placement) (valid : MultiplyLayout.Admissible place) (block : Block)
    (active : block ≠ .finish) : tailStart place block + 11 < 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  cases block <;> simp_all only [tailStart]
  all_goals omega

theorem continuation_fits (place : Placement) (valid : MultiplyLayout.Admissible place) (kind : Continuation) :
    continuationStart place kind + 30 < 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  cases kind <;> simp only [continuationStart]
  all_goals omega

theorem pointer_fits (place : Placement) (valid : MultiplyLayout.Admissible place) :
    place.stackInstruction + 6 + 4 ≤ 2 ^ 32 := by have h := valid.capacity; omega

theorem address_fits (place : Placement) (valid : MultiplyLayout.Admissible place) :
    place.stackInstruction + 2 + 4 ≤ 2 ^ 32 := by have h := valid.capacity; omega

theorem call_fits (place : Placement) (valid : MultiplyLayout.Admissible place) (block : Block) :
    callField place block + 4 ≤ 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  cases block <;> simp only [callField, MultiplyBlocks.callWord, MultiplyPackets.layout, MultiplyPackets.fields]
  all_goals omega

theorem slot_alias (place : Placement) : BitVec.sub (pointer place) 4 = address place := by
  have sum : pointer place = BitVec.add (address place) 4 := by
    change BitVec.ofNat 32 (place.stackInstruction + 6) = BitVec.ofNat 32 (place.stackInstruction + 2) + BitVec.ofNat 32 4
    rw [BitVec.ofNat_add_ofNat]
  rw [sum]
  exact BitVec.add_sub_cancel _ _

theorem pointer_nonwrap (place : Placement) (valid : MultiplyLayout.Admissible place) :
    4 ≤ (pointer place).toNat := by
  change 4 ≤ (FieldRefinement.address (place.stackInstruction + 6)).toNat
  rw [FieldRefinement.address_toNat _ (pointer_fits place valid)]
  omega

theorem slot_apart (place : Placement) (valid : MultiplyLayout.Admissible place) :
    ByteControl.Apart (pointer place) (address place) := by
  intro index
  change ¬Native.ByteMemory.Inside (FieldRefinement.address (place.stackInstruction + 2)).toNat 4
    ((FieldRefinement.address (place.stackInstruction + 6)).toNat + index.val)
  rw [FieldRefinement.address_toNat _ (address_fits place valid), FieldRefinement.address_toNat _ (pointer_fits place valid)]
  unfold Native.ByteMemory.Inside
  omega

theorem call_apart (place : Placement) (valid : MultiplyLayout.Admissible place) (block : Block) :
    ByteControl.Apart (displacement place block) (pointer place) := by
  intro index
  change ¬Native.ByteMemory.Inside (FieldRefinement.address (place.stackInstruction + 6)).toNat 4
    ((FieldRefinement.address (callField place block)).toNat + index.val)
  rw [FieldRefinement.address_toNat _ (pointer_fits place valid), FieldRefinement.address_toNat _ (call_fits place valid block)]
  have below := index.isLt
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  unfold Native.ByteMemory.Inside
  cases block <;> simp only [callField, MultiplyBlocks.callWord, MultiplyPackets.layout, MultiplyPackets.fields]
  all_goals omega

theorem metadata_outside (place : Placement) (valid : MultiplyLayout.Admissible place)
    (slot : MultiplyWords.Slot) :
    place.stackInstruction + 2 ≠ MultiplyPackets.fields place slot ∧
      place.stackInstruction + 6 ≠ MultiplyPackets.fields place slot := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  cases slot <;> simp only [MultiplyPackets.fields]
  all_goals omega

theorem run_read_frame {fields : List Nat} (layout : FieldRefinement.Layout fields)
    (program : List MultiplyWords.Instruction) (state : State) (observed : Nat)
    (observedIn : observed ∈ fields)
    (writtenIn : ∀ instruction ∈ program, MultiplyWords.destination instruction ∈ fields)
    (distinct : ∀ instruction ∈ program, observed ≠ MultiplyWords.destination instruction) :
    FieldRefinement.readField (MultiplyRefinement.run program state) observed = FieldRefinement.readField state observed := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [MultiplyRefinement.run, ih _ (fun op member => writtenIn op (by simp [member]))
      (fun op member => distinct op (by simp [member]))]
    exact MultiplyRefinement.execute_read_frame layout instruction state observed
      (writtenIn instruction (by simp)) observedIn (distinct instruction (by simp))

theorem data_read_frame (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (block : Block) (state : State) (observed : Nat)
    (owned : Owned (MultiplyLayout.entries place x y) observed)
    (outside : ∀ slot, observed ≠ MultiplyPackets.fields place slot) :
    FieldRefinement.readField (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) state) observed =
      FieldRefinement.readField state observed := by
  apply run_read_frame (MultiplyLayout.field_layout place x y valid) _ state observed
    ((MultiplyPacking.fields_owned _ _).mpr owned)
  · intro instruction member
    exact (MultiplyPacking.fields_owned _ _).mpr
      (MultiplyData.block_dependency_owned place x y block instruction member _ (MultiplyRefinement.destination_dependency instruction))
  · exact MultiplyLoop.pure_destinations _ _ _
      (MultiplyBlocks.words_pure (MultiplyPackets.layout place) block
        ⟨state.accumulator, state.carry, FieldRefinement.readField state⟩ _ outside)

theorem data_ready (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    Ready place (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) state) := by
  have p := data_read_frame place x y valid block state (place.stackInstruction + 6)
    (MultiplyLayout.pointer_owned place x y) (fun slot => (metadata_outside place valid slot).2)
  have a := data_read_frame place x y valid block state (place.stackInstruction + 2)
    (MultiplyLayout.address_owned place x y) (fun slot => (metadata_outside place valid slot).1)
  constructor
  · change FieldRefinement.readField _ (place.stackInstruction + 6) = pointer place
    rw [p]; exact ready.top
  · change FieldRefinement.readField _ (place.stackInstruction + 2) = pointer place
    rw [a]; exact ready.addressValue

theorem stack_placed (place : Placement) (x y : Word) :
    (⟨place.stackInstruction, .common (.both .store (pointer place) (pointer place))⟩ : Entry) ∈
      MultiplyLayout.entries place x y := by
  apply (MultiplyRegions.member (MultiplyLayout.regions place x y) _).mpr
  refine ⟨⟨place.stackInstruction, [.common (.both .store (pointer place) (pointer place))]⟩, ?_, ?_⟩
  · simp [MultiplyLayout.regions, pointer]
  · simp [MultiplyRegions.Region.entries, MultiplyPacking.place]

theorem initial_ready (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (state : State)
    (initial : state.memory = image (MultiplyLayout.entries place x y) backing) : Ready place state := by
  have bytes := image_packet _ backing (MultiplyLayout.separated place x y valid) _ (stack_placed place x y)
  change Native.ByteMemory.bytesAt (image (MultiplyLayout.entries place x y) backing) place.stackInstruction
    (ByteCode.encode (.immediate .store (pointer place) (pointer place))).length =
    ByteCode.encode (.immediate .store (pointer place) (pointer place)) at bytes
  rw [←initial] at bytes
  have words := ByteImage.immediate_words _ _ _ _ _ bytes
  constructor
  · change FieldRefinement.readField state (place.stackInstruction + 6) = pointer place
    rw [←ByteImage.word_at_read_field state _ (pointer_fits place valid)]
    exact words.2
  · change FieldRefinement.readField state (place.stackInstruction + 2) = pointer place
    rw [←ByteImage.word_at_read_field state _ (address_fits place valid)]
    exact words.1

theorem single_owner_placed (place : Placement) (x y : Word) (pc : Nat) (packet : Packet)
    (region : (⟨pc, [packet]⟩ : MultiplyRegions.Region) ∈ MultiplyLayout.regions place x y) :
    (⟨pc, packet⟩ : Entry) ∈ MultiplyLayout.entries place x y := by
  apply (MultiplyRegions.member (MultiplyLayout.regions place x y) _).mpr
  exact ⟨⟨pc, [packet]⟩, region, by simp [MultiplyRegions.Region.entries, MultiplyPacking.place]⟩

theorem initial_mov (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (state : State) (pc : Nat) (value : Word)
    (initial : state.memory = image (MultiplyLayout.entries place x y) backing)
    (member : (⟨pc, .common (.immediate .store (FieldRefinement.address (pc + 6)) value)⟩ : Entry) ∈ MultiplyLayout.entries place x y)
    (fits : pc + 6 + 4 ≤ 2 ^ 32) : FieldRefinement.readField state (pc + 6) = value := by
  have bytes := image_packet _ backing (MultiplyLayout.separated place x y valid) _ member
  change Native.ByteMemory.bytesAt (image (MultiplyLayout.entries place x y) backing) pc
    (ByteCode.encode (.immediate .store (FieldRefinement.address (pc + 6)) value)).length =
    ByteCode.encode (.immediate .store (FieldRefinement.address (pc + 6)) value) at bytes
  rw [←initial] at bytes
  rw [←ByteImage.word_at_read_field state _ fits]
  exact (ByteImage.immediate_words _ _ _ _ _ bytes).2

/-- Input parameters and initial result are decoded from their complete real
inactive MOV owners, for arbitrary registers, CF and backing memory. -/
theorem initial_operands (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (state : State)
    (initial : state.memory = image (MultiplyLayout.entries place x y) backing) :
    FieldRefinement.readField state (MultiplyPackets.fields place .x) = x ∧
      FieldRefinement.readField state (MultiplyPackets.fields place .y) = y ∧
      FieldRefinement.readField state (MultiplyPackets.fields place .result) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply initial_mov place x y valid backing state _ _ initial
  · apply single_owner_placed; simp [MultiplyLayout.regions]
  · exact MultiplyLayout.slot_fits place x y valid .x
  · apply single_owner_placed; simp [MultiplyLayout.regions]
  · exact MultiplyLayout.slot_fits place x y valid .y
  · apply single_owner_placed; simp [MultiplyLayout.regions]
  · exact MultiplyLayout.slot_fits place x y valid .result

@[expose] def callEntry (place : Placement) (block : Block) : Entry :=
  ⟨callPC place block, if block == .guard then .common (.relative 0)
    else .fixed (.common (.callRelative (callInitial place block)))⟩

theorem call_placed (place : Placement) (x y : Word) (block : Block) (active : block ≠ .finish) :
    callEntry place block ∈ MultiplyLayout.entries place x y := by
  apply tail_placed place x y block active
  cases block <;> simp_all [callEntry, callPC, MultiplyLayout.tailPackets, MultiplyPacking.place,
    Packet.initial, MultiplyByteCode.encode_length, MultiplyByteCode.instructionLength,
    ByteCode.instructionLength, ByteCode.MemoryOp.trailer, callInitial]

theorem call_entry_initial (place : Placement) (block : Block) :
    (callEntry place block).bytes = ByteCode.encode (.callRelative (callInitial place block)) := by
  cases block <;> rfl

/-- All three initial CALL fields are read from the single initialized image.
The conditional word starts at zero; the literal back edge is -277 modulo 2^32. -/
theorem initial_call (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (backing : Memory) (state : State)
    (initial : state.memory = image (MultiplyLayout.entries place x y) backing) :
    FieldRefinement.readField state (callField place block) = callInitial place block := by
  have bytes := image_packet _ backing (MultiplyLayout.separated place x y valid) _ (call_placed place x y block active)
  rw [call_entry_initial, ←initial] at bytes
  have value := ByteImage.relative_word state.memory (callPC place block) (callInitial place block) bytes
  rw [←ByteImage.word_at_read_field state _ (call_fits place valid block), call_field_position place block active]
  exact value

/-- Fixed CALL fields retain their literal values under the invariant. No
separate future-read hypothesis is needed after arbitrary owned mutations. -/
theorem fixed_call (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (fixed : block ≠ .guard) (state : State)
    (intact : Intact (MultiplyLayout.entries place x y) state.memory) :
    FieldRefinement.readField state (callField place block) = callInitial place block := by
  have bytes := intact _ (call_placed place x y block active)
  have exactBytes : Native.ByteMemory.bytesAt state.memory (callPC place block)
      (ByteCode.encode (.callRelative (callInitial place block))).length =
      ByteCode.encode (.callRelative (callInitial place block)) := by
    cases block <;> simp_all [callEntry, PacketIntact, MultiplyByteCode.encode]
  rw [←ByteImage.word_at_read_field state _ (call_fits place valid block), call_field_position place block active]
  exact ByteImage.relative_word state.memory _ _ exactBytes

theorem word_separate (place : Placement) (valid : MultiplyLayout.Admissible place) :
    MultiplyWords.Separate (MultiplyPackets.fields place) := by
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  intro first second same
  cases first <;> cases second <;> simp_all only [MultiplyPackets.fields, reduceCtorEq]
  all_goals omega

theorem control_separate (place : Placement) (valid : MultiplyLayout.Admissible place) :
    MultiplyBlocks.Separate (MultiplyPackets.layout place) := by
  refine ⟨word_separate place valid, ?_, ?_, ?_, ?_⟩
  · intro field member slot
    simp only [MultiplyPackets.layout, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases valid with ⟨h0,h1,h2,h3,h4⟩
    rcases member with rfl | rfl | rfl | rfl
    all_goals cases slot <;> simp only [MultiplyPackets.layout, MultiplyPackets.fields]
    all_goals omega
  all_goals simp only [MultiplyPackets.layout]
  all_goals rcases valid with ⟨h0,h1,h2,h3,h4⟩
  all_goals omega

end SmcTuring.Appendix.MultiplySetup
