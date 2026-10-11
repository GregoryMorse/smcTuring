module
public import SmcTuring.Appendix.DivisionData
public import SmcTuring.Appendix.DivisionLinear

public section
namespace SmcTuring.Appendix.DivisionSetup

open DivisionImage
abbrev Placement := DivisionPackets.Placement
abbrev State := DivisionByteExecution.State
abbrev Word := DivisionByteCode.Word
abbrev Block := DivisionBlocks.Block

@[expose] def pointer (place : Placement) : ByteControl.Word := FieldRefinement.address (place.stackInstruction + 6)
@[expose] def address (place : Placement) : ByteControl.Word := FieldRefinement.address (place.stackInstruction + 2)
@[expose] def callField (place : Placement) (block : Block) : Nat := DivisionBlocks.callWord (DivisionPackets.layout place) block
@[expose] def displacement (place : Placement) (block : Block) : ByteControl.Word := FieldRefinement.address (callField place block)
@[expose] def tailStart (place : Placement) : Block → Nat
  | .initial => place.origin + DivisionPackets.initialSpan place
  | .guard => place.origin + DivisionPackets.initialSpan place + 106
  | .body => place.origin + DivisionPackets.initialSpan place + 324
  | .finish => place.origin + DivisionLayout.pureSpan place
@[expose] def callPC (place : Placement) (block : Block) : Nat := tailStart place block + 6
@[expose] def callInitial (place : Placement) : Block → Word
  | .body => DivisionBlocks.backDelta (DivisionPackets.layout place)
  | _ => 0

inductive Continuation where
  | guard | body | exit
  deriving DecidableEq
@[expose] def continuationStart (place : Placement) : Continuation → Nat
  | .guard => place.origin + DivisionPackets.initialSpan place + 11
  | .body => place.origin + DivisionPackets.initialSpan place + 117
  | .exit => place.origin + DivisionPackets.initialSpan place + 335

/-- Boundary values that are initialized once and proved preserved by data and
control execution. Neither a future trace nor future fetch is a premise. -/
structure Ready (place : Placement) (state : State) : Prop where
  top : ByteControl.load state.memory (pointer place) = pointer place
  addressValue : ByteControl.load state.memory (address place) = pointer place

theorem call_field_position (place : Placement) (block : Block) (active : block ≠ .finish) :
    callField place block = callPC place block + 1 := by
  cases block <;> simp_all [callField, DivisionBlocks.callWord, DivisionPackets.layout,
    DivisionPackets.fields, callPC, tailStart, Nat.add_assoc]

set_option maxRecDepth 4096 in
theorem tail_placed (place : Placement) (x y : Word) (block : Block) (active : block ≠ .finish) :
    ∀ entry ∈ DivisionPacking.place (tailStart place block)
      (DivisionLayout.tailPackets place (callInitial place block) (block == .guard)),
      entry ∈ DivisionLayout.entries place x y := by
  intro entry member
  apply (DivisionRegions.member (DivisionLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, DivisionLayout.purePackets place⟩, by simp [DivisionLayout.regions], ?_⟩
  change entry ∈ DivisionPacking.place place.origin (DivisionLayout.purePackets place)
  simp only [DivisionLayout.purePackets, DivisionPacking.place_append, DivisionPacking.size_append,
    DivisionLayout.data_size, DivisionLayout.tail_size, DivisionLayout.restore_size,
    Nat.reduceAdd, Nat.add_assoc, List.mem_append]
  cases block <;> simp_all only [ne_eq, not_true_eq_false, tailStart, callInitial,
    beq_self_eq_true, reduceCtorEq, Nat.add_assoc]
  all_goals tauto

set_option maxRecDepth 4096 in
theorem continuation_placed (place : Placement) (x y : Word) (kind : Continuation) :
    ∀ entry ∈ DivisionPacking.place (continuationStart place kind) (DivisionLayout.restorePackets place),
      entry ∈ DivisionLayout.entries place x y := by
  intro entry member
  apply (DivisionRegions.member (DivisionLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, DivisionLayout.purePackets place⟩, by simp [DivisionLayout.regions], ?_⟩
  change entry ∈ DivisionPacking.place place.origin (DivisionLayout.purePackets place)
  simp only [DivisionLayout.purePackets, DivisionPacking.place_append, DivisionPacking.size_append,
    DivisionLayout.data_size, DivisionLayout.tail_size, DivisionLayout.restore_size,
    Nat.reduceAdd, Nat.add_assoc, List.mem_append]
  cases kind <;> simp only [continuationStart, Nat.add_assoc] at member
  all_goals tauto

theorem tail_fits (place : Placement) (valid : DivisionLayout.Admissible place) (block : Block)
    (active : block ≠ .finish) : tailStart place block + 11 < 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp_all only [tailStart, DivisionLayout.pureSpan, DivisionPackets.initialSpan, ite_true, ite_false,
      Bool.false_eq_true, reduceCtorEq]
  all_goals omega

theorem continuation_fits (place : Placement) (valid : DivisionLayout.Admissible place) (kind : Continuation) :
    continuationStart place kind + 30 < 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  cases signed : place.signed <;> cases mod : place.mod <;> cases kind <;>
    simp only [continuationStart, DivisionLayout.pureSpan, DivisionPackets.initialSpan,
      signed, mod, Bool.false_eq_true, ite_true, ite_false] at *
  all_goals omega

theorem pointer_fits (place : Placement) (valid : DivisionLayout.Admissible place) :
    place.stackInstruction + 6 + 4 ≤ 2 ^ 32 := by have h := valid.capacity; omega

theorem address_fits (place : Placement) (valid : DivisionLayout.Admissible place) :
    place.stackInstruction + 2 + 4 ≤ 2 ^ 32 := by have h := valid.capacity; omega

theorem call_fits (place : Placement) (valid : DivisionLayout.Admissible place) (block : Block) :
    callField place block + 4 ≤ 2 ^ 32 := by
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp only [callField, DivisionBlocks.callWord, DivisionPackets.layout, DivisionPackets.fields,
      DivisionLayout.pureSpan, DivisionPackets.initialSpan, DivisionPackets.signSpan,
      signed, mod, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, and_true, and_false,
      Bool.not_false, Bool.not_true] at *
  all_goals omega

theorem slot_alias (place : Placement) : BitVec.sub (pointer place) 4 = address place := by
  have sum : pointer place = BitVec.add (address place) 4 := by
    change BitVec.ofNat 32 (place.stackInstruction + 6) = BitVec.ofNat 32 (place.stackInstruction + 2) + BitVec.ofNat 32 4
    rw [BitVec.ofNat_add_ofNat]
  rw [sum]
  exact BitVec.add_sub_cancel _ _

theorem pointer_nonwrap (place : Placement) (valid : DivisionLayout.Admissible place) :
    4 ≤ (pointer place).toNat := by
  change 4 ≤ (FieldRefinement.address (place.stackInstruction + 6)).toNat
  rw [FieldRefinement.address_toNat _ (pointer_fits place valid)]
  omega

theorem slot_apart (place : Placement) (valid : DivisionLayout.Admissible place) :
    ByteControl.Apart (pointer place) (address place) := by
  intro index
  change ¬Native.ByteMemory.Inside (FieldRefinement.address (place.stackInstruction + 2)).toNat 4
    ((FieldRefinement.address (place.stackInstruction + 6)).toNat + index.val)
  rw [FieldRefinement.address_toNat _ (address_fits place valid), FieldRefinement.address_toNat _ (pointer_fits place valid)]
  unfold Native.ByteMemory.Inside
  omega

theorem call_apart (place : Placement) (valid : DivisionLayout.Admissible place) (block : Block) :
    ByteControl.Apart (displacement place block) (pointer place) := by
  intro index
  change ¬Native.ByteMemory.Inside (FieldRefinement.address (place.stackInstruction + 6)).toNat 4
    ((FieldRefinement.address (callField place block)).toNat + index.val)
  rw [FieldRefinement.address_toNat _ (pointer_fits place valid), FieldRefinement.address_toNat _ (call_fits place valid block)]
  have below := index.isLt
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  unfold Native.ByteMemory.Inside
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp only [callField, DivisionBlocks.callWord, DivisionPackets.layout, DivisionPackets.fields,
      DivisionLayout.pureSpan, DivisionPackets.initialSpan, DivisionPackets.signSpan,
      signed, mod, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, and_true, and_false,
      Bool.not_false, Bool.not_true] at *
  all_goals omega

theorem metadata_outside (place : Placement) (valid : DivisionLayout.Admissible place)
    (slot : DivisionWords.Slot) :
    place.stackInstruction + 2 ≠ DivisionPackets.fields place slot ∧
      place.stackInstruction + 6 ≠ DivisionPackets.fields place slot := by
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  cases signed : place.signed <;> cases mod : place.mod <;> cases slot <;>
    simp only [DivisionPackets.fields, DivisionPackets.initialSpan, DivisionPackets.signSpan,
      DivisionLayout.pureSpan, signed, mod, Bool.false_eq_true, ite_true, ite_false,
      Bool.not_true, Bool.not_false, and_true, and_false] at *
  all_goals omega

theorem run_read_frame {fields : List Nat} (layout : FieldRefinement.Layout fields)
    (program : List DivisionWords.Instruction) (state : State) (observed : Nat)
    (observedIn : observed ∈ fields)
    (writtenIn : ∀ instruction ∈ program, DivisionWords.destination instruction ∈ fields)
    (distinct : ∀ instruction ∈ program, observed ≠ DivisionWords.destination instruction) :
    FieldRefinement.readField (DivisionRefinement.run program state) observed = FieldRefinement.readField state observed := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [DivisionRefinement.run, ih _ (fun op member => writtenIn op (by simp [member]))
      (fun op member => distinct op (by simp [member]))]
    exact DivisionRefinement.execute_read_frame layout instruction state observed
      (writtenIn instruction (by simp)) observedIn (distinct instruction (by simp))

theorem data_read_frame (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (observed : Nat)
    (owned : Owned (DivisionLayout.entries place x y) observed)
    (outside : ∀ slot, observed ≠ DivisionPackets.fields place slot) :
    FieldRefinement.readField (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) state) observed =
      FieldRefinement.readField state observed := by
  apply run_read_frame (DivisionLayout.field_layout place x y valid) _ state observed
    ((DivisionPacking.fields_owned _ _).mpr owned)
  · intro instruction member
    exact (DivisionPacking.fields_owned _ _).mpr
      (DivisionData.block_dependency_owned place x y block instruction member _ (DivisionRefinement.destination_dependency instruction))
  · exact DivisionData.pure_destinations _ _ _
      (DivisionBlocks.words_pure (DivisionPackets.layout place) block
        ⟨state.accumulator, state.carry, FieldRefinement.readField state⟩ _ (fun slot _ => outside slot))

theorem data_ready (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    Ready place (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) state) := by
  have p := data_read_frame place x y valid block state (place.stackInstruction + 6)
    (DivisionLayout.pointer_owned place x y) (fun slot => (metadata_outside place valid slot).2)
  have a := data_read_frame place x y valid block state (place.stackInstruction + 2)
    (DivisionLayout.address_owned place x y) (fun slot => (metadata_outside place valid slot).1)
  constructor
  · change FieldRefinement.readField _ (place.stackInstruction + 6) = pointer place
    rw [p]; exact ready.top
  · change FieldRefinement.readField _ (place.stackInstruction + 2) = pointer place
    rw [a]; exact ready.addressValue

theorem stack_placed (place : Placement) (x y : Word) :
    (⟨place.stackInstruction, .common (.common (.both .store (pointer place) (pointer place)))⟩ : Entry) ∈
      DivisionLayout.entries place x y := by
  apply (DivisionRegions.member (DivisionLayout.regions place x y) _).mpr
  refine ⟨⟨place.stackInstruction, [.common (.common (.both .store (pointer place) (pointer place)))]⟩, ?_, ?_⟩
  · simp [DivisionLayout.regions, pointer]
  · simp [DivisionRegions.Region.entries, DivisionPacking.place]

theorem initial_ready (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (state : State)
    (initial : state.memory = image (DivisionLayout.entries place x y) backing) : Ready place state := by
  have bytes := image_packet _ backing (DivisionLayout.separated place x y valid) _ (stack_placed place x y)
  change Native.ByteMemory.bytesAt (image (DivisionLayout.entries place x y) backing) place.stackInstruction
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
    (region : (⟨pc, [packet]⟩ : DivisionRegions.Region) ∈ DivisionLayout.regions place x y) :
    (⟨pc, packet⟩ : Entry) ∈ DivisionLayout.entries place x y := by
  apply (DivisionRegions.member (DivisionLayout.regions place x y) _).mpr
  exact ⟨⟨pc, [packet]⟩, region, by simp [DivisionRegions.Region.entries, DivisionPacking.place]⟩

theorem initial_mov (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (state : State) (pc : Nat) (value : Word)
    (initial : state.memory = image (DivisionLayout.entries place x y) backing)
    (member : (⟨pc, .common (.common (.immediate .store (FieldRefinement.address (pc + 6)) value))⟩ : Entry) ∈ DivisionLayout.entries place x y)
    (fits : pc + 6 + 4 ≤ 2 ^ 32) : FieldRefinement.readField state (pc + 6) = value := by
  have bytes := image_packet _ backing (DivisionLayout.separated place x y valid) _ member
  change Native.ByteMemory.bytesAt (image (DivisionLayout.entries place x y) backing) pc
    (ByteCode.encode (.immediate .store (FieldRefinement.address (pc + 6)) value)).length =
    ByteCode.encode (.immediate .store (FieldRefinement.address (pc + 6)) value) at bytes
  rw [←initial] at bytes
  rw [←ByteImage.word_at_read_field state _ fits]
  exact (ByteImage.immediate_words _ _ _ _ _ bytes).2

/-- Input parameters and initial result are decoded from their complete real
inactive MOV owners, for arbitrary registers, CF and backing memory. -/
theorem initial_operands (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (state : State)
    (initial : state.memory = image (DivisionLayout.entries place x y) backing) :
    FieldRefinement.readField state (DivisionPackets.fields place .x) = x ∧
      FieldRefinement.readField state (DivisionPackets.fields place .y) = y ∧
      FieldRefinement.readField state (DivisionPackets.fields place .result) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply initial_mov place x y valid backing state _ _ initial
  · apply single_owner_placed; simp [DivisionLayout.regions]
  · exact DivisionLayout.slot_fits place x y valid .x (by trivial)
  · apply single_owner_placed; simp [DivisionLayout.regions]
  · exact DivisionLayout.slot_fits place x y valid .y (by trivial)
  · apply single_owner_placed; simp [DivisionLayout.regions]
  · exact DivisionLayout.slot_fits place x y valid .result (by trivial)

@[expose] def callEntry (place : Placement) (block : Block) : Entry :=
  ⟨callPC place block, if block == .guard then .common (.common (.relative 0))
    else .fixed (.common (.common (.callRelative (callInitial place block))))⟩

theorem call_placed (place : Placement) (x y : Word) (block : Block) (active : block ≠ .finish) :
    callEntry place block ∈ DivisionLayout.entries place x y := by
  apply tail_placed place x y block active
  cases block <;> simp_all [callEntry, callPC, DivisionLayout.tailPackets, DivisionPacking.place,
    Packet.initial, DivisionByteCode.encode_length, DivisionByteCode.instructionLength,
    MultiplyByteCode.instructionLength, ByteCode.instructionLength, ByteCode.MemoryOp.trailer, callInitial]

theorem call_entry_initial (place : Placement) (block : Block) :
    (callEntry place block).bytes = ByteCode.encode (.callRelative (callInitial place block)) := by
  cases block <;> rfl

/-- All three initial CALL fields are read from the single initialized image.
The conditional word starts at zero; the literal back edge is -324 modulo 2^32. -/
theorem initial_call (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (backing : Memory) (state : State)
    (initial : state.memory = image (DivisionLayout.entries place x y) backing) :
    FieldRefinement.readField state (callField place block) = callInitial place block := by
  have bytes := image_packet _ backing (DivisionLayout.separated place x y valid) _ (call_placed place x y block active)
  rw [call_entry_initial, ←initial] at bytes
  have value := ByteImage.relative_word state.memory (callPC place block) (callInitial place block) bytes
  rw [←ByteImage.word_at_read_field state _ (call_fits place valid block), call_field_position place block active]
  exact value

/-- Fixed CALL fields retain their literal values under the invariant. No
separate future-read hypothesis is needed after arbitrary owned mutations. -/
theorem fixed_call (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (fixed : block ≠ .guard) (state : State)
    (intact : Intact (DivisionLayout.entries place x y) state.memory) :
    FieldRefinement.readField state (callField place block) = callInitial place block := by
  have bytes := intact _ (call_placed place x y block active)
  have exactBytes : Native.ByteMemory.bytesAt state.memory (callPC place block)
      (ByteCode.encode (.callRelative (callInitial place block))).length =
      ByteCode.encode (.callRelative (callInitial place block)) := by
    cases block <;> simp_all [callEntry, PacketIntact, DivisionByteCode.encode, MultiplyByteCode.encode]
  rw [←ByteImage.word_at_read_field state _ (call_fits place valid block), call_field_position place block active]
  exact ByteImage.relative_word state.memory _ _ exactBytes

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem word_separate (place : Placement) (valid : DivisionLayout.Admissible place) :
    DivisionWords.Separate (DivisionPackets.fields place) := by
  rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  intro first second same
  cases signed : place.signed <;> cases mod : place.mod <;> cases first <;> cases second <;> try rfl
  all_goals simp only [DivisionPackets.fields, DivisionPackets.initialSpan, DivisionPackets.signSpan,
    DivisionLayout.pureSpan, signed, mod, ite_true, ite_false, Bool.false_eq_true, Bool.not_true,
    Bool.not_false, and_true, and_false, reduceCtorEq] at same h0 ⊢
  all_goals omega

theorem control_separate (place : Placement) (valid : DivisionLayout.Admissible place) :
    DivisionBlocks.Separate (DivisionPackets.layout place) := by
  refine ⟨word_separate place valid, ?_, ?_, ?_, ?_⟩
  · intro field member slot
    simp only [DivisionPackets.layout, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
    rcases member with rfl | rfl | rfl | rfl
    all_goals cases signed : place.signed <;> cases mod : place.mod <;> cases slot <;>
      simp only [DivisionPackets.layout, DivisionPackets.fields, DivisionPackets.initialSpan,
        DivisionPackets.signSpan, DivisionLayout.pureSpan, signed, mod,
        Bool.false_eq_true, Bool.not_true, Bool.not_false, ite_true, ite_false,
        and_true, and_false] at *
    all_goals omega
  all_goals simp only [DivisionPackets.layout]
  all_goals rcases valid with ⟨h0,h1,h2,h3,h4,h5⟩
  all_goals cases signed : place.signed <;> cases mod : place.mod <;>
    simp only [DivisionPackets.initialSpan, DivisionLayout.pureSpan,
      signed, mod, Bool.false_eq_true, ite_true, ite_false] at *
  all_goals omega

theorem continuation_code (place : Placement) (kind : Continuation) :
    FieldRefinement.address (continuationStart place kind) = match kind with
      | .guard => DivisionBlocks.guardContinuation (DivisionPackets.layout place)
      | .body => DivisionBlocks.bodyContinuation (DivisionPackets.layout place)
      | .exit => DivisionBlocks.exitContinuation (DivisionPackets.layout place) := by
  cases kind <;> simp only [continuationStart, DivisionBlocks.guardContinuation,
    DivisionBlocks.bodyContinuation, DivisionBlocks.guardPC, DivisionBlocks.exitContinuation,
    DivisionBlocks.bodyPC, DivisionPackets.layout, DivisionBlocks.initialSpan,
    DivisionPackets.initialSpan, FieldRefinement.address, ←BitVec.ofNat_add_ofNat]
  case guard =>
    change BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + (11 : Word) =
      BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + 11
    rfl
  case body =>
    change BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + (117 : Word) =
      BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + 11 + 30 + 65 + 11
    ring
  case exit =>
    change BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + (335 : Word) =
      BitVec.ofNat 32 place.origin + BitVec.ofNat 32 (DivisionPackets.initialSpan place) + 11 + 30 + 65 + 11 + 30 + 177 + 11
    ring

end SmcTuring.Appendix.DivisionSetup
