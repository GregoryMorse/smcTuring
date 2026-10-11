module
public import SmcTuring.Appendix.BranchWhole
public import SmcTuring.Appendix.ByteRegions

public section

namespace SmcTuring.Appendix.SpacedLayout

open ByteImage
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

/-- Independent actual byte coordinates. Stack/prefix/continuation/storage gaps
may contain arbitrary host bytes, which no pure branch instruction executes. -/
structure Sites where
  stack : Nat
  start : Nat
  taken : Nat
  data : Nat
@[expose] def prefixStart (sites : Sites) : Nat := sites.start
@[expose] def andPC (sites : Sites) (signed : Bool) (relation : Relation) : Nat := sites.start + BranchLayout.leading signed relation
@[expose] def xorPC (sites : Sites) (signed : Bool) (relation : Relation) : Nat := andPC sites signed relation + 10
@[expose] def prefixEnd (sites : Sites) (signed : Bool) (relation : Relation) : Nat := andPC sites signed relation + 20
@[expose] def callPC (sites : Sites) (signed : Bool) (relation : Relation) : Nat := prefixEnd sites signed relation + 6
@[expose] def fallPC (sites : Sites) (signed : Bool) (relation : Relation) : Nat := callPC sites signed relation + 5
@[expose] def takenPC (sites : Sites) : Nat := sites.taken
@[expose] def xPC (sites : Sites) : Nat := sites.data
@[expose] def yPC (sites : Sites) : Nat := sites.data + 10
@[expose] def endPC (sites : Sites) : Nat := sites.data + 20
@[expose] def fields (sites : Sites) (signed : Bool) (relation : Relation) : Branching.Fields :=
  { x := xPC sites + 6
    y := yPC sites + 6
    mask := xorPC sites signed relation + 6
    delta := andPC sites signed relation + 6
    displacement := callPC sites signed relation + 1 }
@[expose] def delta (sites : Sites) (signed : Bool) (relation : Relation) : Word :=
  FieldRefinement.address (takenPC sites) - FieldRefinement.address (fallPC sites signed relation)
@[expose] def program (sites : Sites) (signed : Bool) (relation : Relation) : List Machine32.Instruction :=
  Branching.relationProgram (fields sites signed relation) signed relation (delta sites signed relation)
@[expose] def stack (sites : Sites) : Packet := BranchLayout.stack sites.stack
@[expose] def tail (sites : Sites) : List Packet := BranchLayout.tail sites.stack
@[expose] def continuation (sites : Sites) : List Packet := BranchLayout.continuation sites.stack
@[expose] def storage (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) : List Packet :=
  [.immediate .store (FieldRefinement.address (fields sites signed relation).x) x,
   .immediate .store (FieldRefinement.address (fields sites signed relation).y) y]
@[expose] def core (sites : Sites) (signed : Bool) (relation : Relation) : List Packet :=
  (program sites signed relation).map ByteProgram.packet ++ tail sites ++ continuation sites
@[expose] def regions (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) : List ByteRegions.Region :=
  [⟨sites.stack, [stack sites]⟩, ⟨sites.start, core sites signed relation⟩,
   ⟨sites.taken, continuation sites⟩, ⟨sites.data, storage sites signed relation x y⟩]
@[expose] def entries (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) : List Entry :=
  ByteRegions.entries (regions sites signed relation x y)
@[expose] def ownedFields (sites : Sites) (signed : Bool) (relation : Relation) : List Nat :=
  [sites.stack + 2, sites.stack + 6, (fields sites signed relation).delta, (fields sites signed relation).mask,
    (fields sites signed relation).displacement, (fields sites signed relation).x, (fields sites signed relation).y]

/-- Static complete packet extent/order constraints. No execution state,
trace, Ready predicate or branch outcome appears in this placement contract. -/
structure OrderedValid (sites : Sites) (signed : Bool) (relation : Relation) : Prop where
  stackBefore : sites.stack + 10 ≤ sites.start
  fallBefore : fallPC sites signed relation + 30 ≤ sites.taken
  takenBefore : sites.taken + 30 ≤ sites.data
  capacity : endPC sites ≤ 2 ^ 32


/-- Static complete extents and disjoint regions, with no physical ordering
restriction. Pure observation endpoints are representable without wrapping.
No execution state, trace, Ready or branch outcome is a placement premise. -/
structure Valid (sites : Sites) (signed : Bool) (relation : Relation) : Prop where
  stackCapacity : sites.stack + 10 ≤ 2 ^ 32
  coreCapacity : fallPC sites signed relation + 30 < 2 ^ 32
  takenCapacity : sites.taken + 30 < 2 ^ 32
  dataCapacity : endPC sites ≤ 2 ^ 32
  stackCore : sites.stack + 10 ≤ sites.start ∨ fallPC sites signed relation + 30 ≤ sites.stack
  stackTaken : sites.stack + 10 ≤ sites.taken ∨ sites.taken + 30 ≤ sites.stack
  stackData : sites.stack + 10 ≤ sites.data ∨ sites.data + 20 ≤ sites.stack
  coreTaken : fallPC sites signed relation + 30 ≤ sites.taken ∨ sites.taken + 30 ≤ sites.start
  coreData : fallPC sites signed relation + 30 ≤ sites.data ∨ sites.data + 20 ≤ sites.start
  takenData : sites.taken + 30 ≤ sites.data ∨ sites.data + 20 ≤ sites.taken

/-- Exactly the ten static geometry premises, executable for comparison at
independently obtained assembler coordinates. -/
@[expose] def admissibleChecks (sites : Sites) (signed : Bool) (relation : Relation) : List Bool :=
  [decide (sites.stack + 10 ≤ 2 ^ 32),
   decide (fallPC sites signed relation + 30 < 2 ^ 32),
   decide (sites.taken + 30 < 2 ^ 32), decide (endPC sites ≤ 2 ^ 32),
   decide (sites.stack + 10 ≤ sites.start ∨ fallPC sites signed relation + 30 ≤ sites.stack),
   decide (sites.stack + 10 ≤ sites.taken ∨ sites.taken + 30 ≤ sites.stack),
   decide (sites.stack + 10 ≤ sites.data ∨ sites.data + 20 ≤ sites.stack),
   decide (fallPC sites signed relation + 30 ≤ sites.taken ∨ sites.taken + 30 ≤ sites.start),
   decide (fallPC sites signed relation + 30 ≤ sites.data ∨ sites.data + 20 ≤ sites.start),
   decide (sites.taken + 30 ≤ sites.data ∨ sites.data + 20 ≤ sites.taken)]

theorem valid_checks (sites : Sites) (signed : Bool) (relation : Relation) :
    Valid sites signed relation ↔ (admissibleChecks sites signed relation).all id = true := by
  simp only [admissibleChecks, List.all_cons, List.all_nil, Bool.and_eq_true,
    decide_eq_true_eq, and_true, id_eq]
  constructor
  · intro valid
    exact ⟨valid.stackCapacity, valid.coreCapacity, valid.takenCapacity, valid.dataCapacity,
      valid.stackCore, valid.stackTaken, valid.stackData, valid.coreTaken, valid.coreData, valid.takenData⟩
  · rintro ⟨stackFit, coreFit, takenFit, dataFit, stackCore, stackTaken, stackData,
      coreTaken, coreData, takenData⟩
    exact ⟨stackFit, coreFit, takenFit, dataFit, stackCore, stackTaken, stackData, coreTaken, coreData, takenData⟩

theorem ordered_valid (sites : Sites) (signed : Bool) (relation : Relation)
    (ordered : OrderedValid sites signed relation) : Valid sites signed relation := by
  rcases ordered with ⟨stackBefore, fallBefore, takenBefore, capacity⟩
  have startBefore : sites.start ≤ fallPC sites signed relation := by
    simp only [fallPC, callPC, prefixEnd, andPC]; omega
  simp only [endPC] at capacity
  constructor <;> (try simp only [endPC]) <;> omega

theorem span (sites : Sites) (signed : Bool) (relation : Relation) :
    ByteProgram.span (program sites signed relation) = BranchLayout.leading signed relation + 20 := BranchLayout.span _ _ _ _

theorem stack_size (sites : Sites) : BytePacking.size [stack sites] = 10 := by
  simp [stack, BranchLayout.stack, BytePacking.size, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]

theorem storage_size (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    BytePacking.size (storage sites signed relation x y) = 20 := by
  simp [storage, BytePacking.size, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]

theorem core_end (sites : Sites) (signed : Bool) (relation : Relation) :
    sites.start + BytePacking.size (core sites signed relation) = fallPC sites signed relation + 30 := by
  have prefixSize : BytePacking.size ((program sites signed relation).map ByteProgram.packet) = BranchLayout.leading signed relation + 20 := span _ _ _
  simp only [core, BytePacking.size_append, prefixSize, tail, continuation, BranchLayout.tail_size, BranchLayout.continuation_size]
  simp only [fallPC, callPC, prefixEnd, andPC, Nat.add_assoc]

theorem ordered (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : OrderedValid sites signed relation) : ByteRegions.Ordered (regions sites signed relation x y) := by
  have first := valid.stackBefore
  have second := valid.fallBefore
  have third := valid.takenBefore
  have startBefore : sites.start ≤ fallPC sites signed relation := by simp only [fallPC, callPC, prefixEnd, andPC]; omega
  simp only [ByteRegions.Ordered, regions, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, ByteRegions.Region.finish, stack_size, core_end,
    continuation, BranchLayout.continuation_size]
  constructor
  · intro later member; rcases member with rfl | rfl | rfl <;> simp only <;> omega
  · constructor
    · intro later member; rcases member with rfl | rfl <;> simp only <;> omega
    · constructor
      · intro later member; rcases member with rfl; exact third
      · simp

theorem region_capacity (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) :
    ∀ region ∈ regions sites signed relation x y, region.finish ≤ 2 ^ 32 := by
  intro region member
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa only [ByteRegions.Region.finish, stack_size] using valid.stackCapacity
  · change sites.start + BytePacking.size (core sites signed relation) ≤ 2 ^ 32
    rw [core_end]; exact Nat.le_of_lt valid.coreCapacity
  · simpa only [ByteRegions.Region.finish, continuation, BranchLayout.continuation_size]
      using Nat.le_of_lt valid.takenCapacity
  · simpa only [ByteRegions.Region.finish, storage_size, endPC] using valid.dataCapacity

theorem regions_disjoint (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : ByteRegions.Disjoint (regions sites signed relation x y) := by
  simp only [ByteRegions.Disjoint, regions, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, ByteRegions.Region.finish, stack_size, core_end,
    continuation, BranchLayout.continuation_size, storage_size]
  constructor
  · intro later member
    rcases member with rfl | rfl | rfl
    · change sites.stack + 10 ≤ sites.start ∨
        sites.start + BytePacking.size (core sites signed relation) ≤ sites.stack
      rw [core_end]; exact valid.stackCore
    · exact valid.stackTaken
    · exact valid.stackData
  · constructor
    · intro later member
      rcases member with rfl | rfl
      · exact valid.coreTaken
      · exact valid.coreData
    · constructor
      · intro later member
        rcases member with rfl
        exact valid.takenData
      · simp

theorem separated (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : Separated (entries sites signed relation x y) :=
  ByteRegions.separated_disjoint _ (regions_disjoint sites signed relation x y valid)

theorem image_fields (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    BytePacking.fields (entries sites signed relation x y) = ownedFields sites signed relation := by
  cases signed <;> cases relation <;>
    simp [entries, ByteRegions.entries, ByteRegions.Region.entries, regions, core, program,
      Branching.relationProgram, Branching.program, Branching.comparison,
      BytePacking.place, BytePacking.fields, ByteProgram.packet, Packet.initial,
      Entry.fields, Packet.offsets, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer,
      stack, tail, continuation, BranchLayout.stack, BranchLayout.tail, BranchLayout.continuation, storage,
      ownedFields, fields, Branching.swapFields, andPC, xorPC, callPC, prefixEnd,
      BranchLayout.leading, BranchLayout.gtFlag, BranchLayout.notFlag, xPC, yPC, Nat.add_assoc]

theorem full_layout (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : FieldRefinement.Layout (ownedFields sites signed relation) := by
  have layout := BytePacking.field_layout _ (separated sites signed relation x y valid)
    (ByteRegions.capacity _ (region_capacity sites signed relation x y valid))
  change FieldRefinement.Layout (BytePacking.fields (entries sites signed relation x y)) at layout
  rwa [image_fields] at layout

theorem field_owned (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (field : Nat) (member : field ∈ ownedFields sites signed relation) : Owned (entries sites signed relation x y) field := by
  apply (BytePacking.fields_owned _ field).mp
  rwa [image_fields]

theorem fields_owned (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (field : Nat) (member : field ∈ BranchExecution.fields (fields sites signed relation)) :
    Owned (entries sites signed relation x y) field := by
  apply field_owned sites signed relation x y
  simp only [BranchExecution.fields, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [ownedFields, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem field_layout (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) : FieldRefinement.Layout (BranchExecution.fields (fields sites signed relation)) := by
  have layout := full_layout sites signed relation x y valid
  constructor
  · intro field member
    exact layout.fits field (by simp only [BranchExecution.fields, List.mem_cons, List.not_mem_nil, or_false] at member; simp only [ownedFields, List.mem_cons, List.not_mem_nil, or_false]; tauto)
  · intro first firstMember second secondMember distinct
    apply layout.separate first _ second _ distinct
    all_goals
      simp only [BranchExecution.fields, List.mem_cons, List.not_mem_nil, or_false] at *
      simp only [ownedFields, List.mem_cons, List.not_mem_nil, or_false]
      tauto

theorem linked (sites : Sites) (signed : Bool) (relation : Relation) :
    ByteProgram.Linked (prefixStart sites) (program sites signed relation) := by
  cases signed <;> cases relation <;>
    simp [program, Branching.relationProgram, Branching.program, Branching.comparison,
      ByteProgram.Linked, ByteProgram.OwnOperand, ByteProgram.bytes, ByteProgram.packet,
      Packet.initial, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer,
      fields, andPC, xorPC, callPC, prefixEnd, prefixStart,
      BranchLayout.leading, BranchLayout.gtFlag, BranchLayout.notFlag, Branching.swapFields]

theorem separate_fields (sites : Sites) (signed : Bool) (relation : Relation)
    (valid : Valid sites signed relation) : Branching.Separate (fields sites signed relation) := by
  have apart := valid.coreData
  constructor <;> simp only [fields, xPC, yPC, xorPC, callPC, prefixEnd, fallPC, andPC] at * <;> omega

theorem initial_intact (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (valid : Valid sites signed relation) : Intact (entries sites signed relation x y) (image (entries sites signed relation x y) backing) :=
  initialized_intact _ backing (separated sites signed relation x y valid)

theorem core_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place sites.start (core sites signed relation), entry ∈ entries sites signed relation x y := by
  intro entry member
  apply (ByteRegions.member _ entry).mpr
  exact ⟨⟨sites.start, core sites signed relation⟩, by simp [regions], member⟩

theorem stack_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    (⟨sites.stack, stack sites⟩ : Entry) ∈ entries sites signed relation x y := by
  apply (ByteRegions.member _ _).mpr
  exact ⟨⟨sites.stack, [stack sites]⟩, by simp [regions], by simp [ByteRegions.Region.entries, BytePacking.place]⟩

theorem prefix_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ ByteProgram.entries (prefixStart sites) (program sites signed relation), entry ∈ entries sites signed relation x y := by
  intro entry member
  apply core_placed sites signed relation x y entry
  simp only [core, BytePacking.place_append, List.mem_append]
  exact Or.inl (Or.inl member)

theorem tail_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (prefixEnd sites signed relation) (tail sites), entry ∈ entries sites signed relation x y := by
  have prefixSize : BytePacking.size ((program sites signed relation).map ByteProgram.packet) = BranchLayout.leading signed relation + 20 := span _ _ _
  intro entry member
  apply core_placed sites signed relation x y entry
  simp only [core, BytePacking.place_append, List.mem_append]
  left; right
  simpa only [prefixSize, prefixEnd, andPC, Nat.add_assoc] using member

theorem fall_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (fallPC sites signed relation) (continuation sites), entry ∈ entries sites signed relation x y := by
  have prefixSize : BytePacking.size ((program sites signed relation).map ByteProgram.packet) = BranchLayout.leading signed relation + 20 := span _ _ _
  intro entry member
  apply core_placed sites signed relation x y entry
  simp only [core, BytePacking.place_append, List.mem_append]
  right
  simpa only [BytePacking.size_append, prefixSize, tail, BranchLayout.tail_size, fallPC, callPC, prefixEnd, andPC, Nat.add_assoc] using member

theorem taken_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (takenPC sites) (continuation sites), entry ∈ entries sites signed relation x y := by
  intro entry member
  apply (ByteRegions.member _ entry).mpr
  exact ⟨⟨sites.taken, continuation sites⟩, by simp [regions], member⟩

theorem storage_placed (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (xPC sites) (storage sites signed relation x y), entry ∈ entries sites signed relation x y := by
  intro entry member
  apply (ByteRegions.member _ entry).mpr
  exact ⟨⟨sites.data, storage sites signed relation x y⟩, by simp [regions], member⟩

theorem gap_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory) (position : Nat)
    (outside : ∀ region ∈ regions sites signed relation x y, position < region.start ∨ region.finish ≤ position) :
    image (entries sites signed relation x y) backing position = backing position := ByteRegions.image_frame _ _ _ outside

/-- Every byte outside the four complete regions, in any physical order. -/
@[expose] def Gap (sites : Sites) (signed : Bool) (relation : Relation) (position : Nat) : Prop :=
  (position < sites.stack ∨ sites.stack + 10 ≤ position) ∧
  (position < sites.start ∨ fallPC sites signed relation + 30 ≤ position) ∧
  (position < sites.taken ∨ sites.taken + 30 ≤ position) ∧
  (position < sites.data ∨ sites.data + 20 ≤ position)

theorem gap_outside (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (_valid : Valid sites signed relation) (position : Nat) (gap : Gap sites signed relation position) :
    ∀ region ∈ regions sites signed relation x y, position < region.start ∨ region.finish ≤ position := by
  intro region member
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa only [ByteRegions.Region.finish, stack_size] using gap.1
  · change position < sites.start ∨ sites.start + BytePacking.size (core sites signed relation) ≤ position
    rw [core_end]; exact gap.2.1
  · simpa only [ByteRegions.Region.finish, continuation, BranchLayout.continuation_size] using gap.2.2.1
  · simpa only [ByteRegions.Region.finish, storage_size] using gap.2.2.2

theorem initial_gap_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (valid : Valid sites signed relation) (position : Nat) (gap : Gap sites signed relation position) :
    image (entries sites signed relation x y) backing position = backing position :=
  gap_frame sites signed relation x y backing position (gap_outside sites signed relation x y valid position gap)

end SmcTuring.Appendix.SpacedLayout
