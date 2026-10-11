module
public import SmcTuring.Appendix.BranchLayout

public section

namespace SmcTuring.Appendix.BranchPrefix

open ByteImage BranchLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

/-- The literal prefix fragment is present at the computed entry coordinate. -/
theorem prefix_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ ByteProgram.entries (prefixStart base) (program base signed relation),
      entry ∈ entries base signed relation x y := by
  intro entry member
  unfold entries
  simp only [packets, BytePacking.place_append, List.mem_append]
  left; left; left; left; right
  simpa only [ByteProgram.entries, prefixStart, BytePacking.size, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, stack, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength,
    Nat.add_zero] using member

theorem storage_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (xPC base signed relation) (storage base signed relation x y),
      entry ∈ entries base signed relation x y := by
  let core := [BranchLayout.stack base] ++ (program base signed relation).map ByteProgram.packet ++ tail base ++
    continuation base ++ continuation base
  have total := image_end base signed relation x y
  change base + BytePacking.size (core ++ storage base signed relation x y) = endPC base signed relation at total
  rw [BytePacking.size_append] at total
  have storeSize : BytePacking.size (storage base signed relation x y) = 20 := by
    simp [storage, BytePacking.size, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  rw [storeSize] at total
  have atX : base + BytePacking.size core = xPC base signed relation := by
    simp only [endPC, yPC] at total
    omega
  intro entry member
  change entry ∈ BytePacking.place base (core ++ storage base signed relation x y)
  rw [BytePacking.place_append, atX]
  exact List.mem_append_right _ member

/-- The emitter's two input parameters are the actual initial byte words,
including for arbitrary backing bytes and arbitrary incoming registers/CF. -/
theorem initial_operands (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : native.memory = image (entries base signed relation x y) backing) :
    FieldRefinement.readField native (fields base signed relation).x = x ∧
      FieldRefinement.readField native (fields base signed relation).y = y := by
  have physical := field_layout base signed relation x y capacity
  constructor
  · let owner : Entry := ⟨xPC base signed relation,
      .immediate .store (FieldRefinement.address (fields base signed relation).x) x⟩
    have member : owner ∈ entries base signed relation x y :=
      storage_placed base signed relation x y owner (by simp [owner, storage, BytePacking.place])
    have exactBytes := image_packet _ backing (BytePacking.placed_separated _ _) owner member
    have bytes : Native.ByteMemory.bytesAt native.memory (xPC base signed relation)
        (ByteCode.encode (.immediate .store (FieldRefinement.address (fields base signed relation).x) x)).length =
        ByteCode.encode (.immediate .store (FieldRefinement.address (fields base signed relation).x) x) := by
      rw [initial]; exact exactBytes
    have word := (immediate_words _ _ _ _ _ bytes).2
    rw [←word_at_read_field native _ (physical.fits _ (by simp [BranchExecution.fields]))]
    exact word
  · let owner : Entry := ⟨yPC base signed relation,
      .immediate .store (FieldRefinement.address (fields base signed relation).y) y⟩
    have member : owner ∈ entries base signed relation x y :=
      storage_placed base signed relation x y owner (by
        simp [owner, storage, BytePacking.place, Packet.initial, ByteCode.encode_length,
          ByteCode.instructionLength, yPC])
    have exactBytes := image_packet _ backing (BytePacking.placed_separated _ _) owner member
    have bytes : Native.ByteMemory.bytesAt native.memory (yPC base signed relation)
        (ByteCode.encode (.immediate .store (FieldRefinement.address (fields base signed relation).y) y)).length =
        ByteCode.encode (.immediate .store (FieldRefinement.address (fields base signed relation).y) y) := by
      rw [initial]; exact exactBytes
    have word := (immediate_words _ _ _ _ _ bytes).2
    rw [←word_at_read_field native _ (physical.fits _ (by simp [BranchExecution.fields]))]
    exact word

theorem prefix_capacity (base : Nat) (signed : Bool) (relation : Relation)
    (capacity : endPC base signed relation ≤ 2 ^ 32) :
    prefixStart base + ByteProgram.span (program base signed relation) < 2 ^ 32 := by
  have prefixSize := span (fields base signed relation) signed relation (delta base signed relation)
  change ByteProgram.span (program base signed relation) = _ at prefixSize
  rw [prefixSize]
  simp only [endPC, yPC, xPC, takenPC, fallPC, callPC, prefixEnd, andPC] at capacity
  omega

/-- Closed constructed current-byte prefix trace. Only one initial image,
its complete extent bound and its entry PC are execution premises. Every
operand/address/header/ownership/readiness fact is derived from the emitter. -/
theorem trace (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State)
    (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : native.memory = image (entries base signed relation x y) backing)
    (location : native.pc = FieldRefinement.address (prefixStart base)) :
    ByteExecution.Trace native (FieldRefinement.forms (program base signed relation) native)
      (FieldRefinement.run (program base signed relation) native) := by
  have physical := field_layout base signed relation x y capacity
  apply ByteProgram.image_trace (entries base signed relation x y) _ _ backing native
    (BytePacking.placed_separated _ _) initial (prefix_placed base signed relation x y)
    (linked base signed relation) _ (prefix_capacity base signed relation capacity) _ location
  · intro instruction member field dependency
    exact physical.fits field (BranchExecution.relation_dependencies _ signed relation _ instruction member field dependency)
  · intro instruction member
    apply fields_owned base signed relation x y
    exact BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)

theorem finish_pc (base : Nat) (signed : Bool) (relation : Relation) (native : State)
    (location : native.pc = FieldRefinement.address (prefixStart base)) :
    (FieldRefinement.run (program base signed relation) native).pc = FieldRefinement.address (prefixEnd base signed relation) := by
  rw [ByteProgram.run_pc _ _ _ location]
  have prefixSize := span (fields base signed relation) signed relation (delta base signed relation)
  change ByteProgram.span (program base signed relation) = _ at prefixSize
  rw [prefixSize]
  simp only [prefixEnd, andPC, Nat.add_assoc]
  rfl

theorem displacement (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32) :
    FieldRefinement.readField (FieldRefinement.run (program base signed relation) native)
      (fields base signed relation).displacement =
      if BranchAlgebra.holds signed relation (FieldRefinement.readField native (fields base signed relation).x)
        (FieldRefinement.readField native (fields base signed relation).y) then delta base signed relation else 0 :=
  BranchExecution.displacement _ _ _ _ native (field_layout base signed relation x y capacity) (separate_fields base signed relation)

theorem initialized_displacement (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : native.memory = image (entries base signed relation x y) backing) :
    FieldRefinement.readField (FieldRefinement.run (program base signed relation) native)
      (fields base signed relation).displacement =
      if BranchAlgebra.holds signed relation x y then delta base signed relation else 0 := by
  rw [displacement base signed relation x y native capacity,
    (initial_operands base signed relation x y backing native capacity initial).1,
    (initial_operands base signed relation x y backing native capacity initial).2]

theorem accumulator (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32) :
    (FieldRefinement.run (program base signed relation) native).accumulator = native.accumulator :=
  BranchExecution.accumulator _ _ _ _ native (field_layout base signed relation x y capacity) (separate_fields base signed relation)

theorem stack (base : Nat) (signed : Bool) (relation : Relation) (native : State) :
    (FieldRefinement.run (program base signed relation) native).stack = native.stack := FieldRefinement.run_stack _ _

theorem carry (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32) :
    (FieldRefinement.run (program base signed relation) native).carry = false :=
  BranchExecution.carry _ _ _ _ native (field_layout base signed relation x y capacity)

theorem byte_frame (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32) (position : Nat)
    (outside : ∀ field ∈ [(fields base signed relation).mask, (fields base signed relation).displacement,
      (fields base signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) :
    (FieldRefinement.run (program base signed relation) native).memory position = native.memory position :=
  BranchExecution.restored_byte_frame _ _ _ _ native (field_layout base signed relation x y capacity)
    (separate_fields base signed relation) position outside

/-- All code packets, including both continuation headers and DEFSTACK's
mutable address, retain their protected encoding invariant after the prefix. -/
theorem finish_intact (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (intact : Intact (entries base signed relation x y) native.memory) :
    Intact (entries base signed relation x y) (FieldRefinement.run (program base signed relation) native).memory := by
  have physical := BytePacking.placed_field_layout (packets base signed relation x y) base
    ((image_end base signed relation x y).trans_le capacity)
  have ownership : ∀ instruction ∈ program base signed relation,
      Owned (entries base signed relation x y) (Machine32.destination instruction) := by
    intro instruction member
    apply fields_owned base signed relation x y
    exact BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)
  generalize program base signed relation = code at ownership ⊢
  induction code generalizing native with
  | nil => exact intact
  | cons instruction rest ih =>
    refine ih (ByteExecution.execute (FieldRefinement.translate instruction native) native) ?_
      (fun next member => ownership next (by simp [member]))
    apply execute_intact _ native _ (BytePacking.placed_separated _ _) intact
    rw [FieldRefinement.translate_destination]
    have fit := physical.fits _ ((BytePacking.fields_owned _ _).mpr (ownership instruction (by simp)))
    rw [FieldRefinement.address_toNat _ fit]
    exact ownership instruction (by simp)

end SmcTuring.Appendix.BranchPrefix
