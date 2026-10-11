module
public import SmcTuring.Appendix.SpacedLayout

public section

namespace SmcTuring.Appendix.SpacedPrefix

open ByteImage SpacedLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

/-- The emitter's two input parameters are the actual initial byte words,
including for arbitrary backing bytes and arbitrary incoming registers/CF. -/
theorem initial_operands (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State) (valid : Valid sites signed relation)
    (initial : native.memory = image (entries sites signed relation x y) backing) :
    FieldRefinement.readField native (fields sites signed relation).x = x ∧
      FieldRefinement.readField native (fields sites signed relation).y = y := by
  have physical := field_layout sites signed relation x y valid
  constructor
  · let owner : Entry := ⟨xPC sites,
      .immediate .store (FieldRefinement.address (fields sites signed relation).x) x⟩
    have member : owner ∈ entries sites signed relation x y :=
      storage_placed sites signed relation x y owner (by simp [owner, storage, BytePacking.place])
    have exactBytes := image_packet _ backing (separated sites signed relation x y valid) owner member
    have bytes : Native.ByteMemory.bytesAt native.memory (xPC sites)
        (ByteCode.encode (.immediate .store (FieldRefinement.address (fields sites signed relation).x) x)).length =
        ByteCode.encode (.immediate .store (FieldRefinement.address (fields sites signed relation).x) x) := by
      rw [initial]; exact exactBytes
    have word := (immediate_words _ _ _ _ _ bytes).2
    rw [←word_at_read_field native _ (physical.fits _ (by simp [BranchExecution.fields]))]
    exact word
  · let owner : Entry := ⟨yPC sites,
      .immediate .store (FieldRefinement.address (fields sites signed relation).y) y⟩
    have member : owner ∈ entries sites signed relation x y :=
      storage_placed sites signed relation x y owner (by
        simp [owner, storage, BytePacking.place, Packet.initial, ByteCode.encode_length,
          ByteCode.instructionLength, yPC, xPC])
    have exactBytes := image_packet _ backing (separated sites signed relation x y valid) owner member
    have bytes : Native.ByteMemory.bytesAt native.memory (yPC sites)
        (ByteCode.encode (.immediate .store (FieldRefinement.address (fields sites signed relation).y) y)).length =
        ByteCode.encode (.immediate .store (FieldRefinement.address (fields sites signed relation).y) y) := by
      rw [initial]; exact exactBytes
    have word := (immediate_words _ _ _ _ _ bytes).2
    rw [←word_at_read_field native _ (physical.fits _ (by simp [BranchExecution.fields]))]
    exact word

theorem prefix_valid (sites : Sites) (signed : Bool) (relation : Relation)
    (valid : Valid sites signed relation) :
    prefixStart sites + ByteProgram.span (program sites signed relation) < 2 ^ 32 := by
  have full := valid.coreCapacity
  rw [span]
  simp only [endPC, fallPC, callPC, prefixEnd, andPC, prefixStart] at *
  omega

/-- Closed constructed current-byte prefix trace. Only one initial image,
its complete extent bound and its entry PC are execution premises. Every
operand/address/header/ownership/readiness fact is derived from the emitter. -/
theorem trace (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State)
    (valid : Valid sites signed relation)
    (initial : native.memory = image (entries sites signed relation x y) backing)
    (location : native.pc = FieldRefinement.address (prefixStart sites)) :
    ByteExecution.Trace native (FieldRefinement.forms (program sites signed relation) native)
      (FieldRefinement.run (program sites signed relation) native) := by
  have physical := field_layout sites signed relation x y valid
  apply ByteProgram.image_trace (entries sites signed relation x y) _ _ backing native
    (separated sites signed relation x y valid) initial (prefix_placed sites signed relation x y)
    (linked sites signed relation) _ (prefix_valid sites signed relation valid) _ location
  · intro instruction member field dependency
    exact physical.fits field (BranchExecution.relation_dependencies _ signed relation _ instruction member field dependency)
  · intro instruction member
    apply fields_owned sites signed relation x y
    exact BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)

theorem finish_pc (sites : Sites) (signed : Bool) (relation : Relation) (native : State)
    (location : native.pc = FieldRefinement.address (prefixStart sites)) :
    (FieldRefinement.run (program sites signed relation) native).pc = FieldRefinement.address (prefixEnd sites signed relation) := by
  rw [ByteProgram.run_pc _ _ _ location]
  have prefixSize := span sites signed relation
  change ByteProgram.span (program sites signed relation) = _ at prefixSize
  rw [prefixSize]
  simp only [prefixEnd, andPC, Nat.add_assoc]
  rfl

theorem displacement (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (valid : Valid sites signed relation) :
    FieldRefinement.readField (FieldRefinement.run (program sites signed relation) native)
      (fields sites signed relation).displacement =
      if BranchAlgebra.holds signed relation (FieldRefinement.readField native (fields sites signed relation).x)
        (FieldRefinement.readField native (fields sites signed relation).y) then delta sites signed relation else 0 :=
  BranchExecution.displacement _ _ _ _ native (field_layout sites signed relation x y valid) (separate_fields sites signed relation valid)

theorem initialized_displacement (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (backing : Memory) (native : State) (valid : Valid sites signed relation)
    (initial : native.memory = image (entries sites signed relation x y) backing) :
    FieldRefinement.readField (FieldRefinement.run (program sites signed relation) native)
      (fields sites signed relation).displacement =
      if BranchAlgebra.holds signed relation x y then delta sites signed relation else 0 := by
  rw [displacement sites signed relation x y native valid,
    (initial_operands sites signed relation x y backing native valid initial).1,
    (initial_operands sites signed relation x y backing native valid initial).2]

theorem accumulator (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (valid : Valid sites signed relation) :
    (FieldRefinement.run (program sites signed relation) native).accumulator = native.accumulator :=
  BranchExecution.accumulator _ _ _ _ native (field_layout sites signed relation x y valid) (separate_fields sites signed relation valid)

theorem stack (sites : Sites) (signed : Bool) (relation : Relation) (native : State) :
    (FieldRefinement.run (program sites signed relation) native).stack = native.stack := FieldRefinement.run_stack _ _

theorem carry (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (valid : Valid sites signed relation) :
    (FieldRefinement.run (program sites signed relation) native).carry = false :=
  BranchExecution.carry _ _ _ _ native (field_layout sites signed relation x y valid)

theorem byte_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (valid : Valid sites signed relation) (position : Nat)
    (outside : ∀ field ∈ [(fields sites signed relation).mask, (fields sites signed relation).displacement,
      (fields sites signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) :
    (FieldRefinement.run (program sites signed relation) native).memory position = native.memory position :=
  BranchExecution.restored_byte_frame _ _ _ _ native (field_layout sites signed relation x y valid)
    (separate_fields sites signed relation valid) position outside

/-- All code packets, including both continuation headers and DEFSTACK's
mutable address, retain their protected encoding invariant after the prefix. -/
theorem finish_intact (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (native : State) (valid : Valid sites signed relation)
    (intact : Intact (entries sites signed relation x y) native.memory) :
    Intact (entries sites signed relation x y) (FieldRefinement.run (program sites signed relation) native).memory := by
  have physical := full_layout sites signed relation x y valid
  have ownership : ∀ instruction ∈ program sites signed relation,
      Owned (entries sites signed relation x y) (Machine32.destination instruction) := by
    intro instruction member
    apply fields_owned sites signed relation x y
    exact BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)
  generalize program sites signed relation = code at ownership ⊢
  induction code generalizing native with
  | nil => exact intact
  | cons instruction rest ih =>
    refine ih (ByteExecution.execute (FieldRefinement.translate instruction native) native) ?_
      (fun next member => ownership next (by simp [member]))
    apply execute_intact _ native _ (separated sites signed relation x y valid) intact
    rw [FieldRefinement.translate_destination]
    have fieldIn : Machine32.destination instruction ∈ ownedFields sites signed relation := by
      rw [←image_fields sites signed relation x y]
      exact (BytePacking.fields_owned _ _).mpr (ownership instruction (by simp))
    have fit := physical.fits _ fieldIn
    rw [FieldRefinement.address_toNat _ fit]
    exact ownership instruction (by simp)

end SmcTuring.Appendix.SpacedPrefix
