module
public import SmcTuring.Appendix.BranchControl

public section

namespace SmcTuring.Appendix.BranchPaths

open ByteImage BranchLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

theorem tail_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (prefixEnd base signed relation) (BranchLayout.tail base),
      entry ∈ entries base signed relation x y := by
  have prefixSize : BytePacking.size ((program base signed relation).map ByteProgram.packet) = leading signed relation + 20 := span _ _ _ _
  have stackSize : BytePacking.size [BranchLayout.stack base] = 10 := by
    simp [BytePacking.size, BranchLayout.stack, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  intro entry member
  unfold entries
  simp only [packets, BytePacking.place_append, List.mem_append]
  left; left; left; right
  simpa only [BytePacking.size_append, prefixSize, stackSize, prefixEnd, andPC, prefixStart, Nat.add_assoc] using member

theorem fall_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (fallPC base signed relation) (continuation base),
      entry ∈ entries base signed relation x y := by
  have prefixSize : BytePacking.size ((program base signed relation).map ByteProgram.packet) = leading signed relation + 20 := span _ _ _ _
  have stackSize : BytePacking.size [BranchLayout.stack base] = 10 := by
    simp [BytePacking.size, BranchLayout.stack, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  intro entry member
  unfold entries
  simp only [packets, BytePacking.place_append, List.mem_append]
  left; left; right
  simpa only [BytePacking.size_append, prefixSize, tail_size, stackSize, fallPC, callPC, prefixEnd, andPC, prefixStart, Nat.add_assoc] using member

theorem taken_placed (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    ∀ entry ∈ BytePacking.place (takenPC base signed relation) (continuation base),
      entry ∈ entries base signed relation x y := by
  have prefixSize : BytePacking.size ((program base signed relation).map ByteProgram.packet) = leading signed relation + 20 := span _ _ _ _
  have stackSize : BytePacking.size [BranchLayout.stack base] = 10 := by
    simp [BytePacking.size, BranchLayout.stack, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  intro entry member
  unfold entries
  simp only [packets, BytePacking.place_append, List.mem_append]
  left; right
  simpa only [BytePacking.size_append, prefixSize, tail_size, continuation_size, stackSize,
    takenPC, fallPC, callPC, prefixEnd, andPC, prefixStart, Nat.add_assoc] using member

theorem fetched_current (whole : List Entry) (entry : Entry) (state : State)
    (intact : Intact whole state.memory) (member : entry ∈ whole)
    (fit : entry.pc + 4 ≤ 2 ^ 32) (location : state.pc = FieldRefinement.address entry.pc) :
    ByteCode.fetch state.memory state.pc.toNat = some (current entry state.memory) := by
  rw [location]
  change ByteCode.fetch state.memory (FieldRefinement.address entry.pc).toNat = _
  rw [FieldRefinement.address_toNat entry.pc fit]
  exact fetch_current entry state.memory (intact entry member)

/-- Fetch both tail instructions from the actual current image. XCHG precedes
reading CALL's own displacement; CALL's write is the real DEFSTACK address slot. -/
theorem tail_trace_intact (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (intact : Intact (entries base signed relation x y) state.memory)
    (location : state.pc = FieldRefinement.address (prefixEnd base signed relation))
    (top : ByteControl.load state.memory (BranchControl.pointer base) = BranchControl.pointer base) :
    ByteExecution.Trace state
      (ByteControl.tailForms (BranchControl.pointer base) (BranchControl.displacement base signed relation) state)
      (ByteControl.tail (BranchControl.pointer base) (BranchControl.displacement base signed relation) state) ∧
    Intact (entries base signed relation x y)
      (ByteControl.tail (BranchControl.pointer base) (BranchControl.displacement base signed relation) state).memory := by
  let exchanged := ByteControl.exchangeStack (BranchControl.pointer base) state
  have layout := BranchControl.full_layout base signed relation x y capacity
  have pMember : base + 6 ∈ ownedFields base signed relation := by simp [ownedFields]
  have aMember : base + 2 ∈ ownedFields base signed relation := by simp [ownedFields]
  have pOwned : Owned (entries base signed relation x y) (BranchControl.pointer base).toNat := by
    change Owned _ (FieldRefinement.address (base + 6)).toNat
    rw [FieldRefinement.address_toNat _ (layout.fits _ pMember)]
    exact BranchControl.field_owned base signed relation x y _ pMember
  have exIntact : Intact (entries base signed relation x y) exchanged.memory :=
    execute_intact _ state _ (BytePacking.placed_separated _ _) intact pOwned
  have exLocation : exchanged.pc = FieldRefinement.address (callPC base signed relation) := by
    change (ByteControl.exchangeStack (BranchControl.pointer base) state).pc = _
    rw [ByteControl.exchange_stack_effect, location]
    exact BitVec.ofNat_add_ofNat _ _
  have slot : ByteExecution.destination (.callRelative (0 : Word)) exchanged = BranchControl.address base := by
    change BitVec.sub (ByteControl.exchangeStack (BranchControl.pointer base) state).stack 4 = _
    rw [ByteControl.exchange_stack_effect, top]
    exact BranchControl.slot_alias base
  have callOwned : ∀ value : Word, Owned (entries base signed relation x y) (ByteExecution.destination (.callRelative value) exchanged).toNat := by
    intro value
    change Owned _ (BitVec.sub exchanged.stack 4).toNat
    change BitVec.sub exchanged.stack 4 = BranchControl.address base at slot
    rw [slot]
    change Owned _ (FieldRefinement.address (base + 2)).toNat
    rw [FieldRefinement.address_toNat _ (layout.fits _ aMember)]
    exact BranchControl.field_owned base signed relation x y _ aMember
  have prefixFit : prefixEnd base signed relation + 4 ≤ 2 ^ 32 := by
    simp only [endPC, yPC, xPC, takenPC, fallPC, callPC] at capacity
    omega
  have callFit : callPC base signed relation + 4 ≤ 2 ^ 32 := by
    simp only [endPC, yPC, xPC, takenPC, fallPC] at capacity
    omega
  have firstMember : (⟨prefixEnd base signed relation, .fixed (.memory .exchangeStack (BranchControl.pointer base))⟩ : Entry) ∈ entries base signed relation x y :=
    tail_placed base signed relation x y _ (by simp [BranchLayout.tail, BranchControl.pointer, BytePacking.place])
  have callMember : (⟨callPC base signed relation, .relative 0⟩ : Entry) ∈ entries base signed relation x y :=
    tail_placed base signed relation x y _ (by
      simp [BranchLayout.tail, BytePacking.place, Packet.initial, ByteCode.encode_length,
        ByteCode.instructionLength, ByteCode.MemoryOp.trailer, callPC])
  have firstFetch : ByteCode.fetch state.memory state.pc.toNat = some (.memory .exchangeStack (BranchControl.pointer base)) :=
    fetched_current _ _ state intact firstMember prefixFit location
  have callFetch : ByteCode.fetch exchanged.memory exchanged.pc.toNat =
      some (.callRelative (ByteControl.load exchanged.memory (BranchControl.displacement base signed relation))) := by
    have fetched := fetched_current _ _ exchanged exIntact callMember callFit exLocation
    have cFit := layout.fits (fields base signed relation).displacement (by simp [ownedFields])
    have word := word_at_read_field exchanged (fields base signed relation).displacement cFit
    change wordAt exchanged.memory (callPC base signed relation + 1) =
      ByteControl.load exchanged.memory (BranchControl.displacement base signed relation) at word
    simpa only [current, word] using fetched
  constructor
  · exact .step firstFetch (.step callFetch (.nil _))
  · exact execute_intact _ exchanged _ (BytePacking.placed_separated _ _) exIntact (callOwned _)

end SmcTuring.Appendix.BranchPaths
