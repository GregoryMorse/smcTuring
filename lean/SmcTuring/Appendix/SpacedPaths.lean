module
public import SmcTuring.Appendix.SpacedControl

public section

namespace SmcTuring.Appendix.SpacedPaths

open ByteImage SpacedLayout
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

/-- Fetch both tail instructions from the actual current image. XCHG precedes
reading CALL's own displacement; CALL's write is the real DEFSTACK address slot. -/
theorem tail_trace_intact (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (valid : Valid sites signed relation)
    (intact : Intact (entries sites signed relation x y) state.memory)
    (location : state.pc = FieldRefinement.address (prefixEnd sites signed relation))
    (top : ByteControl.load state.memory (SpacedControl.pointer sites) = SpacedControl.pointer sites) :
    ByteExecution.Trace state
      (ByteControl.tailForms (SpacedControl.pointer sites) (SpacedControl.displacement sites signed relation) state)
      (ByteControl.tail (SpacedControl.pointer sites) (SpacedControl.displacement sites signed relation) state) ∧
    Intact (entries sites signed relation x y)
      (ByteControl.tail (SpacedControl.pointer sites) (SpacedControl.displacement sites signed relation) state).memory := by
  let exchanged := ByteControl.exchangeStack (SpacedControl.pointer sites) state
  have layout := SpacedLayout.full_layout sites signed relation x y valid
  have pMember : sites.stack + 6 ∈ ownedFields sites signed relation := by simp [ownedFields]
  have aMember : sites.stack + 2 ∈ ownedFields sites signed relation := by simp [ownedFields]
  have pOwned : Owned (entries sites signed relation x y) (SpacedControl.pointer sites).toNat := by
    change Owned _ (FieldRefinement.address (sites.stack + 6)).toNat
    rw [FieldRefinement.address_toNat _ (layout.fits _ pMember)]
    exact SpacedLayout.field_owned sites signed relation x y _ pMember
  have exIntact : Intact (entries sites signed relation x y) exchanged.memory :=
    execute_intact _ state _ (separated sites signed relation x y valid) intact pOwned
  have exLocation : exchanged.pc = FieldRefinement.address (callPC sites signed relation) := by
    change (ByteControl.exchangeStack (SpacedControl.pointer sites) state).pc = _
    rw [ByteControl.exchange_stack_effect, location]
    exact BitVec.ofNat_add_ofNat _ _
  have slot : ByteExecution.destination (.callRelative (0 : Word)) exchanged = SpacedControl.address sites := by
    change BitVec.sub (ByteControl.exchangeStack (SpacedControl.pointer sites) state).stack 4 = _
    rw [ByteControl.exchange_stack_effect, top]
    exact SpacedControl.slot_alias sites
  have callOwned : ∀ value : Word, Owned (entries sites signed relation x y) (ByteExecution.destination (.callRelative value) exchanged).toNat := by
    intro value
    change Owned _ (BitVec.sub exchanged.stack 4).toNat
    change BitVec.sub exchanged.stack 4 = SpacedControl.address sites at slot
    rw [slot]
    change Owned _ (FieldRefinement.address (sites.stack + 2)).toNat
    rw [FieldRefinement.address_toNat _ (layout.fits _ aMember)]
    exact SpacedLayout.field_owned sites signed relation x y _ aMember
  have full := valid.coreCapacity
  have prefixFit : prefixEnd sites signed relation + 4 ≤ 2 ^ 32 := by
    simp only [fallPC, callPC] at *
    omega
  have callFit : callPC sites signed relation + 4 ≤ 2 ^ 32 := by
    simp only [fallPC] at *
    omega
  have firstMember : (⟨prefixEnd sites signed relation, .fixed (.memory .exchangeStack (SpacedControl.pointer sites))⟩ : Entry) ∈ entries sites signed relation x y :=
    tail_placed sites signed relation x y _ (by simp [tail, BranchLayout.tail, SpacedControl.pointer, BytePacking.place])
  have callMember : (⟨callPC sites signed relation, .relative 0⟩ : Entry) ∈ entries sites signed relation x y :=
    tail_placed sites signed relation x y _ (by
      simp [tail, BranchLayout.tail, BytePacking.place, Packet.initial, ByteCode.encode_length,
        ByteCode.instructionLength, ByteCode.MemoryOp.trailer, callPC])
  have firstFetch : ByteCode.fetch state.memory state.pc.toNat = some (.memory .exchangeStack (SpacedControl.pointer sites)) :=
    BranchPaths.fetched_current _ _ state intact firstMember prefixFit location
  have callFetch : ByteCode.fetch exchanged.memory exchanged.pc.toNat =
      some (.callRelative (ByteControl.load exchanged.memory (SpacedControl.displacement sites signed relation))) := by
    have fetched := BranchPaths.fetched_current _ _ exchanged exIntact callMember callFit exLocation
    have cFit := layout.fits (fields sites signed relation).displacement (by simp [ownedFields])
    have word := word_at_read_field exchanged (fields sites signed relation).displacement cFit
    change wordAt exchanged.memory (callPC sites signed relation + 1) =
      ByteControl.load exchanged.memory (SpacedControl.displacement sites signed relation) at word
    simpa only [current, word] using fetched
  constructor
  · exact .step firstFetch (.step callFetch (.nil _))
  · exact execute_intact _ exchanged _ (separated sites signed relation x y valid) exIntact (callOwned _)

end SmcTuring.Appendix.SpacedPaths
