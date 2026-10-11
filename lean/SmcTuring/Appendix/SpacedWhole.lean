module
public import SmcTuring.Appendix.SpacedPaths

public section

namespace SmcTuring.Appendix.SpacedWhole

open ByteImage SpacedLayout SpacedControl
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

@[expose] def selectedPC (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) : Nat :=
  if BranchAlgebra.holds signed relation x y then takenPC sites else fallPC sites signed relation
@[expose] def finishPC (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) : Nat :=
  selectedPC sites signed relation x y + 30
@[expose] def run (sites : Sites) (signed : Bool) (relation : Relation) (state : State) : State :=
  ByteControl.restore (pointer sites) (address sites)
    (ByteControl.tail (pointer sites) (SpacedControl.displacement sites signed relation)
      (FieldRefinement.run (program sites signed relation) state))
@[expose] def forms (sites : Sites) (signed : Bool) (relation : Relation) (state : State) : List ByteCode.Form :=
  FieldRefinement.forms (program sites signed relation) state ++
    ByteControl.tailForms (pointer sites) (SpacedControl.displacement sites signed relation)
      (FieldRefinement.run (program sites signed relation) state) ++ ByteControl.restoreForms (pointer sites) (address sites)

theorem run_forms (sites : Sites) (signed : Bool) (relation : Relation) (state : State) :
    ByteExecution.run (forms sites signed relation state) state = run sites signed relation state := by
  simp only [forms, ByteExecution.run_append, FieldRefinement.forms_run, ByteControl.tail_run, ByteControl.restore_run, run]

theorem tail_pc (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart sites)) :
    (ByteControl.tail (pointer sites) (SpacedControl.displacement sites signed relation)
      (FieldRefinement.run (program sites signed relation) state)).pc =
      FieldRefinement.address (selectedPC sites signed relation x y) := by
  have effect := congrArg Native.Execution.State.pc
    (ByteControl.tail_effect (pointer sites) (SpacedControl.displacement sites signed relation)
      (FieldRefinement.run (program sites signed relation) state) (call_apart sites signed relation x y valid))
  have value := SpacedPrefix.initialized_displacement sites signed relation x y backing state valid initial
  change ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory
    (SpacedControl.displacement sites signed relation) = _ at value
  change _ = BitVec.add (BitVec.add (FieldRefinement.run (program sites signed relation) state).pc 11)
    (ByteControl.load (FieldRefinement.run (program sites signed relation) state).memory
      (SpacedControl.displacement sites signed relation)) at effect
  rw [effect, value, SpacedPrefix.finish_pc sites signed relation state location]
  have next : BitVec.add (FieldRefinement.address (prefixEnd sites signed relation)) (BitVec.ofNat 32 11) =
      FieldRefinement.address (fallPC sites signed relation) := BitVec.ofNat_add_ofNat _ _
  change BitVec.add (BitVec.add (FieldRefinement.address (prefixEnd sites signed relation)) (BitVec.ofNat 32 11))
    (if BranchAlgebra.holds signed relation x y then delta sites signed relation else (0 : Word)) =
      FieldRefinement.address (selectedPC sites signed relation x y)
  rw [next]
  by_cases holds : BranchAlgebra.holds signed relation x y
  · simp only [selectedPC, ite_eq_left holds, delta]
    change FieldRefinement.address (fallPC sites signed relation) +
      (FieldRefinement.address (takenPC sites) - FieldRefinement.address (fallPC sites signed relation)) =
        FieldRefinement.address (takenPC sites)
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  · simp [holds, selectedPC]

/-- Whole byte memory after the continuation equals the PREFIX result, rather
than a fresh initializer or a word-only projection. -/
theorem restored (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    run sites signed relation state =
      { FieldRefinement.run (program sites signed relation) state with
        pc := BitVec.add (ByteControl.tail (pointer sites) (SpacedControl.displacement sites signed relation)
          (FieldRefinement.run (program sites signed relation) state)).pc 30, carry := false } := by
  have slots := prefix_stack sites signed relation x y backing state valid initial
  exact ByteControl.continued_alias (pointer sites) (SpacedControl.displacement sites signed relation) (address sites)
    _ (call_apart sites signed relation x y valid) (slot_apart sites signed relation x y valid)
    slots.1 (slot_alias sites) slots.2 (pointer_nonwrap sites signed relation x y valid)

theorem finish_pc (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart sites)) :
    (run sites signed relation state).pc = FieldRefinement.address (finishPC sites signed relation x y) := by
  rw [restored sites signed relation x y backing state valid initial,
    tail_pc sites signed relation x y backing state valid initial location]
  change BitVec.add (FieldRefinement.address (selectedPC sites signed relation x y)) (BitVec.ofNat 32 30) =
    FieldRefinement.address (finishPC sites signed relation x y)
  exact BitVec.ofNat_add_ofNat _ _

theorem accumulator (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    (run sites signed relation state).accumulator = state.accumulator := by
  rw [restored sites signed relation x y backing state valid initial]
  exact SpacedPrefix.accumulator sites signed relation x y state valid

theorem stack (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    (run sites signed relation state).stack = state.stack := by
  rw [restored sites signed relation x y backing state valid initial]
  exact SpacedPrefix.stack sites signed relation state

theorem carry (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    (run sites signed relation state).carry = false := by
  rw [restored sites signed relation x y backing state valid initial]

theorem byte_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) (position : Nat)
    (outside : ∀ field ∈ [(fields sites signed relation).mask, (fields sites signed relation).displacement,
      (fields sites signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) :
    (run sites signed relation state).memory position = state.memory position := by
  rw [restored sites signed relation x y backing state valid initial]
  exact SpacedPrefix.byte_frame sites signed relation x y state valid position outside

theorem continuation_ownership (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (valid : Valid sites signed relation) :
    ∀ form ∈ ByteControl.restoreForms (pointer sites) (address sites), ∀ state : State,
      Owned (entries sites signed relation x y) (ByteExecution.destination form state).toNat := by
  have layout := full_layout sites signed relation x y valid
  have pFit := layout.fits (sites.stack + 6) (by simp [ownedFields])
  have aFit := layout.fits (sites.stack + 2) (by simp [ownedFields])
  intro form member state
  change form ∈ [.memory .exchangeStack (FieldRefinement.address (sites.stack + 6)),
    .memory .addFour (FieldRefinement.address (sites.stack + 6)), .memory .exchangeAcc (FieldRefinement.address (sites.stack + 6)),
    .storeAcc (FieldRefinement.address (sites.stack + 2)), .memory .exchangeAcc (FieldRefinement.address (sites.stack + 6))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [ByteExecution.destination, FieldRefinement.address_toNat _ pFit, FieldRefinement.address_toNat _ aFit]
    apply field_owned sites signed relation x y
    simp [ownedFields]

theorem continuation_straight (sites : Sites) :
    ∀ form ∈ ByteControl.restoreForms (pointer sites) (address sites), ByteLinear.Straight form := by
  intro form member
  change form ∈ [.memory .exchangeStack (FieldRefinement.address (sites.stack + 6)),
    .memory .addFour (FieldRefinement.address (sites.stack + 6)), .memory .exchangeAcc (FieldRefinement.address (sites.stack + 6)),
    .storeAcc (FieldRefinement.address (sites.stack + 2)), .memory .exchangeAcc (FieldRefinement.address (sites.stack + 6))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem continuation_span (sites : Sites) : ByteLinear.span (ByteControl.restoreForms (pointer sites) (address sites)) = 30 := rfl

theorem continuation_trace (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (valid : Valid sites signed relation)
    (intact : Intact (entries sites signed relation x y) state.memory)
    (location : state.pc = FieldRefinement.address (selectedPC sites signed relation x y)) :
    ByteExecution.Trace state (ByteControl.restoreForms (pointer sites) (address sites))
      (ByteControl.restore (pointer sites) (address sites) state) := by
  rw [←ByteControl.restore_run]
  apply ByteLinear.constructed_trace _ _ (selectedPC sites signed relation x y) state
    (separated sites signed relation x y valid) intact _ (continuation_straight sites) _
    (continuation_ownership sites signed relation x y valid) location
  · change ∀ entry ∈ BytePacking.place (selectedPC sites signed relation x y) (continuation sites),
      entry ∈ entries sites signed relation x y
    by_cases holds : BranchAlgebra.holds signed relation x y
    · simpa only [selectedPC, ite_eq_left holds] using SpacedLayout.taken_placed sites signed relation x y
    · simpa only [selectedPC, ite_eq_right holds] using SpacedLayout.fall_placed sites signed relation x y
  · have coreFit := valid.coreCapacity
    have takenFit := valid.takenCapacity
    rw [continuation_span]
    simp only [selectedPC]
    split
    · exact takenFit
    · exact coreFit

/-- One independently spaced initializer supplies ALL fetches through prefix, CALL and the selected
continuation. The only execution premises are image, entry and finite valid. -/
theorem trace (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart sites)) :
    ByteExecution.Trace state (forms sites signed relation state) (run sites signed relation state) := by
  have initialized : Intact (entries sites signed relation x y) state.memory := by
    rw [initial]
    exact initial_intact sites signed relation x y backing valid
  have tail := SpacedPaths.tail_trace_intact sites signed relation x y _ valid
    (SpacedPrefix.finish_intact sites signed relation x y state valid initialized)
    (SpacedPrefix.finish_pc sites signed relation state location)
    (prefix_stack sites signed relation x y backing state valid initial).1
  exact ByteExecution.trace_append
    (ByteExecution.trace_append (SpacedPrefix.trace sites signed relation x y backing state valid initial location) tail.1)
    (continuation_trace sites signed relation x y _ valid tail.2
      (tail_pc sites signed relation x y backing state valid initial location))

theorem tail_owned_run (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (valid : Valid sites signed relation)
    (top : ByteControl.load state.memory (pointer sites) = pointer sites) :
    ByteExecution.OwnedRun (fun word => Owned (entries sites signed relation x y) word.toNat)
      (ByteControl.tailForms (pointer sites) (SpacedControl.displacement sites signed relation) state) state := by
  have layout := full_layout sites signed relation x y valid
  have pFit := layout.fits (sites.stack + 6) (by simp [ownedFields])
  have aFit := layout.fits (sites.stack + 2) (by simp [ownedFields])
  constructor
  · change Owned _ (FieldRefinement.address (sites.stack + 6)).toNat
    rw [FieldRefinement.address_toNat _ pFit]
    exact field_owned sites signed relation x y _ (by simp [ownedFields])
  · constructor
    · change Owned _ (BitVec.sub (ByteControl.exchangeStack (pointer sites) state).stack 4).toNat
      rw [ByteControl.exchange_stack_effect, top, slot_alias]
      change Owned _ (FieldRefinement.address (sites.stack + 2)).toNat
      rw [FieldRefinement.address_toNat _ aFit]
      exact field_owned sites signed relation x y _ (by simp [ownedFields])
    · trivial

theorem owned_run (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    ByteExecution.OwnedRun (fun word => Owned (entries sites signed relation x y) word.toNat)
      (forms sites signed relation state) state := by
  have layout := SpacedLayout.field_layout sites signed relation x y valid
  have prefixOwned : ByteExecution.OwnedRun (fun word => Owned (entries sites signed relation x y) word.toNat)
      (FieldRefinement.forms (program sites signed relation) state) state := by
    apply FieldRefinement.owned_run
    intro instruction member
    have dependency := BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)
    rw [FieldRefinement.address_toNat _ (layout.fits _ dependency)]
    exact fields_owned sites signed relation x y _ dependency
  unfold forms
  rw [ByteExecution.owned_append, ByteExecution.owned_append, FieldRefinement.forms_run,
    ByteExecution.run_append, FieldRefinement.forms_run, ByteControl.tail_run]
  exact ⟨⟨prefixOwned, tail_owned_run sites signed relation x y _ valid
    (prefix_stack sites signed relation x y backing state valid initial).1⟩,
    ByteLinear.owned_run _ _ _ (continuation_ownership sites signed relation x y valid)⟩

theorem finish_intact (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing) :
    Intact (entries sites signed relation x y) (run sites signed relation state).memory := by
  rw [restored sites signed relation x y backing state valid initial]
  apply SpacedPrefix.finish_intact sites signed relation x y state valid
  rw [initial]
  exact initial_intact sites signed relation x y backing valid

/-- Closed independently spaced branch certificate for arbitrary backing bytes, incoming
registers/CF and all 32-bit inputs. The endpoint is an observation boundary,
not a halt theorem or a physical hardware instruction-fetch claim. -/
theorem correct (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart sites)) :
    ByteExecution.Trace state (forms sites signed relation state) (run sites signed relation state) ∧
    (run sites signed relation state).pc = FieldRefinement.address (finishPC sites signed relation x y) ∧
    (run sites signed relation state).accumulator = state.accumulator ∧
    (run sites signed relation state).stack = state.stack ∧
    (run sites signed relation state).carry = false ∧
    ByteExecution.OwnedRun (fun word => Owned (entries sites signed relation x y) word.toNat)
      (forms sites signed relation state) state ∧
    Intact (entries sites signed relation x y) (run sites signed relation state).memory ∧
    (∀ position, (∀ field ∈ [(fields sites signed relation).mask, (fields sites signed relation).displacement,
      (fields sites signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) →
      (run sites signed relation state).memory position = state.memory position) :=
  ⟨trace sites signed relation x y backing state valid initial location,
   finish_pc sites signed relation x y backing state valid initial location,
   accumulator sites signed relation x y backing state valid initial,
   stack sites signed relation x y backing state valid initial,
   carry sites signed relation x y backing state valid initial,
   owned_run sites signed relation x y backing state valid initial,
   finish_intact sites signed relation x y backing state valid initial,
   byte_frame sites signed relation x y backing state valid initial⟩

theorem gap_frame (sites : Sites) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (valid : Valid sites signed relation)
    (initial : state.memory = image (entries sites signed relation x y) backing)
    (position : Nat) (gap : Gap sites signed relation position) :
    (run sites signed relation state).memory position = backing position := by
  rw [byte_frame sites signed relation x y backing state valid initial position (by
    intro field member
    apply ByteRegions.outside_owned (regions sites signed relation x y) position
      (gap_outside sites signed relation x y valid position gap) field
    apply field_owned sites signed relation x y
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [ownedFields, List.mem_cons, List.not_mem_nil, or_false]
    tauto), initial]
  exact initial_gap_frame sites signed relation x y backing valid position gap

end SmcTuring.Appendix.SpacedWhole
