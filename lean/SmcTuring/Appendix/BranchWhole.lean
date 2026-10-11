module
public import SmcTuring.Appendix.BranchPaths

public section

namespace SmcTuring.Appendix.BranchWhole

open ByteImage BranchLayout BranchControl
abbrev State := ByteExecution.State
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

@[expose] def selectedPC (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) : Nat :=
  if BranchAlgebra.holds signed relation x y then takenPC base signed relation else fallPC base signed relation
@[expose] def finishPC (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) : Nat :=
  if BranchAlgebra.holds signed relation x y then xPC base signed relation else takenPC base signed relation
@[expose] def run (base : Nat) (signed : Bool) (relation : Relation) (state : State) : State :=
  ByteControl.restore (pointer base) (address base)
    (ByteControl.tail (pointer base) (BranchControl.displacement base signed relation)
      (FieldRefinement.run (program base signed relation) state))
@[expose] def forms (base : Nat) (signed : Bool) (relation : Relation) (state : State) : List ByteCode.Form :=
  FieldRefinement.forms (program base signed relation) state ++
    ByteControl.tailForms (pointer base) (BranchControl.displacement base signed relation)
      (FieldRefinement.run (program base signed relation) state) ++ ByteControl.restoreForms (pointer base) (address base)

theorem run_forms (base : Nat) (signed : Bool) (relation : Relation) (state : State) :
    ByteExecution.run (forms base signed relation state) state = run base signed relation state := by
  simp only [forms, ByteExecution.run_append, FieldRefinement.forms_run, ByteControl.tail_run, ByteControl.restore_run, run]

theorem tail_pc (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart base)) :
    (ByteControl.tail (pointer base) (BranchControl.displacement base signed relation)
      (FieldRefinement.run (program base signed relation) state)).pc =
      FieldRefinement.address (selectedPC base signed relation x y) := by
  have effect := congrArg Native.Execution.State.pc
    (ByteControl.tail_effect (pointer base) (BranchControl.displacement base signed relation)
      (FieldRefinement.run (program base signed relation) state) (call_apart base signed relation x y capacity))
  have value := BranchPrefix.initialized_displacement base signed relation x y backing state capacity initial
  change ByteControl.load (FieldRefinement.run (program base signed relation) state).memory
    (BranchControl.displacement base signed relation) = _ at value
  change _ = BitVec.add (BitVec.add (FieldRefinement.run (program base signed relation) state).pc 11)
    (ByteControl.load (FieldRefinement.run (program base signed relation) state).memory
      (BranchControl.displacement base signed relation)) at effect
  rw [effect, value, BranchPrefix.finish_pc base signed relation state location]
  have next : BitVec.add (FieldRefinement.address (prefixEnd base signed relation)) (BitVec.ofNat 32 11) =
      FieldRefinement.address (fallPC base signed relation) := BitVec.ofNat_add_ofNat _ _
  change BitVec.add (BitVec.add (FieldRefinement.address (prefixEnd base signed relation)) (BitVec.ofNat 32 11))
    (if BranchAlgebra.holds signed relation x y then delta base signed relation else (0 : Word)) =
      FieldRefinement.address (selectedPC base signed relation x y)
  rw [next]
  by_cases holds : BranchAlgebra.holds signed relation x y
  · simp only [selectedPC, ite_eq_left holds, delta]
    change FieldRefinement.address (fallPC base signed relation) +
      (FieldRefinement.address (takenPC base signed relation) - FieldRefinement.address (fallPC base signed relation)) =
        FieldRefinement.address (takenPC base signed relation)
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  · simp [holds, selectedPC]

/-- Whole byte memory after the continuation equals the PREFIX result, rather
than a fresh initializer or a word-only projection. -/
theorem restored (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    run base signed relation state =
      { FieldRefinement.run (program base signed relation) state with
        pc := BitVec.add (ByteControl.tail (pointer base) (BranchControl.displacement base signed relation)
          (FieldRefinement.run (program base signed relation) state)).pc 30, carry := false } := by
  have slots := prefix_stack base signed relation x y backing state capacity initial
  exact ByteControl.continued_alias (pointer base) (BranchControl.displacement base signed relation) (address base)
    _ (call_apart base signed relation x y capacity) (slot_apart base signed relation x y capacity)
    slots.1 (slot_alias base) slots.2 (pointer_nonwrap base signed relation x y capacity)

theorem finish_pc (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart base)) :
    (run base signed relation state).pc = FieldRefinement.address (finishPC base signed relation x y) := by
  rw [restored base signed relation x y backing state capacity initial,
    tail_pc base signed relation x y backing state capacity initial location]
  change BitVec.add (FieldRefinement.address (selectedPC base signed relation x y)) (BitVec.ofNat 32 30) =
    FieldRefinement.address (finishPC base signed relation x y)
  by_cases holds : BranchAlgebra.holds signed relation x y
  · simp only [finishPC, selectedPC, ite_eq_left holds]
    exact BitVec.ofNat_add_ofNat _ _
  · simp only [finishPC, selectedPC, ite_eq_right holds]
    exact BitVec.ofNat_add_ofNat _ _

theorem accumulator (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    (run base signed relation state).accumulator = state.accumulator := by
  rw [restored base signed relation x y backing state capacity initial]
  exact BranchPrefix.accumulator base signed relation x y state capacity

theorem stack (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    (run base signed relation state).stack = state.stack := by
  rw [restored base signed relation x y backing state capacity initial]
  exact BranchPrefix.stack base signed relation state

theorem carry (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    (run base signed relation state).carry = false := by
  rw [restored base signed relation x y backing state capacity initial]

theorem byte_frame (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) (position : Nat)
    (outside : ∀ field ∈ [(fields base signed relation).mask, (fields base signed relation).displacement,
      (fields base signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) :
    (run base signed relation state).memory position = state.memory position := by
  rw [restored base signed relation x y backing state capacity initial]
  exact BranchPrefix.byte_frame base signed relation x y state capacity position outside

theorem continuation_ownership (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) :
    ∀ form ∈ ByteControl.restoreForms (pointer base) (address base), ∀ state : State,
      Owned (entries base signed relation x y) (ByteExecution.destination form state).toNat := by
  have layout := full_layout base signed relation x y capacity
  have pFit := layout.fits (base + 6) (by simp [ownedFields])
  have aFit := layout.fits (base + 2) (by simp [ownedFields])
  intro form member state
  change form ∈ [.memory .exchangeStack (FieldRefinement.address (base + 6)),
    .memory .addFour (FieldRefinement.address (base + 6)), .memory .exchangeAcc (FieldRefinement.address (base + 6)),
    .storeAcc (FieldRefinement.address (base + 2)), .memory .exchangeAcc (FieldRefinement.address (base + 6))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [ByteExecution.destination, FieldRefinement.address_toNat _ pFit, FieldRefinement.address_toNat _ aFit]
    apply field_owned base signed relation x y
    simp [ownedFields]

theorem continuation_straight (base : Nat) :
    ∀ form ∈ ByteControl.restoreForms (pointer base) (address base), ByteLinear.Straight form := by
  intro form member
  change form ∈ [.memory .exchangeStack (FieldRefinement.address (base + 6)),
    .memory .addFour (FieldRefinement.address (base + 6)), .memory .exchangeAcc (FieldRefinement.address (base + 6)),
    .storeAcc (FieldRefinement.address (base + 2)), .memory .exchangeAcc (FieldRefinement.address (base + 6))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem continuation_span (base : Nat) : ByteLinear.span (ByteControl.restoreForms (pointer base) (address base)) = 30 := rfl

theorem continuation_trace (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (intact : Intact (entries base signed relation x y) state.memory)
    (location : state.pc = FieldRefinement.address (selectedPC base signed relation x y)) :
    ByteExecution.Trace state (ByteControl.restoreForms (pointer base) (address base))
      (ByteControl.restore (pointer base) (address base) state) := by
  rw [←ByteControl.restore_run]
  apply ByteLinear.constructed_trace _ _ (selectedPC base signed relation x y) state
    (BytePacking.placed_separated _ _) intact _ (continuation_straight base) _
    (continuation_ownership base signed relation x y capacity) location
  · change ∀ entry ∈ BytePacking.place (selectedPC base signed relation x y) (continuation base),
      entry ∈ entries base signed relation x y
    by_cases holds : BranchAlgebra.holds signed relation x y
    · simpa only [selectedPC, ite_eq_left holds] using BranchPaths.taken_placed base signed relation x y
    · simpa only [selectedPC, ite_eq_right holds] using BranchPaths.fall_placed base signed relation x y
  · rw [continuation_span]
    simp only [selectedPC]
    split <;> simp only [endPC, yPC, xPC, takenPC] at capacity ⊢ <;> omega

/-- One initializer supplies ALL fetches through prefix, CALL and the selected
continuation. The only execution premises are image, entry and finite capacity. -/
theorem trace (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart base)) :
    ByteExecution.Trace state (forms base signed relation state) (run base signed relation state) := by
  have initialized : Intact (entries base signed relation x y) state.memory := by
    rw [initial]
    exact BytePacking.initial_intact _ _ _
  have tail := BranchPaths.tail_trace_intact base signed relation x y _ capacity
    (BranchPrefix.finish_intact base signed relation x y state capacity initialized)
    (BranchPrefix.finish_pc base signed relation state location)
    (prefix_stack base signed relation x y backing state capacity initial).1
  exact ByteExecution.trace_append
    (ByteExecution.trace_append (BranchPrefix.trace base signed relation x y backing state capacity initial location) tail.1)
    (continuation_trace base signed relation x y _ capacity tail.2
      (tail_pc base signed relation x y backing state capacity initial location))

theorem tail_owned_run (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (top : ByteControl.load state.memory (pointer base) = pointer base) :
    ByteExecution.OwnedRun (fun word => Owned (entries base signed relation x y) word.toNat)
      (ByteControl.tailForms (pointer base) (BranchControl.displacement base signed relation) state) state := by
  have layout := full_layout base signed relation x y capacity
  have pFit := layout.fits (base + 6) (by simp [ownedFields])
  have aFit := layout.fits (base + 2) (by simp [ownedFields])
  constructor
  · change Owned _ (FieldRefinement.address (base + 6)).toNat
    rw [FieldRefinement.address_toNat _ pFit]
    exact field_owned base signed relation x y _ (by simp [ownedFields])
  · constructor
    · change Owned _ (BitVec.sub (ByteControl.exchangeStack (pointer base) state).stack 4).toNat
      rw [ByteControl.exchange_stack_effect, top, slot_alias]
      change Owned _ (FieldRefinement.address (base + 2)).toNat
      rw [FieldRefinement.address_toNat _ aFit]
      exact field_owned base signed relation x y _ (by simp [ownedFields])
    · trivial

theorem owned_run (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    ByteExecution.OwnedRun (fun word => Owned (entries base signed relation x y) word.toNat)
      (forms base signed relation state) state := by
  have layout := BranchLayout.field_layout base signed relation x y capacity
  have prefixOwned : ByteExecution.OwnedRun (fun word => Owned (entries base signed relation x y) word.toNat)
      (FieldRefinement.forms (program base signed relation) state) state := by
    apply FieldRefinement.owned_run
    intro instruction member
    have dependency := BranchExecution.relation_dependencies _ signed relation _ instruction member _
      (FieldRefinement.destination_dependency instruction)
    rw [FieldRefinement.address_toNat _ (layout.fits _ dependency)]
    exact fields_owned base signed relation x y _ dependency
  unfold forms
  rw [ByteExecution.owned_append, ByteExecution.owned_append, FieldRefinement.forms_run,
    ByteExecution.run_append, FieldRefinement.forms_run, ByteControl.tail_run]
  exact ⟨⟨prefixOwned, tail_owned_run base signed relation x y _ capacity
    (prefix_stack base signed relation x y backing state capacity initial).1⟩,
    ByteLinear.owned_run _ _ _ (continuation_ownership base signed relation x y capacity)⟩

theorem finish_intact (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing) :
    Intact (entries base signed relation x y) (run base signed relation state).memory := by
  rw [restored base signed relation x y backing state capacity initial]
  apply BranchPrefix.finish_intact base signed relation x y state capacity
  rw [initial]
  exact BytePacking.initial_intact _ _ _

/-- Closed reference branch certificate for arbitrary backing bytes, incoming
registers/CF and all 32-bit inputs. The endpoint is an observation boundary,
not a halt theorem or a physical hardware instruction-fetch claim. -/
theorem correct (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) (backing : Memory)
    (state : State) (capacity : endPC base signed relation ≤ 2 ^ 32)
    (initial : state.memory = image (entries base signed relation x y) backing)
    (location : state.pc = FieldRefinement.address (prefixStart base)) :
    ByteExecution.Trace state (forms base signed relation state) (run base signed relation state) ∧
    (run base signed relation state).pc = FieldRefinement.address (finishPC base signed relation x y) ∧
    (run base signed relation state).accumulator = state.accumulator ∧
    (run base signed relation state).stack = state.stack ∧
    (run base signed relation state).carry = false ∧
    ByteExecution.OwnedRun (fun word => Owned (entries base signed relation x y) word.toNat)
      (forms base signed relation state) state ∧
    Intact (entries base signed relation x y) (run base signed relation state).memory ∧
    (∀ position, (∀ field ∈ [(fields base signed relation).mask, (fields base signed relation).displacement,
      (fields base signed relation).delta], ¬Native.ByteMemory.Inside field 4 position) →
      (run base signed relation state).memory position = state.memory position) :=
  ⟨trace base signed relation x y backing state capacity initial location,
   finish_pc base signed relation x y backing state capacity initial location,
   accumulator base signed relation x y backing state capacity initial,
   stack base signed relation x y backing state capacity initial,
   carry base signed relation x y backing state capacity initial,
   owned_run base signed relation x y backing state capacity initial,
   finish_intact base signed relation x y backing state capacity initial,
   byte_frame base signed relation x y backing state capacity initial⟩

end SmcTuring.Appendix.BranchWhole
