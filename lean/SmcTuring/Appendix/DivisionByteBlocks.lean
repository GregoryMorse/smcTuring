module
public import SmcTuring.Appendix.DivisionPaths

public section
namespace SmcTuring.Appendix.DivisionByteBlocks

open DivisionImage DivisionSetup
abbrev State := DivisionByteExecution.State
abbrev Word := DivisionByteCode.Word

@[expose] def data (place : Placement) (block : Block) (state : State) : State :=
  DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) state
@[expose] def run (place : Placement) (block : Block) (state : State) : State :=
  if block == .finish then data place block state else DivisionPaths.continued place block (data place block state)
@[expose] def forms (place : Placement) (block : Block) (state : State) : List DivisionByteCode.Form :=
  DivisionRefinement.forms (DivisionBlocks.words (DivisionPackets.layout place) block) state ++
    if block == .finish then [] else DivisionPaths.forms place block (data place block state)
@[expose] def view (state : State) : Machine32.State :=
  ⟨state.accumulator, state.carry, FieldRefinement.readField state⟩
@[expose] def selected (place : Placement) (block : Block) (state : State) : Continuation :=
  if block == .guard then
    if FieldRefinement.readField state (DivisionPackets.fields place .counter) = BitVec.ofNat 32 0 then .exit else .body
  else .guard

/-- Only the zero-test block needs its current displacement at zero. This is
initialized once and maintained on the actual guard/body path. -/
@[expose] def GuardReady (place : Placement) (block : Block) (state : State) : Prop :=
  block = .guard → FieldRefinement.readField state (DivisionPackets.fields place .displacement) = 0

theorem view_agreement (fields : List Nat) (state : State) : FieldRefinement.Agreement fields (view state) state :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem forms_run (place : Placement) (block : Block) (state : State) :
    DivisionByteExecution.run (forms place block state) state = run place block state := by
  rw [forms, DivisionByteExecution.run_append, DivisionRefinement.forms_run]
  cases block <;> simp [run, data, DivisionPaths.forms_run, DivisionByteExecution.run]

theorem data_end_pc (place : Placement) (block : Block) (state : State)
    (location : state.pc = FieldRefinement.address (DivisionData.blockStart place block)) :
    (data place block state).pc = FieldRefinement.address (tailStart place block) := by
  rw [data, DivisionData.run_pc _ _ _ location]
  change FieldRefinement.address (DivisionData.blockStart place block + DivisionPacking.size (DivisionLayout.dataPackets place block)) = _
  rw [DivisionLayout.data_size]
  cases block <;> simp [DivisionData.blockStart, tailStart, DivisionLayout.pureSpan, Nat.add_assoc]

theorem guard_displacement (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (state : State) (zero : FieldRefinement.readField state (DivisionPackets.fields place .displacement) = 0) :
    FieldRefinement.readField (data place .guard state) (DivisionPackets.fields place .displacement) =
      if FieldRefinement.readField state (DivisionPackets.fields place .counter) = 0 then
        DivisionBlocks.delta (DivisionPackets.layout place) else 0 := by
  have agreement := DivisionData.block_refinement place x y valid .guard (view state) state (view_agreement _ state)
  have word := agreement.words (DivisionPackets.fields place .displacement)
    ((DivisionPacking.fields_owned _ _).mpr (DivisionLayout.slot_owned place x y .displacement (by trivial)))
  rw [data, word]
  exact DivisionGuard.displacement _ _ (view state) (word_separate place valid) zero

/-- The control target is calculated from the executed DATA state. Fixed
CALL operands come from protected bytes; the conditional comes from the proved
zero-test arithmetic. No future PC or target value is supplied. -/
theorem target (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (state : State)
    (intact : Intact (DivisionLayout.entries place x y) state.memory) (guard : GuardReady place block state) :
    ByteControl.load (data place block state).memory (displacement place block) =
      BitVec.sub (FieldRefinement.address (continuationStart place (selected place block state)))
        (FieldRefinement.address (tailStart place block + 11)) := by
  have nextIntact := DivisionData.block_intact place x y valid block state intact
  cases block with
  | initial =>
    change FieldRefinement.readField (data place .initial state) (callField place .initial) = _
    have value := fixed_call place x y valid .initial active (by decide) (data place .initial state) nextIntact
    change FieldRefinement.readField (data place .initial state) (callField place .initial) = _ at value
    rw [value]
    simp [callInitial, selected, continuationStart, tailStart, Nat.add_assoc]
  | guard =>
    change FieldRefinement.readField (data place .guard state) (DivisionPackets.fields place .displacement) = _
    rw [guard_displacement place x y valid state (guard rfl)]
    simp only [selected, beq_self_eq_true, ite_true, tailStart, Nat.add_assoc, Nat.reduceAdd]
    by_cases zero : FieldRefinement.readField state (DivisionPackets.fields place .counter) = (0 : Word)
    · simp only [show (BitVec.ofNat 32 0 : Word) = (0 : Word) from rfl, zero, ite_true, continuationStart]
      have equality := congrArg₂ (fun (first second : Word) => first - second) (continuation_code place .exit).symm (continuation_code place .body).symm
      simpa only [DivisionBlocks.delta, continuationStart, Nat.add_assoc, BitVec.sub_eq] using equality
    · change (if FieldRefinement.readField state (DivisionPackets.fields place .counter) = (0 : Word)
          then DivisionBlocks.delta (DivisionPackets.layout place) else BitVec.ofNat 32 0) = _
      simp only [show (BitVec.ofNat 32 0 : Word) = (0 : Word) from rfl,
        zero, ite_false, continuationStart, Nat.add_assoc, BitVec.sub_eq]
      exact (BitVec.sub_self _).symm
  | body =>
    change FieldRefinement.readField (data place .body state) (callField place .body) = _
    have value := fixed_call place x y valid .body active (by decide) (data place .body state) nextIntact
    change FieldRefinement.readField (data place .body state) (callField place .body) = _ at value
    rw [value]
    have equality := congrArg₂ (fun (first second : Word) => first - second) (continuation_code place .guard).symm (continuation_code place .exit).symm
    simpa only [callInitial, selected, Bool.false_eq_true, beq_iff_eq, reduceCtorEq,
      ite_false, continuationStart, tailStart, DivisionBlocks.backDelta, Nat.add_assoc, Nat.reduceAdd, BitVec.sub_eq] using equality
  | finish => exact False.elim (active rfl)

theorem run_effect (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (state : State) (ready : Ready place state) :
    run place block state = { data place block state with
      pc := BitVec.add (DivisionPaths.tail place block (data place block state)).pc 30, carry := false } := by
  have nextReady := data_ready place x y valid block state ready
  have effect := DivisionPaths.continued_effect place valid block (data place block state) nextReady
  simpa only [run, Bool.not_eq_true, beq_iff_eq, active, ite_false] using effect

/-- Complete live-byte execution of each printed block, including its actual
CALL and selected continuation. Only the maintained boundary image, stack
values, entry PC and guard-zero value are supplied, with all future fetches,
owned writes, transfer PC and preservation derived. -/
theorem trace (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (ready : Ready place state) (guard : GuardReady place block state)
    (location : state.pc = FieldRefinement.address (DivisionData.blockStart place block)) :
    DivisionByteExecution.Trace state (forms place block state) (run place block state) := by
  have leading := DivisionData.block_trace place x y valid block state intact location
  by_cases finish : block = .finish
  · subst block
    simpa only [forms, run, beq_self_eq_true, ite_true, List.append_nil, data] using leading
  · have trailing := DivisionPaths.continued_trace place x y valid block finish (selected place block state)
      (data place block state) (DivisionData.block_intact place x y valid block state intact)
      (data_end_pc place block state location) (data_ready place x y valid block state ready)
      (target place x y valid block finish state intact guard)
    simpa only [forms, run, Bool.not_eq_true, beq_iff_eq, finish, ite_false, data] using
      DivisionByteExecution.trace_append leading trailing

theorem image_trace (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (backing : Memory) (state : State)
    (initial : state.memory = image (DivisionLayout.entries place x y) backing)
    (location : state.pc = FieldRefinement.address (DivisionData.blockStart place block)) :
    DivisionByteExecution.Trace state (forms place block state) (run place block state) := by
  have intact : Intact (DivisionLayout.entries place x y) state.memory := by
    rw [initial]; exact DivisionLayout.initial_intact place x y backing valid
  apply trace place x y valid block state intact (initial_ready place x y valid backing state initial) _ location
  intro same
  subst block
  exact initial_call place x y valid .guard (by decide) backing state initial

theorem run_intact (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (ready : Ready place state) : Intact (DivisionLayout.entries place x y) (run place block state).memory := by
  by_cases finish : block = .finish
  · subst block
    exact DivisionData.block_intact place x y valid .finish state intact
  · rw [run_effect place x y valid block finish state ready]
    exact DivisionData.block_intact place x y valid block state intact

theorem run_ready (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) : Ready place (run place block state) := by
  by_cases finish : block = .finish
  · subst block
    exact data_ready place x y valid .finish state ready
  · rw [run_effect place x y valid block finish state ready]
    have nextReady := data_ready place x y valid block state ready
    exact ⟨nextReady.top, nextReady.addressValue⟩

theorem owned (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) (forms place block state) state := by
  have leading : DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat)
      (DivisionRefinement.forms (DivisionBlocks.words (DivisionPackets.layout place) block) state) state := by
    apply DivisionRefinement.owned_run
    intro instruction member
    rw [FieldRefinement.address_toNat _ (DivisionData.block_capacity place x y valid block instruction member _
      (DivisionRefinement.destination_dependency instruction))]
    exact DivisionData.block_dependency_owned place x y block instruction member _ (DivisionRefinement.destination_dependency instruction)
  by_cases finish : block = .finish
  · subst block
    simpa only [forms, beq_self_eq_true, ite_true, List.append_nil] using leading
  · simp only [forms, beq_iff_eq, finish, ite_false]
    rw [DivisionByteExecution.owned_append, DivisionRefinement.forms_run]
    exact ⟨leading, DivisionPaths.continued_owned place x y valid block _ (data_ready place x y valid block state ready)⟩

/-- Finite field/EAX/CF refinement of the COMPLETE block. CALL and continuation
restore all bytes to the data result and clear CF, so metadata words are included
without assuming a global independent-DWORD physical memory. -/
theorem refinement (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (source : Machine32.State) (state : State) (ready : Ready place state)
    (agreement : FieldRefinement.Agreement (DivisionPacking.fields (DivisionLayout.entries place x y)) source state) :
    FieldRefinement.Agreement (DivisionPacking.fields (DivisionLayout.entries place x y))
      (if block == .finish then DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) source
        else MultiplyControl.clearCarry (DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) source))
      (run place block state) := by
  have next := DivisionData.block_refinement place x y valid block source state agreement
  by_cases finish : block = .finish
  · subst block
    exact next
  · rw [run_effect place x y valid block finish state ready]
    simp only [beq_iff_eq, finish, ite_false]
    exact ⟨next.accumulator, rfl, next.words⟩

@[expose] def finishPC (place : Placement) (block : Block) (state : State) : Nat :=
  if block == .finish then place.origin + DivisionLayout.pureSpan place else continuationStart place (selected place block state) + 30

/-- Exact resulting PC, calculated from the original block input and reached
arithmetic/control states, for guard/body/backedge/exit dispatch. -/
theorem run_pc (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (ready : Ready place state) (guard : GuardReady place block state)
    (location : state.pc = FieldRefinement.address (DivisionData.blockStart place block)) :
    (run place block state).pc = FieldRefinement.address (finishPC place block state) := by
  by_cases finish : block = .finish
  · subst block
    exact data_end_pc place .finish state location
  · rw [run_effect place x y valid block finish state ready,
      DivisionPaths.tail_target_pc place valid block (selected place block state) (data place block state)
        (data_end_pc place block state location) (target place x y valid block finish state intact guard)]
    simp only [finishPC, beq_iff_eq, finish, ite_false]
    exact BitVec.ofNat_add_ofNat _ _

theorem field (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) (slot : DivisionWords.Slot) (active : DivisionLayout.ActiveSlot place slot) :
    FieldRefinement.readField (run place block state) (DivisionPackets.fields place slot) =
      (DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) (view state)).memory (DivisionPackets.fields place slot) := by
  have agreement := refinement place x y valid block (view state) state ready (view_agreement _ state)
  have word := agreement.words _ ((DivisionPacking.fields_owned _ _).mpr (DivisionLayout.slot_owned place x y slot active))
  by_cases finish : block = .finish
  · simpa only [beq_iff_eq, finish, ite_true] using word
  · simpa only [beq_iff_eq, finish, ite_false, MultiplyControl.clearCarry] using word

theorem stack (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) : (run place block state).stack = state.stack := by
  by_cases finish : block = .finish
  · subst block
    exact DivisionRefinement.run_stack _ state
  · rw [run_effect place x y valid block finish state ready]
    exact DivisionRefinement.run_stack _ state

end SmcTuring.Appendix.DivisionByteBlocks
