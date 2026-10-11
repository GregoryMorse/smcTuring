module
public import SmcTuring.Appendix.DivisionSetup

public section
namespace SmcTuring.Appendix.DivisionPaths

open DivisionImage DivisionSetup
abbrev State := DivisionByteExecution.State
abbrev Word := DivisionByteCode.Word

@[expose] def tailForms (place : Placement) (block : Block) (state : State) : List DivisionByteCode.Form :=
  (ByteControl.tailForms (pointer place) (displacement place block) state).map
    (fun form => DivisionByteCode.Form.common (MultiplyByteCode.Form.common form))
@[expose] def tail (place : Placement) (block : Block) (state : State) : State :=
  ByteControl.tail (pointer place) (displacement place block) state
@[expose] def continued (place : Placement) (block : Block) (state : State) : State :=
  ByteControl.restore (pointer place) (address place) (tail place block state)
@[expose] def forms (place : Placement) (block : Block) (state : State) : List DivisionByteCode.Form :=
  tailForms place block state ++ DivisionPackets.restoreForms place

theorem tail_run (place : Placement) (block : Block) (state : State) :
    DivisionByteExecution.run (tailForms place block state) state = tail place block state := by
  change DivisionByteExecution.run ((ByteControl.tailForms (pointer place) (displacement place block) state).map
    MultiplyByteCode.Form.common |>.map DivisionByteCode.Form.common) state = _
  rw [DivisionLinear.run_common, MultiplyLinear.run_common, ByteControl.tail_run]
  rfl

theorem restore_run (place : Placement) (state : State) :
    DivisionByteExecution.run (DivisionPackets.restoreForms place) state = ByteControl.restore (pointer place) (address place) state := by
  change DivisionByteExecution.run ((ByteControl.restoreForms (pointer place) (address place)).map
    MultiplyByteCode.Form.common |>.map DivisionByteCode.Form.common) state = _
  rw [DivisionLinear.run_common, MultiplyLinear.run_common]
  change ByteExecution.run (ByteControl.restoreForms (pointer place) (address place)) state = _
  exact ByteControl.restore_run _ _ state

theorem forms_run (place : Placement) (block : Block) (state : State) :
    DivisionByteExecution.run (forms place block state) state = continued place block state := by
  rw [forms, DivisionByteExecution.run_append, tail_run, restore_run]
  rfl

theorem fetched_current (whole : List Entry) (entry : Entry) (state : State)
    (intact : Intact whole state.memory) (member : entry ∈ whole)
    (fits : entry.pc + 4 ≤ 2 ^ 32) (location : state.pc = FieldRefinement.address entry.pc) :
    DivisionByteCode.fetch state.memory state.pc.toNat = some (current entry state.memory) := by
  rw [location]
  change DivisionByteCode.fetch state.memory (FieldRefinement.address entry.pc).toNat = _
  rw [FieldRefinement.address_toNat entry.pc fits]
  exact fetch_current entry state.memory (intact entry member)

theorem call_current (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (state : State)
    (intact : Intact (DivisionLayout.entries place x y) state.memory) :
    current (callEntry place block) state.memory =
      .common (.common (.callRelative (ByteControl.load state.memory (displacement place block)))) := by
  cases block with
  | initial =>
    have value := fixed_call place x y valid .initial active (by decide) state intact
    change DivisionByteCode.Form.common (.common (.callRelative (callInitial place .initial))) = _
    exact congrArg (fun word => DivisionByteCode.Form.common (.common (ByteCode.Form.callRelative word))) value.symm
  | guard =>
    change DivisionByteCode.Form.common (.common (.callRelative (ByteImage.wordAt state.memory (callPC place .guard + 1)))) = _
    rw [←call_field_position place .guard active, ByteImage.word_at_read_field state _ (call_fits place valid .guard)]
    rfl
  | body =>
    have value := fixed_call place x y valid .body active (by decide) state intact
    change DivisionByteCode.Form.common (.common (.callRelative (callInitial place .body))) = _
    exact congrArg (fun word => DivisionByteCode.Form.common (.common (ByteCode.Form.callRelative word))) value.symm
  | finish => exact False.elim (active rfl)

/-- Both events fetch their own actual current bytes. XCHG ESP executes before
CALL's displacement is read. CALL writes the real inactive DEFSTACK address. -/
theorem tail_trace_intact (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (state : State)
    (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (location : state.pc = FieldRefinement.address (tailStart place block))
    (ready : Ready place state) :
    DivisionByteExecution.Trace state (tailForms place block state) (tail place block state) ∧
      Intact (DivisionLayout.entries place x y) (tail place block state).memory := by
  let exchanged := ByteControl.exchangeStack (pointer place) state
  have pOwned : Owned (DivisionLayout.entries place x y) (pointer place).toNat := by
    change Owned _ (FieldRefinement.address (place.stackInstruction + 6)).toNat
    rw [FieldRefinement.address_toNat _ (pointer_fits place valid)]
    exact DivisionLayout.pointer_owned place x y
  have exIntact : Intact (DivisionLayout.entries place x y) exchanged.memory :=
    execute_intact _ state (.common (.common (.memory .exchangeStack (pointer place))))
      (DivisionLayout.separated place x y valid) intact pOwned
  have exLocation : exchanged.pc = FieldRefinement.address (callPC place block) := by
    change (ByteControl.exchangeStack (pointer place) state).pc = _
    rw [ByteControl.exchange_stack_effect, location]
    exact BitVec.ofNat_add_ofNat _ _
  have slot : BitVec.sub exchanged.stack 4 = address place := by
    change BitVec.sub (ByteControl.exchangeStack (pointer place) state).stack 4 = _
    rw [ByteControl.exchange_stack_effect, ready.top]
    exact slot_alias place
  have callOwned : ∀ value : Word, Owned (DivisionLayout.entries place x y)
      (DivisionByteExecution.destination (.common (.common (.callRelative value))) exchanged).toNat := by
    intro value
    change Owned _ (BitVec.sub exchanged.stack 4).toNat
    rw [slot]
    change Owned _ (FieldRefinement.address (place.stackInstruction + 2)).toNat
    rw [FieldRefinement.address_toNat _ (address_fits place valid)]
    exact DivisionLayout.address_owned place x y
  have extent := tail_fits place valid block active
  have firstFit : tailStart place block + 4 ≤ 2 ^ 32 := by omega
  have callFit : callPC place block + 4 ≤ 2 ^ 32 := by unfold callPC; omega
  have firstMember : (⟨tailStart place block, .fixed (.common (.common (.memory .exchangeStack (pointer place))))⟩ : Entry) ∈
      DivisionLayout.entries place x y :=
    tail_placed place x y block active _ (by simp [DivisionLayout.tailPackets, DivisionPacking.place, pointer])
  have firstFetch : DivisionByteCode.fetch state.memory state.pc.toNat =
      some (.common (.common (.memory .exchangeStack (pointer place)))) :=
    fetched_current _ _ state intact firstMember firstFit location
  have callFetch : DivisionByteCode.fetch exchanged.memory exchanged.pc.toNat =
      some (.common (.common (.callRelative (ByteControl.load exchanged.memory (displacement place block))))) := by
    rw [←call_current place x y valid block active exchanged exIntact]
    exact fetched_current _ _ exchanged exIntact (call_placed place x y block active) callFit exLocation
  constructor
  · exact .step firstFetch (.step callFetch (.nil _))
  · change Intact (DivisionLayout.entries place x y)
      (DivisionByteExecution.execute (.common (.common (.callRelative
        (ByteControl.load exchanged.memory (displacement place block))))) exchanged).memory
    exact execute_intact _ exchanged (.common (.common (.callRelative
      (ByteControl.load exchanged.memory (displacement place block)))))
      (DivisionLayout.separated place x y valid) exIntact (callOwned _)

theorem tail_owned (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat)
      (tailForms place block state) state := by
  constructor
  · change Owned _ (FieldRefinement.address (place.stackInstruction + 6)).toNat
    rw [FieldRefinement.address_toNat _ (pointer_fits place valid)]
    exact DivisionLayout.pointer_owned place x y
  · constructor
    · change Owned _ (BitVec.sub (ByteControl.exchangeStack (pointer place) state).stack 4).toNat
      rw [ByteControl.exchange_stack_effect, ready.top, slot_alias]
      change Owned _ (FieldRefinement.address (place.stackInstruction + 2)).toNat
      rw [FieldRefinement.address_toNat _ (address_fits place valid)]
      exact DivisionLayout.address_owned place x y
    · trivial

theorem continuation_ownership (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place) :
    ∀ form ∈ DivisionPackets.restoreForms place, ∀ state : State,
      Owned (DivisionLayout.entries place x y) (DivisionByteExecution.destination form state).toNat := by
  intro form member state
  change form ∈ [.common (.common (.memory .exchangeStack (pointer place))), .common (.common (.memory .addFour (pointer place))),
    .common (.common (.memory .exchangeAcc (pointer place))), .common (.common (.storeAcc (address place))),
    .common (.common (.memory .exchangeAcc (pointer place)))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [DivisionByteExecution.destination, MultiplyByteExecution.destination, ByteExecution.destination, pointer, address,
    FieldRefinement.address_toNat _ (pointer_fits place valid), FieldRefinement.address_toNat _ (address_fits place valid)]
  all_goals first | exact DivisionLayout.pointer_owned place x y | exact DivisionLayout.address_owned place x y

theorem continuation_straight (place : Placement) :
    ∀ form ∈ DivisionPackets.restoreForms place, DivisionLinear.Straight form := by
  intro form member
  change form ∈ [.common (.common (.memory .exchangeStack (pointer place))), .common (.common (.memory .addFour (pointer place))),
    .common (.common (.memory .exchangeAcc (pointer place))), .common (.common (.storeAcc (address place))),
    .common (.common (.memory .exchangeAcc (pointer place)))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem continuation_span (place : Placement) : DivisionLinear.span (DivisionPackets.restoreForms place) = 30 := rfl

theorem continuation_trace (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (kind : Continuation) (state : State) (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (location : state.pc = FieldRefinement.address (continuationStart place kind)) :
    DivisionByteExecution.Trace state (DivisionPackets.restoreForms place) (ByteControl.restore (pointer place) (address place) state) := by
  rw [←restore_run]
  apply DivisionLinear.constructed_trace _ _ (continuationStart place kind) state
    (DivisionLayout.separated place x y valid) intact (continuation_placed place x y kind)
    (continuation_straight place) _ (continuation_ownership place x y valid) location
  rw [continuation_span]
  exact continuation_fits place valid kind

theorem continuation_intact (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (state : State) (intact : Intact (DivisionLayout.entries place x y) state.memory) :
    Intact (DivisionLayout.entries place x y) (ByteControl.restore (pointer place) (address place) state).memory := by
  rw [←restore_run]
  exact DivisionLinear.run_intact _ _ state (DivisionLayout.separated place x y valid) intact (continuation_ownership place x y valid)

theorem continued_effect (place : Placement) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    continued place block state = { state with pc := BitVec.add (tail place block state).pc 30, carry := false } :=
  ByteControl.continued_alias (pointer place) (displacement place block) (address place) state
    (call_apart place valid block) (slot_apart place valid) ready.top (slot_alias place) ready.addressValue (pointer_nonwrap place valid)

theorem continued_ready (place : Placement) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) : Ready place (continued place block state) := by
  rw [continued_effect place valid block state ready]
  exact ⟨ready.top, ready.addressValue⟩

theorem continued_intact (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state)
    (intact : Intact (DivisionLayout.entries place x y) state.memory) :
    Intact (DivisionLayout.entries place x y) (continued place block state).memory := by
  rw [continued_effect place valid block state ready]
  exact intact

theorem tail_target_pc (place : Placement) (valid : DivisionLayout.Admissible place)
    (block : Block) (kind : Continuation) (state : State)
    (location : state.pc = FieldRefinement.address (tailStart place block))
    (target : ByteControl.load state.memory (displacement place block) =
      BitVec.sub (FieldRefinement.address (continuationStart place kind)) (FieldRefinement.address (tailStart place block + 11))) :
    (tail place block state).pc = FieldRefinement.address (continuationStart place kind) := by
  rw [tail, ByteControl.tail_effect _ _ _ (call_apart place valid block), location, target]
  have next : BitVec.add (FieldRefinement.address (tailStart place block)) 11 =
      FieldRefinement.address (tailStart place block + 11) := BitVec.ofNat_add_ofNat _ _
  change BitVec.add (BitVec.add (FieldRefinement.address (tailStart place block)) 11)
    (BitVec.sub (FieldRefinement.address (continuationStart place kind)) (FieldRefinement.address (tailStart place block + 11))) = _
  rw [next]
  change FieldRefinement.address (tailStart place block + 11) +
    (FieldRefinement.address (continuationStart place kind) - FieldRefinement.address (tailStart place block + 11)) = _
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- The current displacement selects a PRINTED continuation. This component
constructs all seven current-byte fetches and derives their owned writes. Its
current-value equation is to be supplied by the data-block arithmetic bridge,
not by an assumed future PC, future invariant or trace. -/
theorem continued_trace (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (active : block ≠ .finish) (kind : Continuation) (state : State)
    (intact : Intact (DivisionLayout.entries place x y) state.memory)
    (location : state.pc = FieldRefinement.address (tailStart place block)) (ready : Ready place state)
    (target : ByteControl.load state.memory (displacement place block) =
      BitVec.sub (FieldRefinement.address (continuationStart place kind)) (FieldRefinement.address (tailStart place block + 11))) :
    DivisionByteExecution.Trace state (forms place block state) (continued place block state) := by
  have leading := tail_trace_intact place x y valid block active state intact location ready
  have transfer := tail_target_pc place valid block kind state location target
  exact DivisionByteExecution.trace_append leading.1 (continuation_trace place x y valid kind _ leading.2 transfer)

theorem continued_owned (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (block : Block) (state : State) (ready : Ready place state) :
    DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) (forms place block state) state := by
  rw [forms, DivisionByteExecution.owned_append]
  exact ⟨tail_owned place x y valid block state ready,
    DivisionLinear.owned_run _ _ _ (continuation_ownership place x y valid)⟩

end SmcTuring.Appendix.DivisionPaths
