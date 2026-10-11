module
public import SmcTuring.Appendix.MultiplyByteBlocks
public import SmcTuring.Appendix.MultiplyExecution

public section
namespace SmcTuring.Appendix.MultiplyByteSimulation

open MultiplyImage MultiplySetup
abbrev State := MultiplyByteExecution.State
abbrev Source := MultiplyControl.State
abbrev Word := BitVec 32

/-- Only the fourteen disjoint represented words are related. Arbitrary
physical overlapping DWORD loads are not modeled as independent word cells. -/
structure Agreement (place : Placement) (x y : Word) (source : Source) (native : State) : Prop where
  data : FieldRefinement.Agreement (MultiplyPacking.fields (MultiplyLayout.entries place x y)) source.data native
  stack : native.stack = source.stack
  pc : native.pc = source.pc

@[expose] def sourceView (native : State) : Source :=
  ⟨MultiplyByteBlocks.view native, native.stack, native.pc⟩

theorem view_agreement (place : Placement) (x y : Word) (native : State) :
    Agreement place x y (sourceView native) native := ⟨MultiplyByteBlocks.view_agreement _ native, rfl, rfl⟩

theorem slot_word (place : Placement) (x y : Word) (source : Source) (native : State)
    (agreement : Agreement place x y source native) (slot : MultiplyWords.Slot) :
    FieldRefinement.readField native (MultiplyPackets.fields place slot) = source.data.memory (MultiplyPackets.fields place slot) :=
  agreement.data.words _ ((MultiplyPacking.fields_owned _ _).mpr (MultiplyLayout.slot_owned place x y slot))

theorem source_ready (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (source : Source) (native : State) (agreement : Agreement place x y source native) (ready : Ready place native) :
    MultiplyControl.StackReady (MultiplyPackets.layout place).pointer (MultiplyPackets.layout place).address source := by
  have p := agreement.data.words _ ((MultiplyPacking.fields_owned _ _).mpr (MultiplyLayout.pointer_owned place x y))
  have a := agreement.data.words _ ((MultiplyPacking.fields_owned _ _).mpr (MultiplyLayout.address_owned place x y))
  have pointerValue : source.data.memory (place.stackInstruction + 6) = pointer place := p.symm.trans ready.top
  have addressValue : source.data.memory (place.stackInstruction + 2) = pointer place := a.symm.trans ready.addressValue
  constructor
  · change (source.data.memory (place.stackInstruction + 6) - 4).toNat = place.stackInstruction + 2
    rw [pointerValue]
    change (BitVec.sub (pointer place) 4).toNat = _
    rw [slot_alias]
    exact FieldRefinement.address_toNat _ (address_fits place valid)
  · exact addressValue.trans pointerValue.symm
  · change 4 ≤ (source.data.memory (place.stackInstruction + 6)).toNat
    rw [pointerValue]; exact pointer_nonwrap place valid

theorem block_start (place : Placement) (block : Block) :
    FieldRefinement.address (MultiplyData.blockStart place block) = match block with
      | .initial => (MultiplyPackets.layout place).origin
      | .guard => MultiplyBlocks.guardPC (MultiplyPackets.layout place)
      | .body => MultiplyBlocks.bodyPC (MultiplyPackets.layout place)
      | .finish => MultiplyBlocks.exitPC (MultiplyPackets.layout place) := by
  cases block <;> simp only [MultiplyData.blockStart, MultiplyBlocks.guardPC, MultiplyBlocks.bodyPC,
    MultiplyBlocks.exitPC, MultiplyPackets.layout, FieldRefinement.address]
  all_goals first | rfl | exact (BitVec.ofNat_add_ofNat _ _).symm

theorem guard_ready (place : Placement) (x y : Word) (block : Block) (source : Source) (native : State)
    (agreement : Agreement place x y source native)
    (zero : block = .guard → source.data.memory (MultiplyPackets.fields place .displacement) = 0) :
    MultiplyByteBlocks.GuardReady place block native := by
  intro same
  rw [slot_word place x y source native agreement .displacement]
  exact zero same

theorem source_data_effect (place : Placement) (valid : MultiplyLayout.Admissible place)
    (block : Block) (source : Source)
    (ready : MultiplyControl.StackReady (MultiplyPackets.layout place).pointer (MultiplyPackets.layout place).address source) :
    (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) block) source).data =
      if block == .finish then MultiplyWords.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) source.data
      else MultiplyControl.clearCarry (MultiplyWords.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) source.data) := by
  by_cases finish : block = .finish
  · subst block
    simp only [MultiplyBlocks.program, ite_true, List.append_nil, MultiplyControl.lift_effect, beq_self_eq_true]
  · rw [MultiplyBlocks.program_effect _ _ _ (control_separate place valid) ready finish]
    simp only [beq_iff_eq, finish, ite_false]

theorem source_stack_effect (place : Placement) (valid : MultiplyLayout.Admissible place)
    (block : Block) (source : Source)
    (ready : MultiplyControl.StackReady (MultiplyPackets.layout place).pointer (MultiplyPackets.layout place).address source) :
    (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) block) source).stack = source.stack := by
  by_cases finish : block = .finish
  · subst block
    simp only [MultiplyBlocks.program, ite_true, List.append_nil, MultiplyControl.lift_effect]
  · rw [MultiplyBlocks.program_effect _ _ _ (control_separate place valid) ready finish]

/-- The complete block agrees on the actual resulting PC as well as all
represented data words and registers. Fixed source CALL words are initialized
once and framed; the conditional zero value is a current boundary invariant. -/
theorem block (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (kind : Block) (source : Source) (native : State) (agreement : Agreement place x y source native)
    (intact : Intact (MultiplyLayout.entries place x y) native.memory) (ready : Ready place native)
    (location : native.pc = FieldRefinement.address (MultiplyData.blockStart place kind))
    (direct : source.data.memory (MultiplyPackets.layout place).entryDisplacement = 0)
    (back : source.data.memory (MultiplyPackets.layout place).backDisplacement = MultiplyBlocks.backDelta (MultiplyPackets.layout place))
    (zero : kind = .guard → source.data.memory (MultiplyPackets.fields place .displacement) = 0) :
    Agreement place x y (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) kind) source)
      (MultiplyByteBlocks.run place kind native) := by
  have sourceReady := source_ready place x y valid source native agreement ready
  have nativeGuard := guard_ready place x y kind source native agreement zero
  have sourceLocation : source.pc = FieldRefinement.address (MultiplyData.blockStart place kind) := agreement.pc.symm.trans location
  have nativePC := MultiplyByteBlocks.run_pc place x y valid kind native intact ready nativeGuard location
  refine ⟨?_, ?_, ?_⟩
  · rw [source_data_effect place valid kind source sourceReady]
    exact MultiplyByteBlocks.refinement place x y valid kind source.data native ready agreement.data
  · rw [source_stack_effect place valid kind source sourceReady, MultiplyByteBlocks.stack place x y valid kind native ready]
    exact agreement.stack
  · rw [nativePC]
    cases kind with
    | initial =>
      have entry : source.pc = (MultiplyPackets.layout place).origin := sourceLocation.trans (block_start place .initial)
      rw [MultiplyBlocks.entry_effect _ _ (control_separate place valid) sourceReady entry direct]
      change FieldRefinement.address (place.origin + 55 + 30) = FieldRefinement.address place.origin + 85
      simp only [Nat.add_assoc, Nat.reduceAdd]
      change BitVec.ofNat 32 (place.origin + 85) = BitVec.add (BitVec.ofNat 32 place.origin) (BitVec.ofNat 32 85)
      exact (BitVec.ofNat_add_ofNat place.origin 85).symm
    | guard =>
      have entry : source.pc = MultiplyBlocks.guardPC (MultiplyPackets.layout place) := sourceLocation.trans (block_start place .guard)
      rw [MultiplyBlocks.guard_effect _ _ (control_separate place valid) sourceReady entry (zero rfl)]
      simp only [MultiplyByteBlocks.finishPC, MultiplyByteBlocks.selected, beq_self_eq_true, ite_true,
        slot_word place x y source native agreement .multiplier]
      by_cases empty : source.data.memory (MultiplyPackets.fields place .multiplier) = (0 : Machine32.Word)
      · simp only [empty, ite_true, continuationStart, MultiplyBlocks.exitPC, MultiplyPackets.layout]
        change FieldRefinement.address (place.origin + 332 + 30) = FieldRefinement.address place.origin + 362
        simp only [Nat.add_assoc, Nat.reduceAdd]
        change BitVec.ofNat 32 (place.origin + 362) = BitVec.add (BitVec.ofNat 32 place.origin) (BitVec.ofNat 32 362)
        exact (BitVec.ofNat_add_ofNat place.origin 362).symm
      · change FieldRefinement.address (continuationStart place
          (if source.data.memory (MultiplyPackets.fields place .multiplier) = (0 : Machine32.Word) then .exit else .body) + 30) =
          if source.data.memory (MultiplyPackets.fields place .multiplier) = (0 : Machine32.Word) then
            MultiplyBlocks.exitPC (MultiplyPackets.layout place) else MultiplyBlocks.bodyPC (MultiplyPackets.layout place)
        simp only [empty, ite_false, continuationStart, MultiplyBlocks.bodyPC, MultiplyPackets.layout]
        change FieldRefinement.address (place.origin + 161 + 30) = FieldRefinement.address place.origin + 191
        simp only [Nat.add_assoc, Nat.reduceAdd]
        change BitVec.ofNat 32 (place.origin + 191) = BitVec.add (BitVec.ofNat 32 place.origin) (BitVec.ofNat 32 191)
        exact (BitVec.ofNat_add_ofNat place.origin 191).symm
    | body =>
      have entry : source.pc = MultiplyBlocks.bodyPC (MultiplyPackets.layout place) := sourceLocation.trans (block_start place .body)
      rw [MultiplyBlocks.body_effect _ _ (control_separate place valid) sourceReady entry back]
      change FieldRefinement.address (place.origin + 55 + 30) = FieldRefinement.address place.origin + 85
      simp only [Nat.add_assoc, Nat.reduceAdd]
      change BitVec.ofNat 32 (place.origin + 85) = BitVec.add (BitVec.ofNat 32 place.origin) (BitVec.ofNat 32 85)
      exact (BitVec.ofNat_add_ofNat place.origin 85).symm
    | finish =>
      have entry : source.pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place) := sourceLocation.trans (block_start place .finish)
      rw [MultiplyBlocks.finish_effect _ _ entry]
      change FieldRefinement.address (place.origin + 382) = FieldRefinement.address place.origin + 382
      exact (BitVec.ofNat_add_ofNat place.origin 382).symm

/-- Maintained correspondence and original-image state, plus the two protected
source CALL values. These are initialized once; all later instances are proved
by executing the actual blocks. -/
structure Context (place : Placement) (x y : Word) (source : Source) (native : State) : Prop where
  agreement : Agreement place x y source native
  intact : Intact (MultiplyLayout.entries place x y) native.memory
  ready : Ready place native
  direct : source.data.memory (MultiplyPackets.layout place).entryDisplacement = 0
  back : source.data.memory (MultiplyPackets.layout place).backDisplacement = MultiplyBlocks.backDelta (MultiplyPackets.layout place)

theorem advance (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (kind : Block) (source : Source) (native : State) (context : Context place x y source native)
    (location : native.pc = FieldRefinement.address (MultiplyData.blockStart place kind))
    (zero : kind = .guard → source.data.memory (MultiplyPackets.fields place .displacement) = 0) :
    Context place x y (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) kind) source)
        (MultiplyByteBlocks.run place kind native) ∧
      MultiplyByteExecution.Trace native (MultiplyByteBlocks.forms place kind native) (MultiplyByteBlocks.run place kind native) ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat)
        (MultiplyByteBlocks.forms place kind native) native := by
  have sourceReady := source_ready place x y valid source native context.agreement context.ready
  have separate := control_separate place valid
  refine ⟨⟨block place x y valid kind source native context.agreement context.intact context.ready location context.direct context.back zero,
    MultiplyByteBlocks.run_intact place x y valid kind native context.intact context.ready,
    MultiplyByteBlocks.run_ready place x y valid kind native context.ready, ?_, ?_⟩, ?_, ?_⟩
  · rw [MultiplyBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.direct
  · rw [MultiplyBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.back
  · exact MultiplyByteBlocks.trace place x y valid kind native context.intact context.ready
      (guard_ready place x y kind source native context.agreement zero) location
  · exact MultiplyByteBlocks.owned place x y valid kind native context.ready

end SmcTuring.Appendix.MultiplyByteSimulation
