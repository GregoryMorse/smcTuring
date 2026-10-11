module
public import SmcTuring.Appendix.DivisionByteBlocks
public import SmcTuring.Appendix.DivisionExecution

public section
namespace SmcTuring.Appendix.DivisionByteSimulation

open DivisionImage DivisionSetup
abbrev State := DivisionByteExecution.State
abbrev Source := DivisionControl.State
abbrev Word := BitVec 32
attribute [local irreducible] DivisionControl.run DivisionWords.run DivisionBlocks.program
  DivisionByteBlocks.run DivisionByteBlocks.forms

/-- Only the actual disjoint represented code-operand words are related. Arbitrary
physical overlapping DWORD loads are not modeled as independent word cells. -/
structure Agreement (place : Placement) (x y : Word) (source : Source) (native : State) : Prop where
  data : FieldRefinement.Agreement (DivisionPacking.fields (DivisionLayout.entries place x y)) source.data native
  stack : native.stack = source.stack
  pc : native.pc = source.pc

@[expose] def sourceView (native : State) : Source :=
  ⟨DivisionByteBlocks.view native, native.stack, native.pc⟩

theorem view_agreement (place : Placement) (x y : Word) (native : State) :
    Agreement place x y (sourceView native) native := ⟨DivisionByteBlocks.view_agreement _ native, rfl, rfl⟩

theorem slot_word (place : Placement) (x y : Word) (source : Source) (native : State)
    (agreement : Agreement place x y source native) (slot : DivisionWords.Slot)
    (active : DivisionLayout.ActiveSlot place slot) :
    FieldRefinement.readField native (DivisionPackets.fields place slot) = source.data.memory (DivisionPackets.fields place slot) :=
  agreement.data.words _ ((DivisionPacking.fields_owned _ _).mpr (DivisionLayout.slot_owned place x y slot active))

theorem source_ready (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (source : Source) (native : State) (agreement : Agreement place x y source native) (ready : Ready place native) :
    DivisionControl.StackReady (DivisionPackets.layout place).pointer (DivisionPackets.layout place).address source := by
  have p := agreement.data.words _ ((DivisionPacking.fields_owned _ _).mpr (DivisionLayout.pointer_owned place x y))
  have a := agreement.data.words _ ((DivisionPacking.fields_owned _ _).mpr (DivisionLayout.address_owned place x y))
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

theorem continued_pc (place : Placement) (kind : Continuation) :
    FieldRefinement.address (continuationStart place kind + 30) = match kind with
      | .guard => DivisionBlocks.guardPC (DivisionPackets.layout place)
      | .body => DivisionBlocks.bodyPC (DivisionPackets.layout place)
      | .exit => DivisionBlocks.exitPC (DivisionPackets.layout place) := by
  change BitVec.ofNat 32 (continuationStart place kind + 30) = _
  rw [←BitVec.ofNat_add_ofNat]
  change FieldRefinement.address (continuationStart place kind) + 30 = _
  rw [continuation_code]
  cases kind <;> rfl

theorem end_code (place : Placement) :
    FieldRefinement.address (place.origin + DivisionLayout.pureSpan place) =
      DivisionBlocks.endPC (DivisionPackets.layout place) := by
  cases signed : place.signed <;> cases mod : place.mod <;>
    simp only [DivisionLayout.pureSpan, DivisionPackets.initialSpan, DivisionBlocks.endPC,
      DivisionBlocks.exitPC, DivisionBlocks.exitContinuation, DivisionBlocks.bodyPC,
      DivisionBlocks.bodyContinuation, DivisionBlocks.guardPC, DivisionBlocks.guardContinuation,
      DivisionBlocks.initialSpan, DivisionBlocks.finishSpan, DivisionPackets.layout,
      signed, mod, Bool.false_eq_true, ite_true, ite_false, FieldRefinement.address,
      Nat.add_assoc, Nat.reduceAdd, ←BitVec.ofNat_add_ofNat]
  case false.false =>
    change BitVec.ofNat 32 place.origin + (464 : Word) =
      BitVec.ofNat 32 place.origin + (69 : Word) + 11 + 30 + 65 + 11 + 30 + 177 + 11 + 30 + 30
    ring
  case false.true =>
    change BitVec.ofNat 32 place.origin + (464 : Word) =
      BitVec.ofNat 32 place.origin + (69 : Word) + 11 + 30 + 65 + 11 + 30 + 177 + 11 + 30 + 30
    ring
  case true.false =>
    change BitVec.ofNat 32 place.origin + (756 : Word) =
      BitVec.ofNat 32 place.origin + (318 : Word) + 11 + 30 + 65 + 11 + 30 + 177 + 11 + 30 + 73
    ring
  case true.true =>
    change BitVec.ofNat 32 place.origin + (718 : Word) =
      BitVec.ofNat 32 place.origin + (280 : Word) + 11 + 30 + 65 + 11 + 30 + 177 + 11 + 30 + 73
    ring

theorem block_start (place : Placement) (block : Block) :
    FieldRefinement.address (DivisionData.blockStart place block) = match block with
      | .initial => (DivisionPackets.layout place).origin
      | .guard => DivisionBlocks.guardPC (DivisionPackets.layout place)
      | .body => DivisionBlocks.bodyPC (DivisionPackets.layout place)
      | .finish => DivisionBlocks.exitPC (DivisionPackets.layout place) := by
  cases block with
  | initial => rfl
  | guard => simpa only [DivisionData.blockStart, continuationStart, Nat.add_assoc, Nat.reduceAdd] using continued_pc place .guard
  | body => simpa only [DivisionData.blockStart, continuationStart, Nat.add_assoc, Nat.reduceAdd] using continued_pc place .body
  | finish => simpa only [DivisionData.blockStart, continuationStart, Nat.add_assoc, Nat.reduceAdd] using continued_pc place .exit

theorem guard_ready (place : Placement) (x y : Word) (block : Block) (source : Source) (native : State)
    (agreement : Agreement place x y source native)
    (zero : block = .guard → source.data.memory (DivisionPackets.fields place .displacement) = 0) :
    DivisionByteBlocks.GuardReady place block native := by
  intro same
  rw [slot_word place x y source native agreement .displacement (by trivial)]
  exact zero same

theorem source_data_effect (place : Placement) (valid : DivisionLayout.Admissible place)
    (block : Block) (source : Source)
    (ready : DivisionControl.StackReady (DivisionPackets.layout place).pointer (DivisionPackets.layout place).address source) :
    (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) block) source).data =
      if block == .finish then DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) source.data
      else MultiplyControl.clearCarry (DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) source.data) := by
  by_cases finish : block = .finish
  · subst block
    simp only [DivisionBlocks.program, ite_true, List.append_nil, DivisionControl.lift_effect, beq_self_eq_true]
  · rw [DivisionBlocks.program_effect _ _ _ (control_separate place valid) ready finish]
    simp only [beq_iff_eq, finish, ite_false]

theorem source_stack_effect (place : Placement) (valid : DivisionLayout.Admissible place)
    (block : Block) (source : Source)
    (ready : DivisionControl.StackReady (DivisionPackets.layout place).pointer (DivisionPackets.layout place).address source) :
    (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) block) source).stack = source.stack := by
  by_cases finish : block = .finish
  · subst block
    simp only [DivisionBlocks.program, ite_true, List.append_nil, DivisionControl.lift_effect]
  · rw [DivisionBlocks.program_effect _ _ _ (control_separate place valid) ready finish]

set_option maxRecDepth 4096 in
/-- The complete block agrees on the actual resulting PC as well as all
represented data words and registers. Fixed source CALL words are initialized
once and framed; the conditional zero value is a current boundary invariant. -/
theorem block (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (kind : Block) (source : Source) (native : State) (agreement : Agreement place x y source native)
    (intact : Intact (DivisionLayout.entries place x y) native.memory) (ready : Ready place native)
    (location : native.pc = FieldRefinement.address (DivisionData.blockStart place kind))
    (direct : source.data.memory (DivisionPackets.layout place).entryDisplacement = 0)
    (back : source.data.memory (DivisionPackets.layout place).backDisplacement = DivisionBlocks.backDelta (DivisionPackets.layout place))
    (zero : kind = .guard → source.data.memory (DivisionPackets.fields place .displacement) = 0) :
    Agreement place x y (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) kind) source)
      (DivisionByteBlocks.run place kind native) := by
  have sourceReady := source_ready place x y valid source native agreement ready
  have nativeGuard := guard_ready place x y kind source native agreement zero
  have sourceLocation : source.pc = FieldRefinement.address (DivisionData.blockStart place kind) := agreement.pc.symm.trans location
  have nativePC := DivisionByteBlocks.run_pc place x y valid kind native intact ready nativeGuard location
  refine ⟨?_, ?_, ?_⟩
  · rw [source_data_effect place valid kind source sourceReady]
    exact DivisionByteBlocks.refinement place x y valid kind source.data native ready agreement.data
  · rw [source_stack_effect place valid kind source sourceReady, DivisionByteBlocks.stack place x y valid kind native ready]
    exact agreement.stack
  · rw [nativePC]
    cases kind with
    | initial =>
      have entry : source.pc = (DivisionPackets.layout place).origin := sourceLocation.trans (block_start place .initial)
      rw [DivisionBlocks.entry_effect _ _ (control_separate place valid) sourceReady entry direct]
      change FieldRefinement.address (continuationStart place .guard + 30) = _
      exact continued_pc place .guard
    | guard =>
      have entry : source.pc = DivisionBlocks.guardPC (DivisionPackets.layout place) := sourceLocation.trans (block_start place .guard)
      rw [DivisionBlocks.guard_effect _ _ (control_separate place valid) sourceReady entry (zero rfl)]
      simp only [DivisionByteBlocks.finishPC, DivisionByteBlocks.selected, beq_self_eq_true, ite_true, DivisionPackets.layout,
        slot_word place x y source native agreement .counter (by trivial),
        show (BitVec.ofNat 32 0 : Word) = (0 : Word) from rfl]
      by_cases empty : source.data.memory (DivisionPackets.fields place .counter) = (0 : Machine32.Word)
      · simp only [empty, ite_true]
        exact continued_pc place .exit
      · change FieldRefinement.address (continuationStart place
          (if source.data.memory (DivisionPackets.fields place .counter) = (0 : Machine32.Word) then .exit else .body) + 30) =
          if source.data.memory (DivisionPackets.fields place .counter) = (0 : Machine32.Word) then
            DivisionBlocks.exitPC (DivisionPackets.layout place) else DivisionBlocks.bodyPC (DivisionPackets.layout place)
        simp only [empty, ite_false]
        exact continued_pc place .body
    | body =>
      have entry : source.pc = DivisionBlocks.bodyPC (DivisionPackets.layout place) := sourceLocation.trans (block_start place .body)
      rw [DivisionBlocks.body_effect _ _ (control_separate place valid) sourceReady entry back]
      change FieldRefinement.address (continuationStart place .guard + 30) = _
      exact continued_pc place .guard
    | finish =>
      have entry : source.pc = DivisionBlocks.exitPC (DivisionPackets.layout place) := sourceLocation.trans (block_start place .finish)
      rw [DivisionBlocks.finish_effect _ _ entry]
      exact end_code place

/-- Maintained correspondence and original-image state, plus the two protected
source CALL values. These are initialized once; all later instances are proved
by executing the actual blocks. -/
structure Context (place : Placement) (x y : Word) (source : Source) (native : State) : Prop where
  agreement : Agreement place x y source native
  intact : Intact (DivisionLayout.entries place x y) native.memory
  ready : Ready place native
  direct : source.data.memory (DivisionPackets.layout place).entryDisplacement = 0
  back : source.data.memory (DivisionPackets.layout place).backDisplacement = DivisionBlocks.backDelta (DivisionPackets.layout place)

theorem advance (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (kind : Block) (source : Source) (native : State) (context : Context place x y source native)
    (location : native.pc = FieldRefinement.address (DivisionData.blockStart place kind))
    (zero : kind = .guard → source.data.memory (DivisionPackets.fields place .displacement) = 0) :
    Context place x y (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) kind) source)
        (DivisionByteBlocks.run place kind native) ∧
      DivisionByteExecution.Trace native (DivisionByteBlocks.forms place kind native) (DivisionByteBlocks.run place kind native) ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat)
        (DivisionByteBlocks.forms place kind native) native := by
  have sourceReady := source_ready place x y valid source native context.agreement context.ready
  have separate := control_separate place valid
  refine ⟨⟨block place x y valid kind source native context.agreement context.intact context.ready location context.direct context.back zero,
    DivisionByteBlocks.run_intact place x y valid kind native context.intact context.ready,
    DivisionByteBlocks.run_ready place x y valid kind native context.ready, ?_, ?_⟩, ?_, ?_⟩
  · rw [DivisionBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.direct
  · rw [DivisionBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.back
  · exact DivisionByteBlocks.trace place x y valid kind native context.intact context.ready
      (guard_ready place x y kind source native context.agreement zero) location
  · exact DivisionByteBlocks.owned place x y valid kind native context.ready

end SmcTuring.Appendix.DivisionByteSimulation
