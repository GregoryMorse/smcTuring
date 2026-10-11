module
public import SmcTuring.Appendix.DivisionByteSimulation

public section
namespace SmcTuring.Appendix.DivisionByteLoop

open DivisionImage DivisionSetup DivisionByteSimulation
abbrev State := DivisionByteExecution.State
abbrev Source := DivisionControl.State
abbrev Word := BitVec 32

-- Use the checked block interfaces instead of expanding complete instruction
-- programs during definitional unification. Kernel reduction is unchanged.
attribute [local irreducible] DivisionControl.run DivisionBlocks.program
  DivisionByteBlocks.run DivisionByteBlocks.forms DivisionExecution.loop
  DivisionByteExecution.OwnedRun DivisionImage.Owned DivisionLayout.entries

/-- Dispatch follows the executed byte PC, including the literal back edge.
The event list records each own current-memory decoding; no continuation bytes
or target are reinitialized between blocks or recursive passes. -/
@[expose] def loop : Nat → Placement → State → Option (List DivisionByteCode.Form × State)
  | fuel, place, state =>
    let tested := DivisionByteBlocks.run place .guard state
    if (tested.pc : Word).toNat = (DivisionBlocks.exitPC (DivisionPackets.layout place) : Word).toNat then
      some (DivisionByteBlocks.forms place .guard state ++ DivisionByteBlocks.forms place .finish tested, DivisionByteBlocks.run place .finish tested)
    else if (tested.pc : Word).toNat = (DivisionBlocks.bodyPC (DivisionPackets.layout place) : Word).toNat then
      match fuel with
      | 0 => none
      | remaining + 1 =>
        (loop remaining place (DivisionByteBlocks.run place .body tested)).map
          (fun result => (DivisionByteBlocks.forms place .guard state ++ DivisionByteBlocks.forms place .body tested ++ result.1, result.2))
    else none

@[expose] def divide (place : Placement) (state : State) : Option (List DivisionByteCode.Form × State) :=
  (loop 32 place (DivisionByteBlocks.run place .initial state)).map
    (fun result => (DivisionByteBlocks.forms place .initial state ++ result.1, result.2))

/-- A pointwise dispatch equation proved by structural reduction. This keeps
symbolic block executions folded when rewriting the continuous loop. -/
theorem loop_step (fuel : Nat) (place : Placement) (state : State) :
    loop fuel place state =
      let tested := DivisionByteBlocks.run place .guard state
      if (tested.pc : Word).toNat = (DivisionBlocks.exitPC (DivisionPackets.layout place) : Word).toNat then
        some (DivisionByteBlocks.forms place .guard state ++ DivisionByteBlocks.forms place .finish tested, DivisionByteBlocks.run place .finish tested)
      else if (tested.pc : Word).toNat = (DivisionBlocks.bodyPC (DivisionPackets.layout place) : Word).toNat then
        match fuel with
        | 0 => none
        | remaining + 1 =>
          (loop remaining place (DivisionByteBlocks.run place .body tested)).map
            (fun result => (DivisionByteBlocks.forms place .guard state ++ DivisionByteBlocks.forms place .body tested ++ result.1, result.2))
      else none := by
  cases fuel <;> rfl

attribute [local irreducible] loop

theorem entry_location (place : Placement) (x y : Word) (source : Source) (native : State)
    (agreement : Agreement place x y source native) (kind : Block)
    (location : source.pc = FieldRefinement.address (DivisionData.blockStart place kind)) :
    native.pc = FieldRefinement.address (DivisionData.blockStart place kind) := agreement.pc.trans location

/-- Reaching BODY implies the zero-test was false, so the executed body and
back edge restore the actual guard PC and preserve zero displacement. -/
theorem body_boundary (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (DivisionData.blockStart place .guard))
    (zero : source.data.memory (DivisionPackets.fields place .displacement) = 0)
    (taken : (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source).pc = DivisionBlocks.bodyPC (DivisionPackets.layout place)) :
    let after := DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .body)
      (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source)
    after.pc = DivisionBlocks.guardPC (DivisionPackets.layout place) ∧
      after.data.memory (DivisionPackets.fields place .displacement) = 0 := by
  let layout := DivisionPackets.layout place
  let tested := DivisionControl.run (DivisionBlocks.program layout .guard) source
  have separate : DivisionBlocks.Separate layout := control_separate place valid
  have sourceReady : DivisionControl.StackReady layout.pointer layout.address source := source_ready place x y valid source native context.agreement context.ready
  have sourceEntry : source.pc = DivisionBlocks.guardPC layout :=
    context.agreement.pc.symm.trans (entry.trans (block_start place .guard))
  have testedEffect := DivisionBlocks.guard_effect layout source separate sourceReady sourceEntry zero
  have nonzero : source.data.memory (DivisionPackets.fields place .counter) ≠ 0 := by
    intro empty
    have exited : tested.pc = DivisionBlocks.exitPC layout := by
      dsimp only [tested]
      rw [testedEffect]
      simp only [layout, DivisionPackets.layout, empty, ite_true]
    exact DivisionBlocks.continuations_distinct layout (exited.symm.trans taken)
  have testedReady := DivisionBlocks.program_ready layout .guard source separate sourceReady
  have testedBack : tested.data.memory layout.backDisplacement = DivisionBlocks.backDelta layout := by
    rw [DivisionBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.back
  have afterEffect := DivisionBlocks.body_effect layout tested separate testedReady taken testedBack
  constructor
  · change (DivisionControl.run (DivisionBlocks.program layout .body) tested).pc = DivisionBlocks.guardPC layout
    rw [afterEffect]
  · change (DivisionControl.run (DivisionBlocks.program layout .body) tested).data.memory (DivisionPackets.fields place .displacement) = 0
    rw [afterEffect]
    change (DivisionWords.run (DivisionWords.body layout.fields) tested.data).memory (layout.fields .displacement) = 0
    rw [DivisionBody.body_field _ _ separate.data .displacement]
    change tested.data.memory (DivisionPackets.fields place .displacement) = 0
    dsimp only [tested]
    rw [testedEffect]
    change (DivisionWords.run (DivisionGuard.program layout.fields (DivisionBlocks.delta layout)) source.data).memory
      (layout.fields .displacement) = 0
    rw [DivisionGuard.displacement _ _ _ separate.data zero]
    change (if source.data.memory (DivisionPackets.fields place .counter) = (0 : Machine32.Word)
      then DivisionBlocks.delta layout else (0 : Machine32.Word)) = 0
    simp only [nonzero, ite_false]

theorem exit_simulate (fuel : Nat) (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (DivisionData.blockStart place .guard))
    (zero : source.data.memory (DivisionPackets.fields place .displacement) = 0)
    (commands : List DivisionControl.Instruction) (sourceFinal : Source)
    (execution : DivisionExecution.loop fuel (DivisionPackets.layout place) source = some (commands, sourceFinal))
    (exited : (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source).pc = DivisionBlocks.exitPC (DivisionPackets.layout place)) :
    ∃ events final, loop fuel place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native := by
  have leading := advance place x y valid .guard source native context entry (fun _ => zero)
  let tested := DivisionByteBlocks.run place .guard native
  have testedExit : tested.pc = DivisionBlocks.exitPC (DivisionPackets.layout place) := leading.1.agreement.pc.trans exited
  have location : tested.pc = FieldRefinement.address (DivisionData.blockStart place .finish) := testedExit.trans (block_start place .finish).symm
  have trailing := advance place x y valid .finish _ tested leading.1 location (by intro impossible; cases impossible)
  have finalSource : DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .finish)
      (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source) = sourceFinal := by
    cases fuel <;> rw [DivisionExecution.loop] at execution
    all_goals rw [exited, ite_eq_left rfl] at execution
    all_goals exact congrArg (fun pair => pair.2) (Option.some.inj execution)
  refine Exists.intro (DivisionByteBlocks.forms place .guard native ++ DivisionByteBlocks.forms place .finish tested) ?_
  refine Exists.intro (DivisionByteBlocks.run place .finish tested) ?_
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · rewrite [loop_step]
    dsimp only
    have chosen : ((DivisionByteBlocks.run place .guard native).pc : Word).toNat =
        (DivisionBlocks.exitPC (DivisionPackets.layout place) : Word).toNat :=
      congrArg (fun word : Word => word.toNat) testedExit
    rw [ite_eq_left chosen]
  · rw [←finalSource]; exact trailing.1
  · exact DivisionByteExecution.trace_append leading.2.1 trailing.2.1
  · rw [DivisionByteExecution.owned_append, DivisionByteBlocks.forms_run]
    exact ⟨leading.2.2, trailing.2.2⟩

/-- Internal simulation of an already constructed WORD loop. The public
original-image theorem constructs that source execution from the all-input
word result. Every reached byte boundary, guard-zero value, future current
fetch and owned write is proved inductively from the initial context. -/
theorem simulate (fuel : Nat) (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (DivisionData.blockStart place .guard))
    (zero : source.data.memory (DivisionPackets.fields place .displacement) = 0)
    (commands : List DivisionControl.Instruction) (sourceFinal : Source)
    (execution : DivisionExecution.loop fuel (DivisionPackets.layout place) source = some (commands, sourceFinal)) :
    ∃ events final, loop fuel place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native := by
  induction fuel generalizing source native commands sourceFinal with
  | zero =>
    by_cases exited : (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source).pc = DivisionBlocks.exitPC (DivisionPackets.layout place)
    · exact exit_simulate _ place x y valid source native context entry zero commands sourceFinal execution exited
    · simp only [DivisionExecution.loop, exited, ite_false] at execution
      cases execution
  | succ fuel ih =>
    by_cases exited : (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source).pc = DivisionBlocks.exitPC (DivisionPackets.layout place)
    · exact exit_simulate _ place x y valid source native context entry zero commands sourceFinal execution exited
    · by_cases taken : (DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source).pc = DivisionBlocks.bodyPC (DivisionPackets.layout place)
      · have leading := advance place x y valid .guard source native context entry (fun _ => zero)
        let tested := DivisionByteBlocks.run place .guard native
        let sourceTested := DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .guard) source
        have testedPC : tested.pc = DivisionBlocks.bodyPC (DivisionPackets.layout place) := leading.1.agreement.pc.trans taken
        have testedLocation : tested.pc = FieldRefinement.address (DivisionData.blockStart place .body) := testedPC.trans (block_start place .body).symm
        have middle := advance place x y valid .body sourceTested tested leading.1 testedLocation (by intro impossible; cases impossible)
        let after := DivisionByteBlocks.run place .body tested
        let sourceAfter := DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .body) sourceTested
        have boundary := body_boundary place x y valid source native context entry zero taken
        have afterLocation : after.pc = FieldRefinement.address (DivisionData.blockStart place .guard) :=
          middle.1.agreement.pc.trans (boundary.1.trans (block_start place .guard).symm)
        rw [DivisionExecution.loop, ite_eq_right exited, ite_eq_left taken] at execution
        obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp execution
        obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ :=
          ih sourceAfter after middle.1 afterLocation boundary.2 result.1 result.2 recursive
        have finalSource : result.2 = sourceFinal := (Prod.mk.inj equality).2
        refine Exists.intro (DivisionByteBlocks.forms place .guard native ++ DivisionByteBlocks.forms place .body tested ++ events) ?_
        refine Exists.intro final ?_
        refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
        · rewrite [loop_step]
          dsimp only
          have chosen : ((DivisionByteBlocks.run place .guard native).pc : Word).toNat =
              (DivisionBlocks.bodyPC (DivisionPackets.layout place) : Word).toNat :=
            congrArg (fun word : Word => word.toNat) testedPC
          rw [ite_eq_right (by
              intro impossible
              have same : tested.pc = DivisionBlocks.exitPC (DivisionPackets.layout place) :=
                BitVec.eq_of_toNat_eq impossible
              exact exited (leading.1.agreement.pc.symm.trans same)), ite_eq_left chosen]
          change (loop fuel place after).map _ = _
          rw [byteExecution]; rfl
        · rw [←finalSource]; exact finalContext
        · exact DivisionByteExecution.trace_append
            (DivisionByteExecution.trace_append leading.2.1 middle.2.1) trace
        · rw [DivisionByteExecution.owned_append, DivisionByteExecution.owned_append,
            DivisionByteBlocks.forms_run, DivisionByteExecution.run_append, DivisionByteBlocks.forms_run,
            DivisionByteBlocks.forms_run]
          exact ⟨⟨leading.2.2, middle.2.2⟩, owned⟩
      · rw [DivisionExecution.loop, ite_eq_right exited, ite_eq_right taken] at execution
        cases execution

end SmcTuring.Appendix.DivisionByteLoop
