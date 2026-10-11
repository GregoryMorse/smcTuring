module
public import SmcTuring.Appendix.MultiplyByteSimulation

public section
namespace SmcTuring.Appendix.MultiplyByteLoop

open MultiplyImage MultiplySetup MultiplyByteSimulation
abbrev State := MultiplyByteExecution.State
abbrev Source := MultiplyControl.State
abbrev Word := BitVec 32

-- Use the checked block interfaces instead of expanding complete instruction
-- programs during definitional unification. Kernel reduction is unchanged.
attribute [local irreducible] MultiplyControl.run MultiplyBlocks.program
  MultiplyByteBlocks.run MultiplyByteBlocks.forms

/-- Dispatch follows the executed byte PC, including the literal back edge.
The event list records each own current-memory decoding; no continuation bytes
or target are reinitialized between blocks or recursive passes. -/
@[expose] def loop : Nat → Placement → State → Option (List MultiplyByteCode.Form × State)
  | fuel, place, state =>
    let tested := MultiplyByteBlocks.run place .guard state
    if (tested.pc : Word).toNat = (MultiplyBlocks.exitPC (MultiplyPackets.layout place) : Word).toNat then
      some (MultiplyByteBlocks.forms place .guard state ++ MultiplyByteBlocks.forms place .finish tested, MultiplyByteBlocks.run place .finish tested)
    else if (tested.pc : Word).toNat = (MultiplyBlocks.bodyPC (MultiplyPackets.layout place) : Word).toNat then
      match fuel with
      | 0 => none
      | remaining + 1 =>
        (loop remaining place (MultiplyByteBlocks.run place .body tested)).map
          (fun result => (MultiplyByteBlocks.forms place .guard state ++ MultiplyByteBlocks.forms place .body tested ++ result.1, result.2))
    else none

@[expose] def multiply (place : Placement) (state : State) : Option (List MultiplyByteCode.Form × State) :=
  (loop 32 place (MultiplyByteBlocks.run place .initial state)).map
    (fun result => (MultiplyByteBlocks.forms place .initial state ++ result.1, result.2))

theorem entry_location (place : Placement) (x y : Word) (source : Source) (native : State)
    (agreement : Agreement place x y source native) (kind : Block)
    (location : source.pc = FieldRefinement.address (MultiplyData.blockStart place kind)) :
    native.pc = FieldRefinement.address (MultiplyData.blockStart place kind) := agreement.pc.trans location

/-- Reaching BODY implies the zero-test was false, so the executed body and
back edge restore the actual guard PC and preserve zero displacement. -/
theorem body_boundary (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (MultiplyData.blockStart place .guard))
    (zero : source.data.memory (MultiplyPackets.fields place .displacement) = 0)
    (taken : (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source).pc = MultiplyBlocks.bodyPC (MultiplyPackets.layout place)) :
    let after := MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .body)
      (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source)
    after.pc = MultiplyBlocks.guardPC (MultiplyPackets.layout place) ∧
      after.data.memory (MultiplyPackets.fields place .displacement) = 0 := by
  let layout := MultiplyPackets.layout place
  let tested := MultiplyControl.run (MultiplyBlocks.program layout .guard) source
  have separate : MultiplyBlocks.Separate layout := control_separate place valid
  have sourceReady : MultiplyControl.StackReady layout.pointer layout.address source := source_ready place x y valid source native context.agreement context.ready
  have sourceEntry : source.pc = MultiplyBlocks.guardPC layout :=
    context.agreement.pc.symm.trans (entry.trans (block_start place .guard))
  have testedEffect := MultiplyBlocks.guard_effect layout source separate sourceReady sourceEntry zero
  have nonzero : source.data.memory (MultiplyPackets.fields place .multiplier) ≠ 0 := by
    intro empty
    have exited : tested.pc = MultiplyBlocks.exitPC layout := by
      dsimp only [tested]
      rw [testedEffect]
      simp only [layout, MultiplyPackets.layout, empty, ite_true]
    exact MultiplyBlocks.continuations_distinct layout (exited.symm.trans taken)
  have testedReady := MultiplyBlocks.program_ready layout .guard source separate sourceReady
  have testedBack : tested.data.memory layout.backDisplacement = MultiplyBlocks.backDelta layout := by
    rw [MultiplyBlocks.program_frame _ _ _ separate sourceReady _ (separate.outside _ (by simp))]
    exact context.back
  have afterEffect := MultiplyBlocks.body_effect layout tested separate testedReady taken testedBack
  constructor
  · change (MultiplyControl.run (MultiplyBlocks.program layout .body) tested).pc = MultiplyBlocks.guardPC layout
    rw [afterEffect]
  · change (MultiplyControl.run (MultiplyBlocks.program layout .body) tested).data.memory (MultiplyPackets.fields place .displacement) = 0
    rw [afterEffect]
    change (MultiplyWords.run (MultiplyWords.body layout.fields) tested.data).memory (layout.fields .displacement) = 0
    rw [MultiplyWords.body_field _ _ separate.data .displacement]
    change tested.data.memory (MultiplyPackets.fields place .displacement) = 0
    dsimp only [tested]
    rw [testedEffect]
    change (MultiplyWords.run (MultiplyWords.guard layout.fields (MultiplyBlocks.delta layout)) source.data).memory
      (layout.fields .displacement) = 0
    rw [MultiplyWords.guard_displacement _ _ _ separate.data zero]
    change (if source.data.memory (MultiplyPackets.fields place .multiplier) = (0 : Machine32.Word)
      then MultiplyBlocks.delta layout else (0 : Machine32.Word)) = 0
    simp only [nonzero, ite_false]

theorem exit_simulate (fuel : Nat) (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (MultiplyData.blockStart place .guard))
    (zero : source.data.memory (MultiplyPackets.fields place .displacement) = 0)
    (commands : List MultiplyControl.Instruction) (sourceFinal : Source)
    (execution : MultiplyExecution.loop fuel (MultiplyPackets.layout place) source = some (commands, sourceFinal))
    (exited : (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source).pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place)) :
    ∃ events final, loop fuel place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ MultiplyByteExecution.Trace native events final ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat) events native := by
  have leading := advance place x y valid .guard source native context entry (fun _ => zero)
  let tested := MultiplyByteBlocks.run place .guard native
  have testedExit : tested.pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place) := leading.1.agreement.pc.trans exited
  have location : tested.pc = FieldRefinement.address (MultiplyData.blockStart place .finish) := testedExit.trans (block_start place .finish).symm
  have trailing := advance place x y valid .finish _ tested leading.1 location (by intro impossible; cases impossible)
  rw [MultiplyExecution.loop.eq_def] at execution
  dsimp only at execution
  rw [exited, ite_eq_left rfl] at execution
  have finalSource : MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .finish)
      (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source) = sourceFinal :=
    congrArg (fun pair => pair.2) (Option.some.inj execution)
  refine ⟨MultiplyByteBlocks.forms place .guard native ++ MultiplyByteBlocks.forms place .finish tested, MultiplyByteBlocks.run place .finish tested, ?_, ?_, ?_, ?_⟩
  · rw [loop.eq_def]
    dsimp only
    have chosen : ((MultiplyByteBlocks.run place .guard native).pc : Word).toNat =
        (MultiplyBlocks.exitPC (MultiplyPackets.layout place) : Word).toNat :=
      congrArg (fun word : Word => word.toNat) testedExit
    rw [ite_eq_left chosen]
  · rw [←finalSource]; exact trailing.1
  · exact MultiplyByteExecution.trace_append leading.2.1 trailing.2.1
  · rw [MultiplyByteExecution.owned_append, MultiplyByteBlocks.forms_run]
    exact ⟨leading.2.2, trailing.2.2⟩

/-- Internal simulation of an already constructed WORD loop. The public
original-image theorem constructs that source execution from the all-input
word result. Every reached byte boundary, guard-zero value, future current
fetch and owned write is proved inductively from the initial context. -/
theorem simulate (fuel : Nat) (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address (MultiplyData.blockStart place .guard))
    (zero : source.data.memory (MultiplyPackets.fields place .displacement) = 0)
    (commands : List MultiplyControl.Instruction) (sourceFinal : Source)
    (execution : MultiplyExecution.loop fuel (MultiplyPackets.layout place) source = some (commands, sourceFinal)) :
    ∃ events final, loop fuel place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ MultiplyByteExecution.Trace native events final ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat) events native := by
  induction fuel generalizing source native commands sourceFinal with
  | zero =>
    by_cases exited : (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source).pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place)
    · exact exit_simulate _ place x y valid source native context entry zero commands sourceFinal execution exited
    · simp only [MultiplyExecution.loop, exited, ite_false] at execution
      simp only [ite_self] at execution
      contradiction
  | succ fuel ih =>
    by_cases exited : (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source).pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place)
    · exact exit_simulate _ place x y valid source native context entry zero commands sourceFinal execution exited
    · by_cases taken : (MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source).pc = MultiplyBlocks.bodyPC (MultiplyPackets.layout place)
      · have leading := advance place x y valid .guard source native context entry (fun _ => zero)
        let tested := MultiplyByteBlocks.run place .guard native
        let sourceTested := MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .guard) source
        have testedPC : tested.pc = MultiplyBlocks.bodyPC (MultiplyPackets.layout place) := leading.1.agreement.pc.trans taken
        have testedLocation : tested.pc = FieldRefinement.address (MultiplyData.blockStart place .body) := testedPC.trans (block_start place .body).symm
        have middle := advance place x y valid .body sourceTested tested leading.1 testedLocation (by intro impossible; cases impossible)
        let after := MultiplyByteBlocks.run place .body tested
        let sourceAfter := MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .body) sourceTested
        have boundary := body_boundary place x y valid source native context entry zero taken
        have afterLocation : after.pc = FieldRefinement.address (MultiplyData.blockStart place .guard) :=
          middle.1.agreement.pc.trans (boundary.1.trans (block_start place .guard).symm)
        rw [MultiplyExecution.loop, ite_eq_right exited, ite_eq_left taken] at execution
        cases recursive : MultiplyExecution.loop fuel (MultiplyPackets.layout place) sourceAfter with
        | none => rw [recursive] at execution; contradiction
        | some result =>
          obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ :=
            ih sourceAfter after middle.1 afterLocation boundary.2 result.1 result.2 recursive
          rw [recursive] at execution
          have finalSource : result.2 = sourceFinal := congrArg (fun pair => pair.2) (Option.some.inj execution)
          refine ⟨MultiplyByteBlocks.forms place .guard native ++ MultiplyByteBlocks.forms place .body tested ++ events, final, ?_, ?_, ?_, ?_⟩
          · have chosen : ((MultiplyByteBlocks.run place .guard native).pc : Word).toNat =
                (MultiplyBlocks.bodyPC (MultiplyPackets.layout place) : Word).toNat :=
              congrArg (fun word : Word => word.toNat) testedPC
            rw [loop, ite_eq_right (by
                intro impossible
                have same : tested.pc = MultiplyBlocks.exitPC (MultiplyPackets.layout place) := BitVec.eq_of_toNat_eq impossible
                exact exited (leading.1.agreement.pc.symm.trans same)), ite_eq_left chosen]
            change (loop fuel place after).map _ = _
            rw [byteExecution]; rfl
          · rw [←finalSource]; exact finalContext
          · exact MultiplyByteExecution.trace_append
              (MultiplyByteExecution.trace_append leading.2.1 middle.2.1) trace
          · rw [MultiplyByteExecution.owned_append, MultiplyByteExecution.owned_append,
              MultiplyByteBlocks.forms_run, MultiplyByteExecution.run_append, MultiplyByteBlocks.forms_run,
              MultiplyByteBlocks.forms_run]
            exact ⟨⟨leading.2.2, middle.2.2⟩, owned⟩
      · rw [MultiplyExecution.loop, ite_eq_right exited, ite_eq_right taken] at execution
        contradiction

end SmcTuring.Appendix.MultiplyByteLoop
