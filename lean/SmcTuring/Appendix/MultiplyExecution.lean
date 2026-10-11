module
public import SmcTuring.Appendix.MultiplyBlocks

public section
namespace SmcTuring.Appendix.MultiplyExecution
open MultiplyControl MultiplyBlocks

/-- Dispatch uses the actual CALL/continuation PC. The listed instructions are
executed individually; no branch outcome or future stack state is supplied. -/
@[expose] def loop : Nat -> Layout -> State -> Option (List Instruction × State)
  | fuel, layout, state =>
    let tested := run (program layout .guard) state
    if tested.pc = exitPC layout then
      some (program layout .guard ++ program layout .finish, run (program layout .finish) tested)
    else if tested.pc = bodyPC layout then
      match fuel with
      | 0 => none
      | remaining + 1 =>
        (loop remaining layout (run (program layout .body) tested)).map
          (fun result => (program layout .guard ++ program layout .body ++ result.1, result.2))
    else none

@[expose] def multiply (layout : Layout) (state : State) : Option (List Instruction × State) :=
  (loop 32 layout (run (program layout .initial) state)).map
    (fun result => (program layout .initial ++ result.1, result.2))

theorem exit_matches (fuel : Nat) (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = guardPC layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (zero : state.data.memory (layout.fields .multiplier) = 0)
    (dataProgram : List MultiplyWords.Instruction) (dataFinal : Machine32.State)
    (trace : MultiplyLoop.loop fuel layout.fields (delta layout) state.data = some (dataProgram, dataFinal)) :
    ∃ commands final, loop fuel layout state = some (commands, final) ∧ final.data = dataFinal ∧
      final.stack = state.stack ∧ final.pc = endPC layout := by
  change state.data.memory (layout.fields .multiplier) = BitVec.ofNat 32 0 at zero
  have nonzero := delta_nonzero layout
  have displacement : (MultiplyWords.run (MultiplyWords.guard layout.fields (delta layout)) state.data).memory (layout.fields .displacement) = delta layout := by
    rw [MultiplyWords.guard_displacement _ _ _ separate.data initial]
    simp [zero]
  have exited : MultiplyLoop.loop fuel layout.fields (delta layout) state.data =
      some (MultiplyWords.guard layout.fields (delta layout) ++ MultiplyWords.finish layout.fields,
        MultiplyWords.run (MultiplyWords.finish layout.fields) (MultiplyWords.run (MultiplyWords.guard layout.fields (delta layout)) state.data)) := by
    cases fuel <;> rw [MultiplyLoop.loop, displacement, ite_eq_right nonzero]
  rw [exited] at trace
  have dataEnd : MultiplyWords.run (MultiplyWords.finish layout.fields)
      (MultiplyWords.run (MultiplyWords.guard layout.fields (delta layout)) state.data) = dataFinal :=
    congrArg (fun pair => pair.2) (Option.some.inj trace)
  have tested : run (program layout .guard) state =
      { data := MultiplyWords.run (words layout .guard) state.data, stack := state.stack, pc := exitPC layout } := by
    simpa [zero] using guard_effect layout state separate ready entry initial
  have pc : (run (program layout .guard) state).pc = exitPC layout := by rw [tested]
  have finished := finish_effect layout (run (program layout .guard) state) pc
  refine ⟨program layout .guard ++ program layout .finish, run (program layout .finish) (run (program layout .guard) state), ?_, ?_, ?_, ?_⟩
  · rw [loop.eq_def]
    dsimp only
    rw [pc, ite_eq_left rfl]
  · rw [finished, tested]
    exact dataEnd
  · rw [finished, tested]
  · rw [finished]

theorem loop_matches (fuel : Nat) (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = guardPC layout)
    (back : state.data.memory layout.backDisplacement = backDelta layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (dataProgram : List MultiplyWords.Instruction) (dataFinal : Machine32.State)
    (trace : MultiplyLoop.loop fuel layout.fields (delta layout) state.data = some (dataProgram, dataFinal)) :
    ∃ commands final, loop fuel layout state = some (commands, final) ∧ final.data = dataFinal ∧
      final.stack = state.stack ∧ final.pc = endPC layout := by
  induction fuel generalizing state dataProgram dataFinal with
  | zero =>
      by_cases zero : state.data.memory (layout.fields .multiplier) = BitVec.ofNat 32 0
      · exact exit_matches _ _ _ separate ready entry initial zero _ _ trace
      · have displacement : (MultiplyWords.run (MultiplyWords.guard layout.fields (delta layout)) state.data).memory (layout.fields .displacement) = 0 := by
          rw [MultiplyWords.guard_displacement _ _ _ separate.data initial]
          simp [zero]
        rw [MultiplyLoop.loop, displacement, ite_eq_left rfl] at trace
        contradiction
  | succ fuel ih =>
      by_cases zero : state.data.memory (layout.fields .multiplier) = BitVec.ofNat 32 0
      · exact exit_matches _ _ _ separate ready entry initial zero _ _ trace
      · let tested := run (program layout .guard) state
        let after := run (program layout .body) tested
        let dataAfter := MultiplyWords.run (words layout .body) (MultiplyWords.run (words layout .guard) state.data)
        have testedEffect : run (program layout .guard) state =
            { data := MultiplyWords.run (words layout .guard) state.data, stack := state.stack, pc := bodyPC layout } := by
          simpa [zero] using guard_effect layout state separate ready entry initial
        have testedPC : tested.pc = bodyPC layout := by
          dsimp only [tested]
          rw [testedEffect]
        have testedReady : StackReady layout.pointer layout.address tested := program_ready layout .guard state separate ready
        have testedBack : tested.data.memory layout.backDisplacement = backDelta layout := by
          rw [program_frame layout .guard state separate ready layout.backDisplacement (separate.outside _ (by simp))]
          exact back
        have afterEffect : after = { data := clearCarry dataAfter, stack := state.stack, pc := guardPC layout } := by
          dsimp only [after]
          rw [body_effect layout tested separate testedReady testedPC testedBack]
          dsimp only [tested]
          rw [testedEffect]
        have afterReady : StackReady layout.pointer layout.address after := program_ready layout .body tested separate testedReady
        have afterPC : after.pc = guardPC layout := by rw [afterEffect]
        have afterBack : after.data.memory layout.backDisplacement = backDelta layout := by
          rw [program_frame layout .body tested separate testedReady layout.backDisplacement (separate.outside _ (by simp))]
          exact testedBack
        have afterInitial : after.data.memory (layout.fields .displacement) = 0 := by
          rw [afterEffect]
          simp only [clearCarry, dataAfter, words, MultiplyWords.body_field _ _ separate.data,
            MultiplyWords.bodyValue, MultiplyWords.guard_displacement _ _ _ separate.data initial]
          simp [zero]
        have displacement : (MultiplyWords.run (MultiplyWords.guard layout.fields (delta layout)) state.data).memory (layout.fields .displacement) = 0 := by
          rw [MultiplyWords.guard_displacement _ _ _ separate.data initial]
          simp [zero]
        rw [MultiplyLoop.loop, displacement, ite_eq_left rfl] at trace
        cases h : MultiplyLoop.loop fuel layout.fields (delta layout) dataAfter with
        | none => simp only [words, dataAfter] at h; rw [h] at trace; contradiction
        | some result =>
            have recursive : MultiplyLoop.loop fuel layout.fields (delta layout) after.data = some result := by
              rw [afterEffect]
              simpa only [clearCarry, MultiplyControl.loop_ignore_carry] using h
            obtain ⟨commands, final, fullTrace, finalData, finalStack, finalPC⟩ :=
              ih after afterReady afterPC afterBack afterInitial result.1 result.2 recursive
            have dataEnd : result.2 = dataFinal := by
              simp only [words, dataAfter] at h
              rw [h] at trace
              exact congrArg (fun pair => pair.2) (Option.some.inj trace)
            refine ⟨program layout .guard ++ program layout .body ++ commands, final, ?_, finalData.trans dataEnd, ?_, finalPC⟩
            · rw [loop, show (run (program layout .guard) state).pc = bodyPC layout from testedPC,
                ite_eq_right (Ne.symm (continuations_distinct layout)), ite_eq_left rfl]
              change (loop fuel layout after).map _ = _
              rw [fullTrace]
              rfl
            · rw [finalStack, afterEffect]

theorem loop_run (fuel : Nat) (layout : Layout) (state : State) (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) : run commands state = final := by
  induction fuel generalizing state commands final with
  | zero =>
      simp only [loop] at trace
      split at trace
      · cases trace; exact run_append _ _ _
      · split at trace <;> contradiction
  | succ fuel ih =>
      simp only [loop] at trace
      split at trace
      · cases trace; exact run_append _ _ _
      · split at trace
        · cases h : loop fuel layout (run (program layout .body) (run (program layout .guard) state)) with
          | none => simp only [h, Option.map_none] at trace; contradiction
          | some result =>
              simp only [h, Option.map_some, Option.some.injEq] at trace
              cases trace
              rw [run_append, run_append]
              exact ih _ _ _ h
        · contradiction

theorem loop_pure (fuel : Nat) (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) (codeField : Nat -> Prop)
    (owned : ∀ slot, codeField (layout.fields slot)) (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    PureRun codeField commands state := by
  induction fuel generalizing state commands final with
  | zero =>
      simp only [loop] at trace
      split at trace
      · cases trace
        exact (pure_append _ _ _ _).mpr ⟨program_pure _ _ _ separate ready codeField owned pointerOwned addressOwned,
          program_pure _ _ _ separate (program_ready _ _ _ separate ready) codeField owned pointerOwned addressOwned⟩
      · split at trace <;> contradiction
  | succ fuel ih =>
      simp only [loop] at trace
      split at trace
      · cases trace
        exact (pure_append _ _ _ _).mpr ⟨program_pure _ _ _ separate ready codeField owned pointerOwned addressOwned,
          program_pure _ _ _ separate (program_ready _ _ _ separate ready) codeField owned pointerOwned addressOwned⟩
      · split at trace
        · cases h : loop fuel layout (run (program layout .body) (run (program layout .guard) state)) with
          | none => simp only [h, Option.map_none] at trace; contradiction
          | some result =>
              simp only [h, Option.map_some, Option.some.injEq] at trace
              cases trace
              rw [pure_append, pure_append, run_append]
              have testedReady := program_ready layout .guard state separate ready
              exact ⟨⟨program_pure _ _ _ separate ready codeField owned pointerOwned addressOwned,
                program_pure _ _ _ separate testedReady codeField owned pointerOwned addressOwned⟩,
                ih _ (program_ready _ _ _ separate testedReady) _ _ h⟩
        · contradiction

structure Spec (layout : Layout) (initial final : State) : Prop where
  product : final.data.memory (layout.fields .result) = initial.data.memory (layout.fields .x) * initial.data.memory (layout.fields .y)
  accumulator : final.data.accumulator = initial.data.accumulator
  stack : final.stack = initial.stack
  carry : final.data.carry = false
  displacement : final.data.memory (layout.fields .displacement) = 0
  inputX : final.data.memory (layout.fields .x) = initial.data.memory (layout.fields .x)
  inputY : final.data.memory (layout.fields .y) = initial.data.memory (layout.fields .y)
  pc : final.pc = endPC layout
  frame : ∀ field, (∀ slot, field ≠ layout.fields slot) -> final.data.memory field = initial.data.memory field

theorem correct (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = layout.origin)
    (direct : state.data.memory layout.entryDisplacement = 0)
    (back : state.data.memory layout.backDisplacement = backDelta layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (codeField : Nat -> Prop) (owned : ∀ slot, codeField (layout.fields slot))
    (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    ∃ commands final, multiply layout state = some (commands, final) ∧ run commands state = final ∧
      PureRun codeField commands state ∧ Spec layout state final := by
  let started := run (program layout .initial) state
  have startEffect := entry_effect layout state separate ready entry direct
  have startReady : StackReady layout.pointer layout.address started := program_ready layout .initial state separate ready
  have startPC : started.pc = guardPC layout := by
    dsimp only [started]
    rw [startEffect]
  have startBack : started.data.memory layout.backDisplacement = backDelta layout := by
    rw [program_frame layout .initial state separate ready layout.backDisplacement (separate.outside _ (by simp))]
    exact back
  have startInitial : started.data.memory (layout.fields .displacement) = 0 := by
    dsimp only [started]
    rw [startEffect]
    simpa only [clearCarry, words, MultiplyWords.initialize_field _ _ separate.data] using initial
  obtain ⟨dataProgram, dataFinal, dataTrace, post⟩ := MultiplyLoop.loop_correct 32 layout.fields (delta layout) started.data
    separate.data (delta_nonzero layout) startInitial (started.data.memory (layout.fields .multiplier)).isLt
  obtain ⟨commands, final, fullTrace, finalData, finalStack, finalPC⟩ :=
    loop_matches 32 layout started separate startReady startPC startBack startInitial dataProgram dataFinal dataTrace
  have originalTrace : MultiplyLoop.loop 32 layout.fields (delta layout) (MultiplyWords.run (words layout .initial) state.data) = some (dataProgram, dataFinal) := by
    dsimp only [started] at dataTrace
    rw [startEffect] at dataTrace
    simpa only [clearCarry, MultiplyControl.loop_ignore_carry] using dataTrace
  have wordTrace : MultiplyLoop.multiply layout.fields (delta layout) state.data =
      some (MultiplyWords.initialProgram layout.fields ++ dataProgram, dataFinal) := by
    simp only [MultiplyLoop.multiply, words] at originalTrace ⊢
    rw [originalTrace]; rfl
  refine ⟨program layout .initial ++ commands, final, ?_, ?_, ?_, ?_⟩
  · simp only [multiply]
    change (loop 32 layout started).map _ = _
    rw [fullTrace]; rfl
  · rw [run_append]; exact loop_run _ _ _ _ _ fullTrace
  · exact (pure_append _ _ _ _).mpr ⟨program_pure _ _ _ separate ready codeField owned pointerOwned addressOwned,
      loop_pure _ _ _ separate startReady _ _ fullTrace codeField owned pointerOwned addressOwned⟩
  · constructor
    · rw [finalData, post.product]
      dsimp only [started]
      rw [startEffect]
      simp only [MultiplyLoop.invariant, clearCarry, words, MultiplyWords.initialize_field _ _ separate.data, zero_add]
    · rw [finalData, post.accumulator]
      dsimp only [started]
      rw [startEffect]
      exact MultiplyWords.initialize_accumulator _ _ separate.data
    · rw [finalStack]
      dsimp only [started]
      rw [startEffect]
    · rw [finalData]; exact post.carry
    · rw [finalData]; exact post.displacement
    · rw [finalData, post.inputX]
      dsimp only [started]
      rw [startEffect]
      exact MultiplyWords.initialize_field _ _ separate.data .x
    · rw [finalData, post.inputY]
      dsimp only [started]
      rw [startEffect]
      exact MultiplyWords.initialize_field _ _ separate.data .y
    · exact finalPC
    · intro field outside
      rw [finalData]
      exact MultiplyLoop.multiply_frame _ _ _ _ _ wordTrace field outside

end SmcTuring.Appendix.MultiplyExecution
