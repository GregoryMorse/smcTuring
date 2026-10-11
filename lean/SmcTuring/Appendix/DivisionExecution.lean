module
public import SmcTuring.Appendix.DivisionBlocks

public section
namespace SmcTuring.Appendix.DivisionExecution
open DivisionControl DivisionBlocks

-- Keep symbolic machine states folded while applying their checked execution laws.
attribute [local irreducible] DivisionControl.run DivisionWords.run

/-- Dispatch is the actual PC after the executed guard and CALL continuation.
No body count, selected branch, or later trace is supplied by the evaluator. -/
@[expose] def loop : Nat → Layout → State → Option (List Instruction × State)
  | 0, layout, state =>
      let tested := run (program layout .guard) state
      if tested.pc = exitPC layout then
        some (program layout .guard ++ program layout .finish, run (program layout .finish) tested)
      else none
  | remaining + 1, layout, state =>
      let tested := run (program layout .guard) state
      if tested.pc = exitPC layout then
        some (program layout .guard ++ program layout .finish, run (program layout .finish) tested)
      else if tested.pc = bodyPC layout then
        (loop remaining layout (run (program layout .body) tested)).map
          (fun result => (program layout .guard ++ program layout .body ++ result.1, result.2))
      else none

attribute [local irreducible] loop

@[expose] def divide (layout : Layout) (state : State) : Option (List Instruction × State) :=
  (loop 32 layout (run (program layout .initial) state)).map
    (fun result => (program layout .initial ++ result.1, result.2))

structure Post (layout : Layout) (dividend divisor : Word) (initial final : State) : Prop where
  invariant : DivisionIteration.Invariant layout.fields dividend divisor 32 final.data
  stack : final.stack = initial.stack
  pc : final.pc = endPC layout
  accumulator : final.data.accumulator = initial.data.accumulator
  ready : StackReady layout.pointer layout.address final
  output : final.data.memory (layout.fields .result) =
    DivisionStages.finishValue layout.fields layout.mod layout.signed final.data .result
  carry : final.data.carry =
    if layout.signed then decide
      ((DivisionStages.selectedResult layout.fields layout.mod final.data).toNat <
        ((DivisionStages.selectedResult layout.fields layout.mod final.data <<< 1) &&&
          final.data.memory (layout.fields .resultSign)).toNat)
    else false
  displacement : final.data.memory (layout.fields .displacement) = 0

theorem finish_invariant (layout : Layout) (dividend divisor : Word) (state : State)
    (separate : Separate layout) (entry : state.pc = exitPC layout)
    (current : DivisionIteration.Invariant layout.fields dividend divisor 32 state.data) :
    DivisionIteration.Invariant layout.fields dividend divisor 32
      (run (program layout .finish) state).data := by
  rw [finish_effect layout state entry]
  rcases current with ⟨first, second, low, high, counter⟩
  simp only [DivisionIteration.Invariant, words,
    DivisionStages.finish_field _ _ _ _ separate.data, DivisionStages.finishValue]
  exact ⟨first, second, low, high, counter⟩

theorem finish_observations (layout : Layout) (state : State) (separate : Separate layout)
    (entry : state.pc = exitPC layout) (clear : state.data.carry = false) :
    let final := run (program layout .finish) state
    final.data.memory (layout.fields .result) =
      DivisionStages.finishValue layout.fields layout.mod layout.signed final.data .result ∧
    final.data.carry =
      (if layout.signed then decide
        ((DivisionStages.selectedResult layout.fields layout.mod final.data).toNat <
          ((DivisionStages.selectedResult layout.fields layout.mod final.data <<< 1) &&&
            final.data.memory (layout.fields .resultSign)).toNat)
       else false) ∧
    final.data.memory (layout.fields .displacement) = 0 := by
  rw [finish_effect layout state entry]
  have projected := DivisionStages.finish_field layout.fields layout.mod layout.signed state.data separate.data
  have carried := DivisionStages.finish_carry layout.fields layout.mod layout.signed state.data separate.data
  cases signed : layout.signed <;> cases mod : layout.mod
  all_goals simp only [signed, mod] at projected carried
  all_goals simp only [words, signed, mod, projected, carried,
    DivisionStages.finishValue, DivisionStages.selectedResult,
    Bool.false_eq_true, ite_false, ite_true, clear]
  all_goals trivial

theorem exit_finishes (fuel : Nat) (layout : Layout) (dividend divisor : Word) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (entry : state.pc = guardPC layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (current : DivisionIteration.Invariant layout.fields dividend divisor 32 state.data) :
    ∃ commands final, loop fuel layout state = some (commands, final) ∧
      Post layout dividend divisor state final := by
  have zero : state.data.memory (layout.fields .counter) = 0 := by
    simpa using current.2.2.2.2
  change state.data.memory (layout.fields .counter) = BitVec.ofNat 32 0 at zero
  let tested := run (program layout .guard) state
  have testedEffect : tested =
      {data := DivisionWords.run (words layout .guard) state.data, stack := state.stack, pc := exitPC layout} := by
    simpa [tested, zero] using guard_effect layout state separate ready entry initial
  have testedPC : tested.pc = exitPC layout := by rw [testedEffect]
  have testedReady := program_ready layout .guard state separate ready
  have testedInvariant : DivisionIteration.Invariant layout.fields dividend divisor 32 tested.data := by
    rw [testedEffect]
    exact DivisionGuard.invariant _ _ _ _ _ _ separate.data current
  have testedCarry : tested.data.carry = false := by
    rw [testedEffect]
    exact DivisionGuard.carry _ _ _
  have observed := finish_observations layout tested separate testedPC testedCarry
  refine ⟨program layout .guard ++ program layout .finish, run (program layout .finish) tested, ?_, ?_⟩
  · cases fuel <;> rw [loop, testedPC, ite_eq_left rfl]
  · constructor
    · exact finish_invariant layout dividend divisor tested separate testedPC testedInvariant
    · exact (program_stack layout .finish tested separate testedReady).trans
        (program_stack layout .guard state separate ready)
    · rw [finish_effect layout tested testedPC]
    · exact (program_accumulator layout .finish tested separate testedReady).trans
        (program_accumulator layout .guard state separate ready)
    · exact program_ready layout .finish tested separate testedReady
    · exact observed.1
    · exact observed.2.1
    · exact observed.2.2

theorem loop_finishes (fuel : Nat) (layout : Layout) (dividend divisor : Word) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (entry : state.pc = guardPC layout)
    (back : state.data.memory layout.backDisplacement = backDelta layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (k : Nat) (range : k ≤ 32) (bound : 32 - k ≤ fuel) (nonzero : 0 < divisor.toNat)
    (current : DivisionIteration.Invariant layout.fields dividend divisor k state.data) :
    ∃ commands final, loop fuel layout state = some (commands, final) ∧
      Post layout dividend divisor state final := by
  induction fuel generalizing state k with
  | zero =>
      have last : k = 32 := by omega
      subst k
      exact exit_finishes 0 layout dividend divisor state separate ready entry initial current
  | succ fuel ih =>
      by_cases last : k = 32
      · subst k
        exact exit_finishes _ layout dividend divisor state separate ready entry initial current
      · have before : k < 32 := by omega
        have count : state.data.memory (layout.fields .counter) ≠ 0 := by
          intro zero
          have words := current.2.2.2.2
          rw [zero] at words
          have natural := congrArg BitVec.toNat words
          have small : 32 - k < 4294967296 := by omega
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at natural
          norm_num at natural
          omega
        change state.data.memory (layout.fields .counter) ≠ BitVec.ofNat 32 0 at count
        let tested := run (program layout .guard) state
        let after := run (program layout .body) tested
        have testedEffect : tested =
            {data := DivisionWords.run (words layout .guard) state.data, stack := state.stack, pc := bodyPC layout} := by
          simpa [tested, count] using guard_effect layout state separate ready entry initial
        have testedPC : tested.pc = bodyPC layout := by rw [testedEffect]
        have testedReady := program_ready layout .guard state separate ready
        have testedBack : tested.data.memory layout.backDisplacement = backDelta layout := by
          rw [program_frame layout .guard state separate ready layout.backDisplacement (separate.outside _ (by simp))]
          exact back
        have testedInvariant : DivisionIteration.Invariant layout.fields dividend divisor k tested.data := by
          rw [testedEffect]
          exact DivisionGuard.invariant _ _ _ _ _ _ separate.data current
        have afterEffect : after =
            {data := MultiplyControl.clearCarry (DivisionWords.run (words layout .body) tested.data),
              stack := tested.stack, pc := guardPC layout} :=
          body_effect layout tested separate testedReady testedPC testedBack
        have afterPC : after.pc = guardPC layout := by rw [afterEffect]
        have afterReady := program_ready layout .body tested separate testedReady
        have afterBack : after.data.memory layout.backDisplacement = backDelta layout := by
          rw [program_frame layout .body tested separate testedReady layout.backDisplacement (separate.outside _ (by simp))]
          exact testedBack
        have afterInitial : after.data.memory (layout.fields .displacement) = 0 := by
          rw [afterEffect]
          change (DivisionWords.run (DivisionWords.body layout.fields) tested.data).memory
            (layout.fields .displacement) = 0
          rw [DivisionBody.body_field _ _ separate.data .displacement]
          change tested.data.memory (layout.fields .displacement) = 0
          rw [testedEffect]
          simp [words, DivisionGuard.displacement _ _ _ separate.data initial, count]
        have afterInvariant : DivisionIteration.Invariant layout.fields dividend divisor (k + 1) after.data := by
          rw [afterEffect]
          simpa only [words, MultiplyControl.clearCarry, DivisionIteration.Invariant] using
            DivisionIteration.advance layout.fields dividend divisor tested.data k separate.data nonzero before testedInvariant
        obtain ⟨commands, final, recursive, post⟩ := ih after afterReady afterPC afterBack afterInitial
          (k + 1) (by omega) (by omega) afterInvariant
        refine ⟨program layout .guard ++ program layout .body ++ commands, final, ?_, ?_⟩
        · rw [loop, show (run (program layout .guard) state).pc = bodyPC layout from testedPC,
            ite_eq_right (Ne.symm (continuations_distinct layout)), ite_eq_left rfl]
          change (loop fuel layout after).map _ = _
          rw [recursive]
          rfl
        · constructor
          · exact post.invariant
          · exact post.stack.trans ((program_stack layout .body tested separate testedReady).trans
              (program_stack layout .guard state separate ready))
          · exact post.pc
          · exact post.accumulator.trans ((program_accumulator layout .body tested separate testedReady).trans
              (program_accumulator layout .guard state separate ready))
          · exact post.ready
          · exact post.output
          · exact post.carry
          · exact post.displacement

theorem loop_run (fuel : Nat) (layout : Layout) (state : State) (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) : run commands state = final := by
  induction fuel generalizing state commands final with
  | zero =>
      rw [loop] at trace
      split at trace
      · cases trace; exact run_append _ _ _
      · cases trace
  | succ fuel ih =>
      rw [loop] at trace
      split at trace
      · cases trace; exact run_append _ _ _
      · split at trace
        · obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
          have pieces := Prod.mk.inj equality
          rw [← pieces.1, ← pieces.2, run_append, run_append]
          exact ih _ _ _ recursive
        · cases trace


/-- One original initializer and its bootstrap CALL establish the complete
loop invariant. Readiness and all relative operands below are initial data,
not an assumed later trace or a supplied division result. -/
theorem divide_finishes (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state)
    (entry : state.pc = layout.origin)
    (direct : state.data.memory layout.entryDisplacement = 0)
    (back : state.data.memory layout.backDisplacement = backDelta layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (nonzero : state.data.memory (layout.fields .y) ≠ 0) :
    ∃ commands final, divide layout state = some (commands, final) ∧
      run commands state = final ∧
      Post layout
        (DivisionDataCorrect.argument layout.signed (state.data.memory (layout.fields .x)))
        (DivisionDataCorrect.argument layout.signed (state.data.memory (layout.fields .y))) state final := by
  let dividend := DivisionDataCorrect.argument layout.signed (state.data.memory (layout.fields .x))
  let divisor := DivisionDataCorrect.argument layout.signed (state.data.memory (layout.fields .y))
  let started := run (program layout .initial) state
  have startEffect : started =
      {data := MultiplyControl.clearCarry (DivisionWords.run (words layout .initial) state.data),
        stack := state.stack, pc := guardPC layout} :=
    entry_effect layout state separate ready entry direct
  have startPC : started.pc = guardPC layout := by rw [startEffect]
  have startReady := program_ready layout .initial state separate ready
  have startBack : started.data.memory layout.backDisplacement = backDelta layout := by
    rw [program_frame layout .initial state separate ready layout.backDisplacement (separate.outside _ (by simp))]
    exact back
  have startInitial : started.data.memory (layout.fields .displacement) = 0 := by
    rw [startEffect]
    change (DivisionWords.run (DivisionWords.initializeData layout.fields layout.mod layout.signed) state.data).memory
      (layout.fields .displacement) = 0
    rw [DivisionStages.initial_field _ _ _ _ separate.data .displacement]
    exact initial
  have startInvariant : DivisionIteration.Invariant layout.fields dividend divisor 0 started.data := by
    have first := DivisionIteration.initial_invariant layout.fields dividend divisor
      (DivisionWords.run (DivisionWords.initializeData layout.fields layout.mod layout.signed) state.data)
      (DivisionDataCorrect.initialized layout.fields layout.mod layout.signed state.data separate.data)
    rw [startEffect]
    simpa only [words, MultiplyControl.clearCarry, DivisionIteration.Invariant] using first
  have positive : 0 < divisor.toNat := by
    have nz := DivisionDataCorrect.divisor_nonzero layout.signed (state.data.memory (layout.fields .y)) nonzero
    have natNZ : divisor.toNat ≠ 0 := fun zero => nz (BitVec.eq_of_toNat_eq zero)
    omega
  obtain ⟨commands, final, trace, post⟩ := loop_finishes 32 layout dividend divisor started separate startReady
    startPC startBack startInitial 0 (by decide) (by decide) positive startInvariant
  refine ⟨program layout .initial ++ commands, final, ?_, ?_, ?_⟩
  · simp only [divide]
    change (loop 32 layout started).map _ = _
    rw [trace]
    rfl
  · rw [run_append]
    exact loop_run 32 layout started commands final trace
  · constructor
    · exact post.invariant
    · exact post.stack.trans (program_stack layout .initial state separate ready)
    · exact post.pc
    · exact post.accumulator.trans (program_accumulator layout .initial state separate ready)
    · exact post.ready
    · exact post.output
    · exact post.carry
    · exact post.displacement

end SmcTuring.Appendix.DivisionExecution

