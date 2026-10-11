module
public import SmcTuring.Appendix.MultiplyWords

public section
namespace SmcTuring.Appendix.MultiplyLoop
open MultiplyWords MultiplyAlgebra
abbrev Word := Machine32.Word
abbrev State := Machine32.State

/-- The data/control projection dispatches on the actual patched displacement.
CALL/SP continuation and byte fetch remain separate composition obligations. -/
@[expose] def loop : Nat -> Fields -> Word -> State -> Option (List Instruction × State)
  | fuel, fields, delta, state =>
    let tested := run (guard fields delta) state
    if tested.memory (fields .displacement) = 0 then
      match fuel with
      | 0 => none
      | remaining + 1 =>
        (loop remaining fields delta (run (body fields) tested)).map
          (fun result => (guard fields delta ++ body fields ++ result.1, result.2))
    else some (guard fields delta ++ finish fields, run (finish fields) tested)

@[expose] def invariant (fields : Fields) (state : State) : Word :=
  state.memory (fields .total) + state.memory (fields .factor) * state.memory (fields .multiplier)

structure Post (fields : Fields) (initial final : State) : Prop where
  product : final.memory (fields .result) = invariant fields initial
  multiplier : final.memory (fields .multiplier) = 0
  displacement : final.memory (fields .displacement) = 0
  accumulator : final.accumulator = initial.accumulator
  carry : final.carry = false
  inputX : final.memory (fields .x) = initial.memory (fields .x)
  inputY : final.memory (fields .y) = initial.memory (fields .y)

theorem guard_invariant (fields : Fields) (delta : Word) (state : State) (separate : Separate fields) :
    invariant fields (run (guard fields delta) state) = invariant fields state := by
  simp [invariant, guard_field fields delta state separate, guardValue]

theorem body_invariant (fields : Fields) (state : State) (separate : Separate fields) :
    invariant fields (run (body fields) state) = invariant fields state := by
  simp only [invariant, body_field fields state separate, bodyValue]
  exact step_invariant _ _ _

theorem exit_post (fields : Fields) (delta : Word) (state : State) (separate : Separate fields)
    (zero : state.memory (fields .multiplier) = 0) :
    Post fields state (run (finish fields) (run (guard fields delta) state)) := by
  change state.memory (fields .multiplier) = BitVec.ofNat 32 0 at zero
  constructor
  · simp [finish_field fields _ separate, guard_field fields delta state separate, guardValue, invariant, zero]
  · simp [finish_field fields _ separate, guard_field fields delta state separate, guardValue, zero]
  · simp [finish_field fields _ separate]
  · rw [(finish_registers fields _).1, guard_accumulator]
  · rw [(finish_registers fields _).2, guard_carry]
  · simp [finish_field fields _ separate, guard_field fields delta state separate, guardValue]
  · simp [finish_field fields _ separate, guard_field fields delta state separate, guardValue]

theorem post_step (fields : Fields) (delta : Word) (state final : State) (separate : Separate fields)
    (post : Post fields (run (body fields) (run (guard fields delta) state)) final) : Post fields state final := by
  constructor
  · rw [post.product, body_invariant fields _ separate, guard_invariant fields delta state separate]
  · exact post.multiplier
  · exact post.displacement
  · rw [post.accumulator, body_accumulator fields _ separate, guard_accumulator]
  · exact post.carry
  · simpa [body_field fields _ separate, bodyValue, guard_field fields delta state separate, guardValue] using post.inputX
  · simpa [body_field fields _ separate, bodyValue, guard_field fields delta state separate, guardValue] using post.inputY

theorem loop_correct (fuel : Nat) (fields : Fields) (delta : Word) (state : State)
    (separate : Separate fields) (nonzero : delta ≠ 0)
    (initial : state.memory (fields .displacement) = 0)
    (bound : (state.memory (fields .multiplier)).toNat < 2 ^ fuel) :
    ∃ program final, loop fuel fields delta state = some (program, final) ∧ Post fields state final := by
  change delta ≠ BitVec.ofNat 32 0 at nonzero
  induction fuel generalizing state with
  | zero =>
      have zero : state.memory (fields .multiplier) = BitVec.ofNat 32 0 := by
        apply BitVec.eq_of_toNat_eq
        have small : (state.memory (fields .multiplier)).toNat < 1 := by simpa using bound
        change (state.memory (fields .multiplier)).toNat = 0
        omega
      refine ⟨guard fields delta ++ finish fields, _, ?_, exit_post fields delta state separate zero⟩
      simp [loop, guard_displacement fields delta state separate initial, zero, nonzero]
  | succ fuel ih =>
      by_cases zero : state.memory (fields .multiplier) = BitVec.ofNat 32 0
      · refine ⟨guard fields delta ++ finish fields, _, ?_, exit_post fields delta state separate zero⟩
        simp [loop, guard_displacement fields delta state separate initial, zero, nonzero]
      · let after := run (body fields) (run (guard fields delta) state)
        have shifted : after.memory (fields .multiplier) = state.memory (fields .multiplier) >>> 1 := by
          simp [after, body_field fields _ separate, bodyValue, guard_field fields delta state separate, guardValue]
        have reset : after.memory (fields .displacement) = 0 := by
          simp [after, body_field fields _ separate, bodyValue, guard_field fields delta state separate, guardValue, initial, zero]
        have smaller : (after.memory (fields .multiplier)).toNat < 2 ^ fuel := by
          rw [shifted]
          exact shifted_bound _ _ bound
        obtain ⟨program, final, trace, post⟩ := ih after reset smaller
        refine ⟨guard fields delta ++ body fields ++ program, final, ?_, post_step fields delta state final separate post⟩
        simp [loop, guard_displacement fields delta state separate initial, zero, after, trace]

theorem loop_run (fuel : Nat) (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : loop fuel fields delta state = some (program, final)) :
    run program state = final := by
  induction fuel generalizing state program final with
  | zero =>
      simp only [loop] at trace
      split at trace
      · contradiction
      · cases trace; exact run_append _ _ _
  | succ fuel ih =>
      simp only [loop] at trace
      split at trace
      · cases h : loop fuel fields delta (run (body fields) (run (guard fields delta) state)) with
        | none => simp [h] at trace
        | some result =>
          simp only [h, Option.map_some, Option.some.injEq] at trace
          cases trace
          rw [run_append, run_append]
          exact ih _ _ _ h
      · cases trace; exact run_append _ _ _

theorem pure_append (codeField : Nat -> Prop) (first second : List Instruction) (state : State) :
    PureRun codeField (first ++ second) state ↔
      PureRun codeField first state ∧ PureRun codeField second (run first state) := by
  induction first generalizing state with
  | nil => simp [PureRun, run]
  | cons instruction rest ih => simp [PureRun, run, ih, and_assoc]

theorem loop_pure (fuel : Nat) (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : loop fuel fields delta state = some (program, final))
    (codeField : Nat -> Prop) (owned : ∀ slot, codeField (fields slot)) : PureRun codeField program state := by
  induction fuel generalizing state program final with
  | zero =>
      simp only [loop] at trace
      split at trace
      · contradiction
      · cases trace
        exact (pure_append _ _ _ _).mpr ⟨guard_pure _ _ _ _ owned, finish_pure _ _ _ owned⟩
  | succ fuel ih =>
      simp only [loop] at trace
      split at trace
      · cases h : loop fuel fields delta (run (body fields) (run (guard fields delta) state)) with
        | none => simp [h] at trace
        | some result =>
          simp only [h, Option.map_some, Option.some.injEq] at trace
          cases trace
          rw [pure_append, pure_append, run_append]
          exact ⟨⟨guard_pure _ _ _ _ owned, body_pure _ _ _ owned⟩, ih _ _ _ h⟩
      · cases trace
        exact (pure_append _ _ _ _).mpr ⟨guard_pure _ _ _ _ owned, finish_pure _ _ _ owned⟩

@[expose] def multiply (fields : Fields) (delta : Word) (state : State) : Option (List Instruction × State) :=
  (loop 32 fields delta (run (initialProgram fields) state)).map
    (fun result => (initialProgram fields ++ result.1, result.2))

theorem full_product (fields : Fields) (delta : Word) (state : State)
    (separate : Separate fields) (nonzero : delta ≠ 0)
    (initial : state.memory (fields .displacement) = 0) :
    ∃ program final, multiply fields delta state = some (program, final) ∧
      run program state = final ∧ final.memory (fields .result) = state.memory (fields .x) * state.memory (fields .y) ∧
      final.accumulator = state.accumulator ∧ final.carry = false ∧ final.memory (fields .displacement) = 0 ∧
      final.memory (fields .x) = state.memory (fields .x) ∧ final.memory (fields .y) = state.memory (fields .y) := by
  have reset : (run (initialProgram fields) state).memory (fields .displacement) = 0 := by
    simpa [initialize_field fields state separate] using initial
  obtain ⟨program, final, trace, post⟩ := loop_correct 32 fields delta (run (initialProgram fields) state) separate nonzero reset
    ((run (initialProgram fields) state).memory (fields .multiplier)).isLt
  refine ⟨initialProgram fields ++ program, final, ?_, ?_, ?_, ?_, post.carry, post.displacement, ?_, ?_⟩
  · simp [multiply, trace]
  · rw [run_append]; exact loop_run _ _ _ _ _ _ trace
  · simpa [invariant, initialize_field fields state separate] using post.product
  · simpa [initialize_accumulator fields state separate] using post.accumulator
  · simpa [initialize_field fields state separate] using post.inputX
  · simpa [initialize_field fields state separate] using post.inputY

theorem multiply_run (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : multiply fields delta state = some (program, final)) :
    run program state = final := by
  simp only [multiply] at trace
  cases h : loop 32 fields delta (run (initialProgram fields) state) with
  | none => simp [h] at trace
  | some result =>
      simp only [h, Option.map_some, Option.some.injEq] at trace
      cases trace
      rw [run_append]
      exact loop_run _ _ _ _ _ _ h

theorem multiply_pure (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : multiply fields delta state = some (program, final))
    (codeField : Nat -> Prop) (owned : ∀ slot, codeField (fields slot)) : PureRun codeField program state := by
  simp only [multiply] at trace
  cases h : loop 32 fields delta (run (initialProgram fields) state) with
  | none => simp [h] at trace
  | some result =>
      simp only [h, Option.map_some, Option.some.injEq] at trace
      cases trace
      exact (pure_append _ _ _ _).mpr ⟨initialize_pure _ _ _ owned, loop_pure _ _ _ _ _ _ h _ owned⟩

theorem pure_destinations (codeField : Nat -> Prop) (program : List Instruction) (state : State)
    (pure : PureRun codeField program state) : ∀ instruction ∈ program, codeField (destination instruction) := by
  induction program generalizing state with
  | nil => simp
  | cons instruction rest ih =>
      intro other member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact pure.1
      · exact ih _ pure.2 _ member

theorem multiply_frame (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : multiply fields delta state = some (program, final))
    (field : Nat) (outside : ∀ slot, field ≠ fields slot) : final.memory field = state.memory field := by
  rw [← multiply_run _ _ _ _ _ trace]
  apply run_frame
  exact pure_destinations (fun address => field ≠ address) program state
    (multiply_pure _ _ _ _ _ trace _ outside)

theorem loop_length (fuel : Nat) (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : loop fuel fields delta state = some (program, final)) :
    program.length ≤ 25 * fuel + 10 := by
  induction fuel generalizing state program final with
  | zero =>
      simp only [loop] at trace
      split at trace
      · contradiction
      · cases trace; simp [MultiplyWords.guard, finish]
  | succ fuel ih =>
      simp only [loop] at trace
      split at trace
      · cases h : loop fuel fields delta (run (body fields) (run (guard fields delta) state)) with
        | none => simp [h] at trace
        | some result =>
          simp only [h, Option.map_some, Option.some.injEq] at trace
          cases trace
          have bound := ih _ _ _ h
          simp only [List.length_append]
          have sizes := block_lengths fields delta
          rw [sizes.2.1, sizes.2.2.1]
          omega
      · cases trace; simp [MultiplyWords.guard, finish]

theorem multiply_length (fields : Fields) (delta : Word) (state : State)
    (program : List Instruction) (final : State) (trace : multiply fields delta state = some (program, final)) :
    program.length ≤ 817 := by
  simp only [multiply] at trace
  cases h : loop 32 fields delta (run (initialProgram fields) state) with
  | none => simp [h] at trace
  | some result =>
      simp only [h, Option.map_some, Option.some.injEq] at trace
      cases trace
      have bound := loop_length _ _ _ _ _ _ h
      rw [List.length_append, (block_lengths fields delta).1]
      omega

end SmcTuring.Appendix.MultiplyLoop
