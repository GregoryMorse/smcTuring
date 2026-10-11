module
public import SmcTuring.Appendix.DivisionExecution

public section
namespace SmcTuring.Appendix.DivisionObservations
open DivisionControl DivisionBlocks DivisionExecution
attribute [local irreducible] DivisionControl.run DivisionWords.run DivisionExecution.loop

@[expose] def loopWritten (layout : Layout) : List DivisionWords.Slot :=
  written layout .guard ++ written layout .body ++ written layout .finish

theorem loop_frame (fuel : Nat) (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) (field : Nat)
    (outside : ∀ slot ∈ loopWritten layout, field ≠ layout.fields slot) :
    final.data.memory field = state.data.memory field := by
  have guardOut : ∀ slot ∈ written layout .guard, field ≠ layout.fields slot :=
    fun slot member => outside slot (by simp only [loopWritten, List.mem_append]; exact Or.inl (Or.inl member))
  have bodyOut : ∀ slot ∈ written layout .body, field ≠ layout.fields slot :=
    fun slot member => outside slot (by simp only [loopWritten, List.mem_append]; exact Or.inl (Or.inr member))
  have finishOut : ∀ slot ∈ written layout .finish, field ≠ layout.fields slot :=
    fun slot member => outside slot (by simp only [loopWritten, List.mem_append]; exact Or.inr member)
  have exited (current : State) (currentReady : StackReady layout.pointer layout.address current) :
      (run (program layout .finish) (run (program layout .guard) current)).data.memory field =
        current.data.memory field := by
    rw [program_frame_written layout .finish _ separate
      (program_ready layout .guard current separate currentReady) field finishOut,
      program_frame_written layout .guard current separate currentReady field guardOut]
  induction fuel generalizing state commands final with
  | zero =>
      rw [loop] at trace
      split at trace
      · cases trace; exact exited state ready
      · cases trace
  | succ fuel ih =>
      rw [loop] at trace
      split at trace
      · cases trace; exact exited state ready
      · split at trace
        · obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
          have pieces := Prod.mk.inj equality
          have testedReady := program_ready layout .guard state separate ready
          have afterReady := program_ready layout .body _ separate testedReady
          rw [← pieces.2, ih _ afterReady result.1 result.2 recursive,
            program_frame_written layout .body _ separate testedReady field bodyOut,
            program_frame_written layout .guard state separate ready field guardOut]
        · cases trace

theorem loop_pure (fuel : Nat) (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) (codeField : Nat → Prop)
    (owned : ∀ block slot, slot ∈ written layout block → codeField (layout.fields slot))
    (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    PureRun codeField commands state := by
  have exited (current : State) (currentReady : StackReady layout.pointer layout.address current) :
      PureRun codeField (program layout .guard ++ program layout .finish) current :=
    (pure_append _ _ _ _).mpr
      ⟨program_pure layout .guard current separate currentReady codeField (owned .guard) pointerOwned addressOwned,
       program_pure layout .finish _ separate (program_ready layout .guard current separate currentReady)
         codeField (owned .finish) pointerOwned addressOwned⟩
  induction fuel generalizing state commands final with
  | zero =>
      rw [loop] at trace
      split at trace
      · cases trace; exact exited state ready
      · cases trace
  | succ fuel ih =>
      rw [loop] at trace
      split at trace
      · cases trace; exact exited state ready
      · split at trace
        · obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
          have pieces := Prod.mk.inj equality
          have testedReady := program_ready layout .guard state separate ready
          have afterReady := program_ready layout .body _ separate testedReady
          rw [← pieces.1, pure_append, pure_append, run_append]
          exact ⟨⟨program_pure layout .guard state separate ready codeField (owned .guard) pointerOwned addressOwned,
            program_pure layout .body _ separate testedReady codeField (owned .body) pointerOwned addressOwned⟩,
            ih _ afterReady result.1 result.2 recursive⟩
        · cases trace

theorem loop_preserves (fuel : Nat) (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : loop fuel layout state = some (commands, final)) (slot : DivisionWords.Slot)
    (outside : slot ∉ loopWritten layout) :
    final.data.memory (layout.fields slot) = state.data.memory (layout.fields slot) := by
  apply loop_frame fuel layout state separate ready commands final trace
  intro other member
  apply separate.data.ne
  intro equality
  apply outside
  rw [equality]
  exact member

theorem source_slots_stable (layout : Layout) :
    DivisionWords.Slot.x ∉ loopWritten layout ∧
    DivisionWords.Slot.y ∉ loopWritten layout ∧
    DivisionWords.Slot.resultSign ∉ loopWritten layout := by
  cases mod : layout.mod <;> cases signed : layout.signed <;>
    simp [loopWritten, written, DivisionGuard.written, DivisionBody.written,
      DivisionStages.finishWritten, mod, signed]

theorem divide_pure (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : divide layout state = some (commands, final)) (codeField : Nat → Prop)
    (owned : ∀ block slot, slot ∈ written layout block → codeField (layout.fields slot))
    (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    PureRun codeField commands state := by
  rw [divide] at trace
  obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
  have pieces := Prod.mk.inj equality
  rw [← pieces.1, pure_append]
  exact ⟨program_pure layout .initial state separate ready codeField (owned .initial) pointerOwned addressOwned,
    loop_pure 32 layout _ separate (program_ready layout .initial state separate ready)
      result.1 result.2 recursive codeField owned pointerOwned addressOwned⟩

theorem divide_frame (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : divide layout state = some (commands, final)) (field : Nat)
    (outside : ∀ slot, field ≠ layout.fields slot) :
    final.data.memory field = state.data.memory field := by
  rw [divide] at trace
  obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
  have pieces := Prod.mk.inj equality
  rw [← pieces.2, loop_frame 32 layout _ separate (program_ready layout .initial state separate ready)
    result.1 result.2 recursive field (fun slot _ => outside slot),
    program_frame layout .initial state separate ready field outside]

theorem divide_inputs (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : divide layout state = some (commands, final)) :
    final.data.memory (layout.fields .x) = state.data.memory (layout.fields .x) ∧
    final.data.memory (layout.fields .y) = state.data.memory (layout.fields .y) := by
  rw [divide] at trace
  obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
  have pieces := Prod.mk.inj equality
  rw [← pieces.2]
  have observed (slot : DivisionWords.Slot) (outside : slot ∉ loopWritten layout) :
      result.2.data.memory (layout.fields slot) =
        DivisionStages.initialValue layout.fields layout.mod layout.signed state.data slot := by
    rw [loop_preserves 32 layout _ separate (program_ready layout .initial state separate ready)
      result.1 result.2 recursive slot outside,
      program_effect layout .initial state separate ready (by decide)]
    exact DivisionStages.initial_field _ _ _ _ separate.data slot
  exact ⟨observed .x (source_slots_stable layout).1, observed .y (source_slots_stable layout).2.1⟩

theorem divide_sign (layout : Layout) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state)
    (commands : List Instruction) (final : State)
    (trace : divide layout state = some (commands, final)) (signed : layout.signed = true) :
    final.data.memory (layout.fields .resultSign) =
      BranchAlgebra.mask (DivisionSignedAlgebra.negative layout.mod
        (state.data.memory (layout.fields .x)) (state.data.memory (layout.fields .y))) := by
  rw [divide] at trace
  obtain ⟨result, recursive, equality⟩ := Option.map_eq_some_iff.mp trace
  have pieces := Prod.mk.inj equality
  rw [← pieces.2, loop_preserves 32 layout _ separate (program_ready layout .initial state separate ready)
      result.1 result.2 recursive .resultSign (source_slots_stable layout).2.2,
    program_effect layout .initial state separate ready (by decide)]
  change (DivisionWords.run (DivisionWords.initializeData layout.fields layout.mod layout.signed) state.data).memory
    (layout.fields .resultSign) = _
  rw [DivisionStages.initial_field _ _ _ _ separate.data .resultSign]
  simp only [DivisionStages.initialValue, signed, ite_true, DivisionPrefixes.signValue]

end SmcTuring.Appendix.DivisionObservations
