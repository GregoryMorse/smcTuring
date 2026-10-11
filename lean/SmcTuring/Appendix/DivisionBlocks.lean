module
public import SmcTuring.Appendix.DivisionGuard
public import SmcTuring.Appendix.DivisionControl

public section
namespace SmcTuring.Appendix.DivisionBlocks
open DivisionControl

structure Layout where
  origin : Word
  fields : DivisionWords.Fields
  mod : Bool
  signed : Bool
  pointer : Nat
  address : Nat
  entryDisplacement : Nat
  backDisplacement : Nat

@[expose] def initialSpan (layout : Layout) : Nat :=
  if layout.signed then (if layout.mod then 280 else 318) else 69
@[expose] def finishSpan (layout : Layout) : Nat := if layout.signed then 73 else 30
@[expose] def guardContinuation (layout : Layout) : Word := layout.origin + BitVec.ofNat 32 (initialSpan layout) + 11
@[expose] def guardPC (layout : Layout) : Word := guardContinuation layout + 30
@[expose] def bodyContinuation (layout : Layout) : Word := guardPC layout + 65 + 11
@[expose] def bodyPC (layout : Layout) : Word := bodyContinuation layout + 30
@[expose] def exitContinuation (layout : Layout) : Word := bodyPC layout + 177 + 11
@[expose] def exitPC (layout : Layout) : Word := exitContinuation layout + 30
@[expose] def endPC (layout : Layout) : Word := exitPC layout + BitVec.ofNat 32 (finishSpan layout)
@[expose] def delta (layout : Layout) : Word := exitContinuation layout - bodyContinuation layout
@[expose] def backDelta (layout : Layout) : Word := guardContinuation layout - exitContinuation layout

structure Separate (layout : Layout) : Prop where
  data : DivisionWords.Separate layout.fields
  outside : ∀ field ∈ [layout.pointer, layout.address, layout.entryDisplacement, layout.backDisplacement],
    ∀ slot, field ≠ layout.fields slot
  address : layout.address ≠ layout.pointer
  entry : layout.entryDisplacement ≠ layout.pointer
  back : layout.backDisplacement ≠ layout.pointer

inductive Block where
  | initial | guard | body | finish
  deriving DecidableEq, Repr

@[expose] def words (layout : Layout) : Block → List DivisionWords.Instruction
  | .initial => DivisionWords.initializeData layout.fields layout.mod layout.signed
  | .guard => DivisionGuard.program layout.fields (delta layout)
  | .body => DivisionWords.body layout.fields
  | .finish => DivisionWords.finishData layout.fields layout.mod layout.signed
@[expose] def written (layout : Layout) : Block → List DivisionWords.Slot
  | .initial => DivisionStages.initialWritten layout.mod layout.signed
  | .guard => DivisionGuard.written
  | .body => DivisionBody.written
  | .finish => DivisionStages.finishWritten layout.mod layout.signed
@[expose] def callWord (layout : Layout) : Block → Nat
  | .initial => layout.entryDisplacement
  | .guard => layout.fields .displacement
  | .body => layout.backDisplacement
  | .finish => layout.entryDisplacement
@[expose] def program (layout : Layout) (block : Block) : List Instruction :=
  lift (words layout block) ++ if block = .finish then [] else roundTrip layout.pointer layout.address (callWord layout block)

theorem delta_value (layout : Layout) : delta layout = (218 : Word) := by
  unfold delta exitContinuation bodyPC bodyContinuation
  ring

theorem delta_nonzero (layout : Layout) : delta layout ≠ 0 := by rw [delta_value]; decide

theorem continuations_distinct (layout : Layout) : exitPC layout ≠ bodyPC layout := by
  intro same
  have difference : exitPC layout - bodyPC layout = (218 : Word) := by
    unfold exitPC exitContinuation
    ring
  rw [same] at difference
  simp at difference

theorem literal_lengths (layout : Layout) :
    span (words layout .initial) = initialSpan layout ∧
    span (words layout .guard) = 65 ∧
    span (words layout .body) = 177 ∧
    span (words layout .finish) = finishSpan layout := by
  cases signed : layout.signed <;> cases mod : layout.mod <;>
    simp [words, initialSpan, finishSpan, signed, mod, span, dataLength,
      DivisionWords.initializeData, DivisionWords.signPrefix, DivisionWords.sample,
      DivisionWords.normalize, DivisionWords.copy, MultiplyWords.copyProgram,
      DivisionGuard.program, MultiplyWords.guard, DivisionGuard.guardFields, DivisionGuard.binding,
      DivisionWords.body, DivisionWords.finishData, DivisionWords.selected, MultiplyControl.dataLength]

theorem words_pure (layout : Layout) (block : Block) (state : Machine32.State) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ written layout block, codeField (layout.fields slot)) :
    DivisionWords.PureRun codeField (words layout block) state := by
  cases block
  · exact DivisionStages.initial_pure _ _ _ _ _ owned
  · exact DivisionGuard.pure _ _ _ _ owned
  · exact DivisionBody.body_pure _ _ _ owned
  · exact DivisionStages.finish_pure _ _ _ _ _ owned

theorem words_frame (layout : Layout) (block : Block) (state : Machine32.State) (field : Nat)
    (outside : ∀ slot, field ≠ layout.fields slot) :
    (DivisionWords.run (words layout block) state).memory field = state.memory field := by
  cases block
  · exact DivisionStages.initial_frame _ _ _ _ _ (fun slot _ => outside slot)
  · exact DivisionGuard.frame _ _ _ _ (fun slot _ => outside slot)
  · exact DivisionBody.body_frame _ _ _ (fun slot _ => outside slot)
  · exact DivisionStages.finish_frame _ _ _ _ _ (fun slot _ => outside slot)

theorem ready_lift (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) :
    StackReady layout.pointer layout.address (run (lift (words layout block)) state) :=
  DivisionControl.ready_lift _ _ _ _ ready
    (words_frame layout block state.data layout.pointer (separate.outside _ (by simp)))
    (words_frame layout block state.data layout.address (separate.outside _ (by simp)))

theorem call_separate (layout : Layout) (block : Block) (separate : Separate layout) :
    callWord layout block ≠ layout.pointer := by
  cases block
  · exact separate.entry
  · exact Ne.symm (separate.outside _ (by simp) .displacement)
  · exact separate.back
  · exact separate.entry

theorem program_effect (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (active : block ≠ .finish) :
    run (program layout block) state =
      {data := MultiplyControl.clearCarry (DivisionWords.run (words layout block) state.data),
        stack := state.stack, pc := state.pc + BitVec.ofNat 32 (span (words layout block)) + 11 +
          (DivisionWords.run (words layout block) state.data).memory (callWord layout block) + 30} := by
  rw [program, ite_eq_right active, run_append,
    round_trip_effect _ _ _ _ (call_separate layout block separate) separate.address (ready_lift layout block state separate ready),
    lift_effect]
  unfold BranchTail.next
  congr 1
  ring

theorem program_ready (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) :
    StackReady layout.pointer layout.address (run (program layout block) state) := by
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil]
    exact ready_lift layout .finish state separate ready
  · rw [program, ite_eq_right finish, run_append]
    exact round_trip_ready _ _ _ _ (call_separate layout block separate) separate.address (ready_lift layout block state separate ready)

theorem program_frame (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (field : Nat)
    (outside : ∀ slot, field ≠ layout.fields slot) :
    (run (program layout block) state).data.memory field = state.data.memory field := by
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil, lift_effect]
    exact words_frame layout .finish state.data field outside
  · rw [program_effect layout block state separate ready finish]
    exact words_frame layout block state.data field outside

theorem program_pure (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ written layout block, codeField (layout.fields slot))
    (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    PureRun codeField (program layout block) state := by
  rw [program, pure_append]
  refine ⟨lift_pure _ _ _ (words_pure layout block state.data codeField owned), ?_⟩
  split
  · trivial
  · exact round_trip_pure _ _ _ _ (ready_lift layout block state separate ready) codeField pointerOwned addressOwned

theorem clear_guard (layout : Layout) (state : Machine32.State) :
    MultiplyControl.clearCarry (DivisionWords.run (words layout .guard) state) =
      DivisionWords.run (words layout .guard) state := by
  rfl

theorem guard_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = guardPC layout)
    (initial : state.data.memory (layout.fields .displacement) = 0) :
    run (program layout .guard) state =
      {data := DivisionWords.run (words layout .guard) state.data, stack := state.stack,
        pc := if state.data.memory (layout.fields .counter) = 0 then exitPC layout else bodyPC layout} := by
  rw [program_effect layout .guard state separate ready (by decide), clear_guard,
    (literal_lengths layout).2.1]
  congr 1
  simp only [words, callWord]
  rw [DivisionGuard.displacement _ _ _ separate.data initial, entry]
  split
  · change guardPC layout + (65 : Word) + 11 + delta layout + 30 = exitPC layout
    unfold delta exitPC exitContinuation bodyPC bodyContinuation guardPC
    ring
  · change guardPC layout + (65 : Word) + 11 + 0 + 30 = bodyPC layout
    unfold bodyPC bodyContinuation
    ring

theorem body_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = bodyPC layout)
    (back : state.data.memory layout.backDisplacement = backDelta layout) :
    run (program layout .body) state =
      {data := MultiplyControl.clearCarry (DivisionWords.run (words layout .body) state.data),
        stack := state.stack, pc := guardPC layout} := by
  rw [program_effect layout .body state separate ready (by decide), (literal_lengths layout).2.2.1]
  have unchanged := words_frame layout .body state.data layout.backDisplacement (separate.outside _ (by simp))
  congr 1
  simp only [callWord]
  rw [unchanged, back, entry]
  change bodyPC layout + (177 : Word) + 11 + backDelta layout + 30 = guardPC layout
  unfold backDelta exitContinuation bodyPC bodyContinuation guardPC guardContinuation
  ring

theorem entry_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = layout.origin)
    (direct : state.data.memory layout.entryDisplacement = 0) :
    run (program layout .initial) state =
      {data := MultiplyControl.clearCarry (DivisionWords.run (words layout .initial) state.data),
        stack := state.stack, pc := guardPC layout} := by
  rw [program_effect layout .initial state separate ready (by decide), (literal_lengths layout).1]
  have unchanged := words_frame layout .initial state.data layout.entryDisplacement (separate.outside _ (by simp))
  congr 1
  simp only [callWord]
  rw [unchanged, direct, entry]
  unfold guardPC guardContinuation
  ring

theorem finish_effect (layout : Layout) (state : State) (entry : state.pc = exitPC layout) :
    run (program layout .finish) state =
      {data := DivisionWords.run (words layout .finish) state.data, stack := state.stack, pc := endPC layout} := by
  simp only [program, ite_true, List.append_nil, lift_effect]
  rw [(literal_lengths layout).2.2.2, entry]
  rfl


theorem words_frame_written (layout : Layout) (block : Block) (state : Machine32.State) (field : Nat)
    (outside : ∀ slot ∈ written layout block, field ≠ layout.fields slot) :
    (DivisionWords.run (words layout block) state).memory field = state.memory field := by
  cases block
  · exact DivisionStages.initial_frame _ _ _ _ _ outside
  · exact DivisionGuard.frame _ _ _ _ outside
  · exact DivisionBody.body_frame _ _ _ outside
  · exact DivisionStages.finish_frame _ _ _ _ _ outside

theorem program_frame_written (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (field : Nat)
    (outside : ∀ slot ∈ written layout block, field ≠ layout.fields slot) :
    (run (program layout block) state).data.memory field = state.data.memory field := by
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil, lift_effect]
    exact words_frame_written layout .finish state.data field (by simpa [finish] using outside)
  · rw [program_effect layout block state separate ready finish]
    exact words_frame_written layout block state.data field outside

theorem program_accumulator (layout : Layout) (block : Block) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state) :
    (run (program layout block) state).data.accumulator = state.data.accumulator := by
  have dataAX : (DivisionWords.run (words layout block) state.data).accumulator = state.data.accumulator := by
    cases block
    · exact DivisionStages.initial_accumulator _ _ _ _ separate.data
    · exact DivisionGuard.accumulator _ _ _
    · exact DivisionBody.body_accumulator _ _ separate.data
    · exact DivisionStages.finish_accumulator _ _ _ _ separate.data
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil, lift_effect]
    simpa only [finish] using dataAX
  · rw [program_effect layout block state separate ready finish]
    exact dataAX

theorem program_stack (layout : Layout) (block : Block) (state : State)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address state) :
    (run (program layout block) state).stack = state.stack := by
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil, lift_effect]
  · rw [program_effect layout block state separate ready finish]

end SmcTuring.Appendix.DivisionBlocks

