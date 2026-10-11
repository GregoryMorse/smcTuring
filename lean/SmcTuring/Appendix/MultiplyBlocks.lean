module
public import SmcTuring.Appendix.MultiplyControl

public section
namespace SmcTuring.Appendix.MultiplyBlocks
open MultiplyControl

structure Layout where
  origin : Word
  fields : MultiplyWords.Fields
  pointer : Nat
  address : Nat
  entryDisplacement : Nat
  backDisplacement : Nat

@[expose] def guardContinuation (layout : Layout) : Word := layout.origin + 55
@[expose] def guardPC (layout : Layout) : Word := layout.origin + 85
@[expose] def bodyContinuation (layout : Layout) : Word := layout.origin + 161
@[expose] def bodyPC (layout : Layout) : Word := layout.origin + 191
@[expose] def exitContinuation (layout : Layout) : Word := layout.origin + 332
@[expose] def exitPC (layout : Layout) : Word := layout.origin + 362
@[expose] def endPC (layout : Layout) : Word := layout.origin + 382
@[expose] def delta (layout : Layout) : Word := exitContinuation layout - bodyContinuation layout
@[expose] def backDelta (layout : Layout) : Word := guardContinuation layout - exitContinuation layout

structure Separate (layout : Layout) : Prop where
  data : MultiplyWords.Separate layout.fields
  outside : ∀ field ∈ [layout.pointer, layout.address, layout.entryDisplacement, layout.backDisplacement],
    ∀ slot, field ≠ layout.fields slot
  address : layout.address ≠ layout.pointer
  entry : layout.entryDisplacement ≠ layout.pointer
  back : layout.backDisplacement ≠ layout.pointer

inductive Block where
  | initial | guard | body | finish
  deriving DecidableEq
@[expose] def words (layout : Layout) : Block -> List MultiplyWords.Instruction
  | .initial => MultiplyWords.initialProgram layout.fields
  | .guard => MultiplyWords.guard layout.fields (delta layout)
  | .body => MultiplyWords.body layout.fields
  | .finish => MultiplyWords.finish layout.fields
@[expose] def callWord (layout : Layout) : Block -> Nat
  | .initial => layout.entryDisplacement
  | .guard => layout.fields .displacement
  | .body => layout.backDisplacement
  | .finish => layout.entryDisplacement
@[expose] def program (layout : Layout) (block : Block) : List Instruction :=
  lift (words layout block) ++ if block = .finish then [] else roundTrip layout.pointer layout.address (callWord layout block)


theorem delta_value (layout : Layout) : delta layout = BitVec.ofNat 32 171 := by
  change delta layout = (171 : Word)
  unfold delta exitContinuation bodyContinuation
  ring

theorem delta_nonzero (layout : Layout) : delta layout ≠ 0 := by rw [delta_value]; decide

theorem continuations_distinct (layout : Layout) : exitPC layout ≠ bodyPC layout := by
  intro same
  have different : (exitPC layout - bodyPC layout) = BitVec.ofNat 32 171 := by
    change exitPC layout - bodyPC layout = (171 : Word)
    unfold exitPC bodyPC
    ring
  rw [same] at different
  simp at different

theorem words_pure (layout : Layout) (block : Block) (state : Machine32.State) (codeField : Nat -> Prop)
    (owned : ∀ slot, codeField (layout.fields slot)) : MultiplyWords.PureRun codeField (words layout block) state := by
  cases block
  · exact MultiplyWords.initialize_pure _ _ _ owned
  · exact MultiplyWords.guard_pure _ _ _ _ owned
  · exact MultiplyWords.body_pure _ _ _ owned
  · exact MultiplyWords.finish_pure _ _ _ owned

theorem words_frame (layout : Layout) (block : Block) (state : Machine32.State) (field : Nat)
    (outside : ∀ slot, field ≠ layout.fields slot) :
    (MultiplyWords.run (words layout block) state).memory field = state.memory field := by
  apply MultiplyWords.run_frame
  exact MultiplyLoop.pure_destinations (fun address => field ≠ address) _ state (words_pure layout block state _ outside)

theorem ready_lift (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) :
    StackReady layout.pointer layout.address (run (lift (words layout block)) state) := by
  have p := words_frame layout block state.data layout.pointer (separate.outside _ (by simp))
  have a := words_frame layout block state.data layout.address (separate.outside _ (by simp))
  rw [lift_effect]
  constructor
  · simpa only [BranchTail.slot, p] using ready.slot
  · simpa only [a, p] using ready.same
  · simpa only [p] using ready.nonwrap

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
      { data := clearCarry (MultiplyWords.run (words layout block) state.data), stack := state.stack,
        pc := state.pc + BitVec.ofNat 32 (span (words layout block)) + 11 +
          (MultiplyWords.run (words layout block) state.data).memory (callWord layout block) + 30 } := by
  rw [program, ite_eq_right active, run_append,
    round_trip_effect _ _ _ _ (call_separate layout block separate) separate.address (ready_lift layout block state separate ready), lift_effect]
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
    (ready : StackReady layout.pointer layout.address state) (field : Nat) (outside : ∀ slot, field ≠ layout.fields slot) :
    (run (program layout block) state).data.memory field = state.data.memory field := by
  by_cases finish : block = .finish
  · simp only [program, finish, ite_true, List.append_nil, lift_effect]
    exact words_frame layout .finish state.data field outside
  · rw [program_effect layout block state separate ready finish]
    exact words_frame layout block state.data field outside

theorem program_pure (layout : Layout) (block : Block) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (codeField : Nat -> Prop)
    (owned : ∀ slot, codeField (layout.fields slot)) (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    PureRun codeField (program layout block) state := by
  rw [program, pure_append]
  refine ⟨lift_pure _ _ _ (words_pure layout block state.data codeField owned), ?_⟩
  split
  · trivial
  · exact round_trip_pure _ _ _ _ (ready_lift layout block state separate ready) codeField pointerOwned addressOwned

theorem clear_guard (layout : Layout) (state : Machine32.State) :
    clearCarry (MultiplyWords.run (words layout .guard) state) = MultiplyWords.run (words layout .guard) state := rfl

theorem guard_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = guardPC layout)
    (initial : state.data.memory (layout.fields .displacement) = 0) :
    run (program layout .guard) state =
      { data := MultiplyWords.run (words layout .guard) state.data, stack := state.stack,
        pc := if state.data.memory (layout.fields .multiplier) = 0 then exitPC layout else bodyPC layout } := by
  rw [program_effect layout .guard state separate ready (by decide), clear_guard]
  have size := (literal_lengths layout.fields (delta layout) layout.pointer layout.address 0).2.1
  simp only [words, callWord] at *
  rw [size, MultiplyWords.guard_displacement _ _ _ separate.data initial, entry]
  congr 1
  split
  · change guardPC layout + (65 : Word) + 11 + delta layout + 30 = exitPC layout
    unfold guardPC exitPC delta exitContinuation bodyContinuation
    ring
  · change guardPC layout + (65 : Word) + 11 + 0 + 30 = bodyPC layout
    unfold guardPC bodyPC
    ring

theorem body_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = bodyPC layout)
    (back : state.data.memory layout.backDisplacement = backDelta layout) :
    run (program layout .body) state =
      { data := clearCarry (MultiplyWords.run (words layout .body) state.data), stack := state.stack, pc := guardPC layout } := by
  rw [program_effect layout .body state separate ready (by decide)]
  have size := (literal_lengths layout.fields (delta layout) layout.pointer layout.address 0).2.2.1
  have unchanged := words_frame layout .body state.data layout.backDisplacement (separate.outside _ (by simp))
  simp only [words, callWord] at *
  rw [size, unchanged, back, entry]
  congr 1
  change bodyPC layout + (130 : Word) + 11 + backDelta layout + 30 = guardPC layout
  unfold bodyPC guardPC backDelta guardContinuation exitContinuation
  ring

theorem entry_effect (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state) (entry : state.pc = layout.origin)
    (direct : state.data.memory layout.entryDisplacement = 0) :
    run (program layout .initial) state =
      { data := clearCarry (MultiplyWords.run (words layout .initial) state.data), stack := state.stack, pc := guardPC layout } := by
  rw [program_effect layout .initial state separate ready (by decide)]
  have size := (literal_lengths layout.fields (delta layout) layout.pointer layout.address 0).1
  have unchanged := words_frame layout .initial state.data layout.entryDisplacement (separate.outside _ (by simp))
  simp only [words, callWord] at *
  rw [size, unchanged, direct, entry]
  congr 1
  change layout.origin + (44 : Word) + 11 + 0 + 30 = guardPC layout
  unfold guardPC
  ring

theorem finish_effect (layout : Layout) (state : State) (entry : state.pc = exitPC layout) :
    run (program layout .finish) state =
      { data := MultiplyWords.run (words layout .finish) state.data, stack := state.stack, pc := endPC layout } := by
  simp only [program, ite_true, List.append_nil, lift_effect]
  have size := (literal_lengths layout.fields (delta layout) layout.pointer layout.address 0).2.2.2.1
  rw [show span (words layout .finish) = 20 from size, entry]
  congr 1
  change exitPC layout + (20 : Word) = endPC layout
  unfold exitPC endPC
  ring

end SmcTuring.Appendix.MultiplyBlocks
