module
public import SmcTuring.Appendix.DivisionByteLoop
public import SmcTuring.Appendix.DivisionCorrect

public section
namespace SmcTuring.Appendix.DivisionByteCorrect

open DivisionImage DivisionSetup DivisionByteSimulation
abbrev State := DivisionByteExecution.State
abbrev Source := DivisionControl.State
abbrev Word := BitVec 32

attribute [local irreducible] DivisionControl.run DivisionBlocks.program
  DivisionByteBlocks.run DivisionByteBlocks.forms

theorem initial_context (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (DivisionLayout.entries place x y) backing) :
    Context place x y (sourceView native) native := by
  refine ⟨view_agreement place x y native, ?_, initial_ready place x y valid backing native initial, ?_, ?_⟩
  · rw [initial]; exact DivisionLayout.initial_intact place x y backing valid
  · exact initial_call place x y valid .initial (by decide) backing native initial
  · exact initial_call place x y valid .body (by decide) backing native initial

/-- Protected literal CALL bytes and restored code-backed stack values are
sufficient to reconstruct the source context after arbitrary owned mutations. -/
theorem maintained_context (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (native : State) (intact : Intact (DivisionLayout.entries place x y) native.memory)
    (ready : Ready place native) : Context place x y (sourceView native) native := by
  refine ⟨view_agreement place x y native, intact, ready, ?_, ?_⟩
  · exact fixed_call place x y valid .initial (by decide) (by decide) native intact
  · exact fixed_call place x y valid .body (by decide) (by decide) native intact

/-- Internal division simulation; the source trace is constructed by
`execution` below from the checked all-input word/register theorem. -/
theorem divide_simulate (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address place.origin)
    (zero : source.data.memory (DivisionPackets.fields place .displacement) = 0)
    (commands : List DivisionControl.Instruction) (sourceFinal : Source)
    (execution : DivisionExecution.divide (DivisionPackets.layout place) source = some (commands, sourceFinal)) :
    ∃ events final, DivisionByteLoop.divide place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native := by
  let started := DivisionByteBlocks.run place .initial native
  let sourceStarted := DivisionControl.run (DivisionBlocks.program (DivisionPackets.layout place) .initial) source
  have leading := advance place x y valid .initial source native context entry (by intro impossible; cases impossible)
  have sourceReady := source_ready place x y valid source native context.agreement context.ready
  have separate := control_separate place valid
  have sourceEntry : source.pc = (DivisionPackets.layout place).origin := context.agreement.pc.symm.trans entry
  have startEffect := DivisionBlocks.entry_effect (DivisionPackets.layout place) source separate sourceReady sourceEntry context.direct
  have startLocation : started.pc = FieldRefinement.address (DivisionData.blockStart place .guard) := by
    have wordPC : sourceStarted.pc = DivisionBlocks.guardPC (DivisionPackets.layout place) := by
      dsimp only [sourceStarted]; rw [startEffect]
    exact leading.1.agreement.pc.trans (wordPC.trans (block_start place .guard).symm)
  have startZero : sourceStarted.data.memory (DivisionPackets.fields place .displacement) = 0 := by
    dsimp only [sourceStarted]
    rw [startEffect]
    change (DivisionWords.run (DivisionWords.initializeData (DivisionPackets.fields place) place.mod place.signed) source.data).memory
      (DivisionPackets.fields place .displacement) = 0
    rw [DivisionStages.initial_field (DivisionPackets.fields place) place.mod place.signed source.data (word_separate place valid) .displacement]
    exact zero
  simp only [DivisionExecution.divide] at execution
  change (DivisionExecution.loop 32 (DivisionPackets.layout place) sourceStarted).map _ = _ at execution
  cases recursive : DivisionExecution.loop 32 (DivisionPackets.layout place) sourceStarted with
  | none => rw [recursive] at execution; contradiction
  | some result =>
    obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ := DivisionByteLoop.simulate 32 place x y valid
      sourceStarted started leading.1 startLocation startZero result.1 result.2 recursive
    rw [recursive] at execution
    have finalSource : result.2 = sourceFinal := congrArg (fun pair => pair.2) (Option.some.inj execution)
    refine ⟨DivisionByteBlocks.forms place .initial native ++ events, final, ?_, ?_, ?_, ?_⟩
    · simp only [DivisionByteLoop.divide]
      change (DivisionByteLoop.loop 32 place started).map _ = _
      rw [byteExecution]; rfl
    · rw [←finalSource]; exact finalContext
    · exact DivisionByteExecution.trace_append leading.2.1 trace
    · rw [DivisionByteExecution.owned_append, DivisionByteBlocks.forms_run]
      exact ⟨leading.2.2, owned⟩

/-- Repeated execution constructs its complete trace from the maintained image,
stack, actual current divisor and reset displacement; no scratch initialization
or future fetch/trace is supplied. -/
theorem context_execution (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (native : State) (context : Context place x y (sourceView native) native)
    (entry : native.pc = FieldRefinement.address place.origin)
    (zero : FieldRefinement.readField native (DivisionPackets.fields place .displacement) = 0)
    (denominator : FieldRefinement.readField native (DivisionPackets.fields place .y) ≠ 0) :
    ∃ events final sourceFinal,
      DivisionByteLoop.divide place native = some (events, final) ∧
      Context place x y sourceFinal final ∧
      DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native ∧
      DivisionCorrect.Spec (DivisionPackets.layout place) (sourceView native) sourceFinal := by
  have sourceReady := source_ready place x y valid (sourceView native) native context.agreement context.ready
  obtain ⟨commands, sourceFinal, wordExecution, _, _, post⟩ := DivisionCorrect.correct (DivisionPackets.layout place)
    (sourceView native) (control_separate place valid) sourceReady entry context.direct context.back zero denominator
    (Owned (DivisionLayout.entries place x y))
    (fun block slot member => DivisionLayout.slot_owned place x y slot (DivisionLayout.written_active place block slot member))
    (DivisionLayout.pointer_owned place x y) (DivisionLayout.address_owned place x y)
  obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ :=
    divide_simulate place x y valid (sourceView native) native context entry zero commands sourceFinal wordExecution
  exact ⟨events, final, sourceFinal, byteExecution, finalContext, trace, owned, post⟩

/-- One original emitted image supplies the whole continuous byte loop. No
future trace, result, branch, intermediate state or Ready invariant is a
premise. The word theorem constructs termination within 32 body passes, and
the byte simulation fetches every actual evolving instruction individually. -/
theorem execution (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (DivisionLayout.entries place x y) backing)
    (entry : native.pc = FieldRefinement.address place.origin) (nonzero : y ≠ 0) :
    ∃ events final sourceFinal,
      DivisionByteLoop.divide place native = some (events, final) ∧
      Context place x y sourceFinal final ∧
      DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native ∧
      DivisionCorrect.Spec (DivisionPackets.layout place) (sourceView native) sourceFinal := by
  have inputs := initial_operands place x y valid backing native initial
  apply context_execution place x y valid native (initial_context place x y valid backing native initial) entry
  · exact initial_call place x y valid .guard (by decide) backing native initial
  · rw [inputs.2.1]; exact nonzero

theorem owned_run_frame (whole : List Entry) (events : List DivisionByteCode.Form) (native : State)
    (owned : DivisionByteExecution.OwnedRun (fun word => Owned whole word.toNat) events native)
    (position : Nat) (outside : ∀ field ∈ DivisionPacking.fields whole, ¬Native.ByteMemory.Inside field 4 position) :
    (DivisionByteExecution.run events native).memory position = native.memory position := by
  induction events generalizing native with
  | nil => rfl
  | cons form rest ih =>
    rw [DivisionByteExecution.run, ih _ owned.2]
    exact DivisionByteExecution.execute_frame form native position
      (outside _ ((DivisionPacking.fields_owned _ _).mpr owned.1))

theorem trace_frame (whole : List Entry) (events : List DivisionByteCode.Form) (native final : State)
    (trace : DivisionByteExecution.Trace native events final)
    (owned : DivisionByteExecution.OwnedRun (fun word => Owned whole word.toNat) events native)
    (position : Nat) (outside : ∀ field ∈ DivisionPacking.fields whole, ¬Native.ByteMemory.Inside field 4 position) :
    final.memory position = native.memory position := by
  rw [DivisionByteExecution.trace_run trace]
  exact owned_run_frame whole events native owned position outside

@[expose] def scratchFields (place : Placement) : List Nat :=
  (DivisionLayout.ownedFields place).filter (fun field =>
    decide (field ≠ DivisionPackets.fields place .x ∧ field ≠ DivisionPackets.fields place .y ∧
      field ≠ place.stackInstruction + 6 ∧ field ≠ place.stackInstruction + 2))

theorem field_cases (place : Placement) (field : Nat) (member : field ∈ DivisionLayout.ownedFields place) :
    field ∈ scratchFields place ∨ field = DivisionPackets.fields place .x ∨
      field = DivisionPackets.fields place .y ∨ field = place.stackInstruction + 6 ∨ field = place.stackInstruction + 2 := by
  by_cases hx : field = DivisionPackets.fields place .x
  · exact Or.inr (Or.inl hx)
  · by_cases hy : field = DivisionPackets.fields place .y
    · exact Or.inr (Or.inr (Or.inl hy))
    · by_cases hp : field = place.stackInstruction + 6
      · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      · by_cases ha : field = place.stackInstruction + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
        · exact Or.inl (by simp [scratchFields, member, hx, hy, hp, ha])

@[expose] def expected (place : Placement) (x y : Word) : Word :=
  if place.signed then DivisionSignedAlgebra.result place.mod x y
  else if place.mod then x.umod y else x.udiv y

@[expose] def expectedCarry (place : Placement) (x y : Word) : Bool :=
  if place.signed then DivisionSignedAlgebra.negative place.mod x y &&
    decide (0 < (BitVec.ofNat 32 (DivisionSignedAlgebra.magnitudeResult place.mod x y)).toNat ∧
      (BitVec.ofNat 32 (DivisionSignedAlgebra.magnitudeResult place.mod x y)).toNat < 2147483648)
  else false

structure Spec (place : Placement) (x y : Word) (initial final : State) : Prop where
  output : FieldRefinement.readField final (DivisionPackets.fields place .result) = expected place x y
  accumulator : final.accumulator = initial.accumulator
  stack : final.stack = initial.stack
  carry : final.carry = expectedCarry place x y
  displacement : FieldRefinement.readField final (DivisionPackets.fields place .displacement) = 0
  inputX : FieldRefinement.readField final (DivisionPackets.fields place .x) = x
  inputY : FieldRefinement.readField final (DivisionPackets.fields place .y) = y
  pc : final.pc = FieldRefinement.address (place.origin + DivisionLayout.pureSpan place)
  frame : ∀ position, (∀ field ∈ scratchFields place, ¬Native.ByteMemory.Inside field 4 position) →
    final.memory position = initial.memory position

/-- The all-input result and exact byte frame hold for any maintained image
and Ready stack, with arbitrary current scratch/result words. -/
theorem context_correct (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (native : State) (initialContext : Context place x y (sourceView native) native)
    (zero : FieldRefinement.readField native (DivisionPackets.fields place .displacement) = 0)
    (inputX : FieldRefinement.readField native (DivisionPackets.fields place .x) = x)
    (inputY : FieldRefinement.readField native (DivisionPackets.fields place .y) = y)
    (entry : native.pc = FieldRefinement.address place.origin) (nonzero : y ≠ 0) :
    ∃ events final, DivisionByteLoop.divide place native = some (events, final) ∧
      DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.run events native = final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native ∧
      Intact (DivisionLayout.entries place x y) final.memory ∧ Ready place final ∧ Spec place x y native final := by
  obtain ⟨events, final, sourceFinal, byteExecution, context, trace, owned, post⟩ := context_execution place x y valid native initialContext entry zero (by rw [inputY]; exact nonzero)
  have inputs := And.intro inputX inputY
  have finalX : FieldRefinement.readField final (DivisionPackets.fields place .x) = x := by
    rw [slot_word place x y sourceFinal final context.agreement .x (by trivial)]
    have restored := post.inputX
    change sourceFinal.data.memory (DivisionPackets.fields place .x) = FieldRefinement.readField native (DivisionPackets.fields place .x) at restored
    exact restored.trans inputs.1
  have finalY : FieldRefinement.readField final (DivisionPackets.fields place .y) = y := by
    rw [slot_word place x y sourceFinal final context.agreement .y (by trivial)]
    have restored := post.inputY
    change sourceFinal.data.memory (DivisionPackets.fields place .y) = FieldRefinement.readField native (DivisionPackets.fields place .y) at restored
    exact restored.trans inputs.2
  have firstReady := initialContext.ready
  refine ⟨events, final, byteExecution, trace, (DivisionByteExecution.trace_run trace).symm,
    owned, context.intact, context.ready, ?_⟩
  constructor
  · rw [slot_word place x y sourceFinal final context.agreement .result (by trivial)]
    have output := post.output
    change sourceFinal.data.memory (DivisionPackets.fields place .result) =
      expected place (FieldRefinement.readField native (DivisionPackets.fields place .x))
        (FieldRefinement.readField native (DivisionPackets.fields place .y)) at output
    rw [inputs.1, inputs.2] at output
    exact output
  · exact context.agreement.data.accumulator.trans post.accumulator
  · exact context.agreement.stack.trans post.stack
  · have carried := context.agreement.data.carry.trans post.carry
    change final.carry = expectedCarry place
      (FieldRefinement.readField native (DivisionPackets.fields place .x))
      (FieldRefinement.readField native (DivisionPackets.fields place .y)) at carried
    rw [inputs.1, inputs.2] at carried
    exact carried
  · rw [slot_word place x y sourceFinal final context.agreement .displacement (by trivial)]; exact post.displacement
  · exact finalX
  · exact finalY
  · rw [context.agreement.pc, post.pc]
    exact (end_code place).symm
  · intro position outside
    by_cases insideX : Native.ByteMemory.Inside (DivisionPackets.fields place .x) 4 position
    · apply FieldRefinement.equal_word_byte final native _ (DivisionLayout.slot_fits place x y valid .x (by trivial)) _ position insideX
      exact finalX.trans inputs.1.symm
    · by_cases insideY : Native.ByteMemory.Inside (DivisionPackets.fields place .y) 4 position
      · apply FieldRefinement.equal_word_byte final native _ (DivisionLayout.slot_fits place x y valid .y (by trivial)) _ position insideY
        exact finalY.trans inputs.2.symm
      · by_cases insideP : Native.ByteMemory.Inside (place.stackInstruction + 6) 4 position
        · apply FieldRefinement.equal_word_byte final native _ (pointer_fits place valid) _ position insideP
          exact context.ready.top.trans firstReady.top.symm
        · by_cases insideA : Native.ByteMemory.Inside (place.stackInstruction + 2) 4 position
          · apply FieldRefinement.equal_word_byte final native _ (address_fits place valid) _ position insideA
            exact context.ready.addressValue.trans firstReady.addressValue.symm
          · apply trace_frame _ events native final trace owned position
            intro field member
            rw [DivisionLayout.image_fields] at member
            rcases field_cases place field member with scratch | rfl | rfl | rfl | rfl
            · exact outside field scratch
            · exact insideX
            · exact insideY
            · exact insideP
            · exact insideA

/-- Positive whole byte correctness: all four original-input results and all
observed registers/PC, input owners and the ENTIRE original byte memory outside
the actual scratch/result fields. Inactive input and DEFSTACK bytes are explicitly restored.
The finite x86 bound and selected nonfaulting/current-fetch machine are stated;
physical ISA/configuration/fetch coherence remain a separate realization. -/
theorem correct (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (DivisionLayout.entries place x y) backing)
    (entry : native.pc = FieldRefinement.address place.origin) (nonzero : y ≠ 0) :
    ∃ events final, DivisionByteLoop.divide place native = some (events, final) ∧
      DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.run events native = final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native ∧
      Intact (DivisionLayout.entries place x y) final.memory ∧ Ready place final ∧ Spec place x y native final := by
  have inputs := initial_operands place x y valid backing native initial
  exact context_correct place x y valid native (initial_context place x y valid backing native initial)
    (initial_call place x y valid .guard (by decide) backing native initial) inputs.1 inputs.2.1 entry nonzero

/-- Repeat the entire original routine with its actual current image. The
returned invariant, stack readiness, input words and zero displacement supply
the next invocation, apart from restoring its entry PC. No reinitialization of
code scratch, result words, CALL targets or later continuation is needed. -/
theorem reusable_correct (place : Placement) (x y : Word) (valid : DivisionLayout.Admissible place)
    (native : State) (intact : Intact (DivisionLayout.entries place x y) native.memory)
    (ready : Ready place native)
    (zero : FieldRefinement.readField native (DivisionPackets.fields place .displacement) = 0)
    (inputX : FieldRefinement.readField native (DivisionPackets.fields place .x) = x)
    (inputY : FieldRefinement.readField native (DivisionPackets.fields place .y) = y)
    (entry : native.pc = FieldRefinement.address place.origin) (nonzero : y ≠ 0) :
    ∃ events final, DivisionByteLoop.divide place native = some (events, final) ∧
      DivisionByteExecution.Trace native events final ∧
      DivisionByteExecution.run events native = final ∧
      DivisionByteExecution.OwnedRun (fun word => Owned (DivisionLayout.entries place x y) word.toNat) events native ∧
      Intact (DivisionLayout.entries place x y) final.memory ∧ Ready place final ∧ Spec place x y native final := by
  exact context_correct place x y valid native (maintained_context place x y valid native intact ready)
    zero inputX inputY entry nonzero

theorem signed_quotient (place : Placement) (x y : Word) (initial final : State)
    (spec : Spec place x y initial final) (signed : place.signed = true) (mod : place.mod = false)
    (nonzero : y ≠ 0) (noOverflow : ¬(x = (2147483648 : Word) ∧ y = (-1 : Word))) :
    (FieldRefinement.readField final (DivisionPackets.fields place .result)).toInt =
      x.toInt.tdiv y.toInt := by
  rw [spec.output]
  simp only [expected, signed, mod, ite_true]
  exact DivisionSignedAlgebra.quotient_toInt x y nonzero noOverflow

theorem signed_remainder (place : Placement) (x y : Word) (initial final : State)
    (spec : Spec place x y initial final) (signed : place.signed = true) (mod : place.mod = true)
    (nonzero : y ≠ 0) :
    (FieldRefinement.readField final (DivisionPackets.fields place .result)).toInt =
      x.toInt.tmod y.toInt := by
  rw [spec.output]
  simp only [expected, signed, mod, ite_true]
  exact DivisionSignedAlgebra.remainder_toInt x y nonzero

theorem unsigned_quotient (place : Placement) (x y : Word) (initial final : State)
    (spec : Spec place x y initial final) (signed : place.signed = false) (mod : place.mod = false) :
    FieldRefinement.readField final (DivisionPackets.fields place .result) = x.udiv y := by
  rw [spec.output]
  simp [expected, signed, mod]

theorem unsigned_remainder (place : Placement) (x y : Word) (initial final : State)
    (spec : Spec place x y initial final) (signed : place.signed = false) (mod : place.mod = true) :
    FieldRefinement.readField final (DivisionPackets.fields place .result) = x.umod y := by
  rw [spec.output]
  simp [expected, signed, mod]

end SmcTuring.Appendix.DivisionByteCorrect
