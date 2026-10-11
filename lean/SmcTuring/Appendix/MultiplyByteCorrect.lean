module
public import SmcTuring.Appendix.MultiplyByteLoop

public section
namespace SmcTuring.Appendix.MultiplyByteCorrect

open MultiplyImage MultiplySetup MultiplyByteSimulation
abbrev State := MultiplyByteExecution.State
abbrev Source := MultiplyControl.State
abbrev Word := BitVec 32

attribute [local irreducible] MultiplyControl.run MultiplyBlocks.program
  MultiplyByteBlocks.run MultiplyByteBlocks.forms

theorem initial_context (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (MultiplyLayout.entries place x y) backing) :
    Context place x y (sourceView native) native := by
  refine ⟨view_agreement place x y native, ?_, initial_ready place x y valid backing native initial, ?_, ?_⟩
  · rw [initial]; exact MultiplyLayout.initial_intact place x y backing valid
  · exact initial_call place x y valid .initial (by decide) backing native initial
  · exact initial_call place x y valid .body (by decide) backing native initial

/-- Internal multiplication simulation; the source trace is constructed by
`execution` below from the checked all-input word/register theorem. -/
theorem multiply_simulate (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (source : Source) (native : State) (context : Context place x y source native)
    (entry : native.pc = FieldRefinement.address place.origin)
    (zero : source.data.memory (MultiplyPackets.fields place .displacement) = 0)
    (commands : List MultiplyControl.Instruction) (sourceFinal : Source)
    (execution : MultiplyExecution.multiply (MultiplyPackets.layout place) source = some (commands, sourceFinal)) :
    ∃ events final, MultiplyByteLoop.multiply place native = some (events, final) ∧
      Context place x y sourceFinal final ∧ MultiplyByteExecution.Trace native events final ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat) events native := by
  let started := MultiplyByteBlocks.run place .initial native
  let sourceStarted := MultiplyControl.run (MultiplyBlocks.program (MultiplyPackets.layout place) .initial) source
  have leading := advance place x y valid .initial source native context entry (by intro impossible; cases impossible)
  have sourceReady := source_ready place x y valid source native context.agreement context.ready
  have separate := control_separate place valid
  have sourceEntry : source.pc = (MultiplyPackets.layout place).origin := context.agreement.pc.symm.trans entry
  have startEffect := MultiplyBlocks.entry_effect (MultiplyPackets.layout place) source separate sourceReady sourceEntry context.direct
  have startLocation : started.pc = FieldRefinement.address (MultiplyData.blockStart place .guard) := by
    have wordPC : sourceStarted.pc = MultiplyBlocks.guardPC (MultiplyPackets.layout place) := by
      dsimp only [sourceStarted]; rw [startEffect]
    exact leading.1.agreement.pc.trans (wordPC.trans (block_start place .guard).symm)
  have startZero : sourceStarted.data.memory (MultiplyPackets.fields place .displacement) = 0 := by
    dsimp only [sourceStarted]
    rw [startEffect]
    change (MultiplyWords.run (MultiplyWords.initialProgram (MultiplyPackets.fields place)) source.data).memory
      (MultiplyPackets.fields place .displacement) = 0
    rw [MultiplyWords.initialize_field (MultiplyPackets.fields place) source.data (word_separate place valid) .displacement]
    exact zero
  simp only [MultiplyExecution.multiply] at execution
  change (MultiplyExecution.loop 32 (MultiplyPackets.layout place) sourceStarted).map _ = _ at execution
  cases recursive : MultiplyExecution.loop 32 (MultiplyPackets.layout place) sourceStarted with
  | none => rw [recursive] at execution; contradiction
  | some result =>
    obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ := MultiplyByteLoop.simulate 32 place x y valid
      sourceStarted started leading.1 startLocation startZero result.1 result.2 recursive
    rw [recursive] at execution
    have finalSource : result.2 = sourceFinal := congrArg (fun pair => pair.2) (Option.some.inj execution)
    refine ⟨MultiplyByteBlocks.forms place .initial native ++ events, final, ?_, ?_, ?_, ?_⟩
    · simp only [MultiplyByteLoop.multiply]
      change (MultiplyByteLoop.loop 32 place started).map _ = _
      rw [byteExecution]; rfl
    · rw [←finalSource]; exact finalContext
    · exact MultiplyByteExecution.trace_append leading.2.1 trace
    · rw [MultiplyByteExecution.owned_append, MultiplyByteBlocks.forms_run]
      exact ⟨leading.2.2, owned⟩

/-- One original emitted image supplies the whole continuous byte loop. No
future trace, result, branch, intermediate state or Ready invariant is a
premise. The word theorem constructs termination within 32 body passes, and
the byte simulation fetches every actual evolving instruction individually. -/
theorem execution (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (MultiplyLayout.entries place x y) backing)
    (entry : native.pc = FieldRefinement.address place.origin) :
    ∃ events final sourceFinal,
      MultiplyByteLoop.multiply place native = some (events, final) ∧
      Context place x y sourceFinal final ∧
      MultiplyByteExecution.Trace native events final ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat) events native ∧
      MultiplyExecution.Spec (MultiplyPackets.layout place) (sourceView native) sourceFinal := by
  have context := initial_context place x y valid backing native initial
  have sourceReady := source_ready place x y valid (sourceView native) native context.agreement context.ready
  have zero := initial_call place x y valid .guard (by decide) backing native initial
  obtain ⟨commands, sourceFinal, wordExecution, _, _, post⟩ := MultiplyExecution.correct (MultiplyPackets.layout place)
    (sourceView native) (control_separate place valid) sourceReady entry context.direct context.back zero
    (Owned (MultiplyLayout.entries place x y)) (MultiplyLayout.slot_owned place x y)
    (MultiplyLayout.pointer_owned place x y) (MultiplyLayout.address_owned place x y)
  obtain ⟨events, final, byteExecution, finalContext, trace, owned⟩ :=
    multiply_simulate place x y valid (sourceView native) native context entry zero commands sourceFinal wordExecution
  exact ⟨events, final, sourceFinal, byteExecution, finalContext, trace, owned, post⟩

theorem owned_run_frame (whole : List Entry) (events : List MultiplyByteCode.Form) (native : State)
    (owned : MultiplyByteExecution.OwnedRun (fun word => Owned whole word.toNat) events native)
    (position : Nat) (outside : ∀ field ∈ MultiplyPacking.fields whole, ¬Native.ByteMemory.Inside field 4 position) :
    (MultiplyByteExecution.run events native).memory position = native.memory position := by
  induction events generalizing native with
  | nil => rfl
  | cons form rest ih =>
    rw [MultiplyByteExecution.run, ih _ owned.2]
    exact MultiplyByteExecution.execute_frame form native position
      (outside _ ((MultiplyPacking.fields_owned _ _).mpr owned.1))

theorem trace_frame (whole : List Entry) (events : List MultiplyByteCode.Form) (native final : State)
    (trace : MultiplyByteExecution.Trace native events final)
    (owned : MultiplyByteExecution.OwnedRun (fun word => Owned whole word.toNat) events native)
    (position : Nat) (outside : ∀ field ∈ MultiplyPacking.fields whole, ¬Native.ByteMemory.Inside field 4 position) :
    final.memory position = native.memory position := by
  rw [MultiplyByteExecution.trace_run trace]
  exact owned_run_frame whole events native owned position outside

@[expose] def scratchFields (place : Placement) : List Nat :=
  [MultiplyPackets.fields place .result, MultiplyPackets.fields place .factor,
   MultiplyPackets.fields place .multiplier, MultiplyPackets.fields place .total,
   MultiplyPackets.fields place .delta, MultiplyPackets.fields place .mask,
   MultiplyPackets.fields place .displacement, MultiplyPackets.fields place .bit,
   MultiplyPackets.fields place .addMask, MultiplyPackets.fields place .addend]

theorem field_cases (place : Placement) (field : Nat) (member : field ∈ MultiplyLayout.ownedFields place) :
    field ∈ scratchFields place ∨ field = MultiplyPackets.fields place .x ∨
      field = MultiplyPackets.fields place .y ∨ field = place.stackInstruction + 6 ∨ field = place.stackInstruction + 2 := by
  simp only [MultiplyLayout.ownedFields, scratchFields, MultiplyPackets.fields,
    List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

structure Spec (place : Placement) (x y : Word) (initial final : State) : Prop where
  product : FieldRefinement.readField final (MultiplyPackets.fields place .result) = x * y
  accumulator : final.accumulator = initial.accumulator
  stack : final.stack = initial.stack
  carry : final.carry = false
  displacement : FieldRefinement.readField final (MultiplyPackets.fields place .displacement) = 0
  inputX : FieldRefinement.readField final (MultiplyPackets.fields place .x) = x
  inputY : FieldRefinement.readField final (MultiplyPackets.fields place .y) = y
  pc : final.pc = FieldRefinement.address (place.origin + 382)
  frame : ∀ position, (∀ field ∈ scratchFields place, ¬Native.ByteMemory.Inside field 4 position) →
    final.memory position = initial.memory position

/-- Positive whole byte correctness: product and all observed registers/PC,
original input owners and the ENTIRE original byte memory outside ten scratch/
result fields. Inactive input and DEFSTACK bytes are explicitly restored.
The finite x86 bound and selected nonfaulting/current-fetch machine are stated;
physical ISA/configuration/fetch coherence remain a separate realization. -/
theorem correct (place : Placement) (x y : Word) (valid : MultiplyLayout.Admissible place)
    (backing : Memory) (native : State)
    (initial : native.memory = image (MultiplyLayout.entries place x y) backing)
    (entry : native.pc = FieldRefinement.address place.origin) :
    ∃ events final, MultiplyByteLoop.multiply place native = some (events, final) ∧
      MultiplyByteExecution.Trace native events final ∧
      MultiplyByteExecution.run events native = final ∧
      MultiplyByteExecution.OwnedRun (fun word => Owned (MultiplyLayout.entries place x y) word.toNat) events native ∧
      Intact (MultiplyLayout.entries place x y) final.memory ∧ Ready place final ∧ Spec place x y native final := by
  obtain ⟨events, final, sourceFinal, byteExecution, context, trace, owned, post⟩ := execution place x y valid backing native initial entry
  have inputs := initial_operands place x y valid backing native initial
  have finalX : FieldRefinement.readField final (MultiplyPackets.fields place .x) = x := by
    rw [slot_word place x y sourceFinal final context.agreement .x]
    have restored := post.inputX
    change sourceFinal.data.memory (MultiplyPackets.fields place .x) = FieldRefinement.readField native (MultiplyPackets.fields place .x) at restored
    exact restored.trans inputs.1
  have finalY : FieldRefinement.readField final (MultiplyPackets.fields place .y) = y := by
    rw [slot_word place x y sourceFinal final context.agreement .y]
    have restored := post.inputY
    change sourceFinal.data.memory (MultiplyPackets.fields place .y) = FieldRefinement.readField native (MultiplyPackets.fields place .y) at restored
    exact restored.trans inputs.2.1
  have firstReady := initial_ready place x y valid backing native initial
  refine ⟨events, final, byteExecution, trace, (MultiplyByteExecution.trace_run trace).symm,
    owned, context.intact, context.ready, ?_⟩
  constructor
  · rw [slot_word place x y sourceFinal final context.agreement .result]
    have product := post.product
    change sourceFinal.data.memory (MultiplyPackets.fields place .result) =
      BitVec.mul (FieldRefinement.readField native (MultiplyPackets.fields place .x))
        (FieldRefinement.readField native (MultiplyPackets.fields place .y)) at product
    rw [inputs.1, inputs.2.1] at product
    exact product
  · exact context.agreement.data.accumulator.trans post.accumulator
  · exact context.agreement.stack.trans post.stack
  · exact context.agreement.data.carry.trans post.carry
  · rw [slot_word place x y sourceFinal final context.agreement .displacement]; exact post.displacement
  · exact finalX
  · exact finalY
  · rw [context.agreement.pc, post.pc]
    exact BitVec.ofNat_add_ofNat _ _
  · intro position outside
    by_cases insideX : Native.ByteMemory.Inside (MultiplyPackets.fields place .x) 4 position
    · apply FieldRefinement.equal_word_byte final native _ (MultiplyLayout.slot_fits place x y valid .x) _ position insideX
      exact finalX.trans inputs.1.symm
    · by_cases insideY : Native.ByteMemory.Inside (MultiplyPackets.fields place .y) 4 position
      · apply FieldRefinement.equal_word_byte final native _ (MultiplyLayout.slot_fits place x y valid .y) _ position insideY
        exact finalY.trans inputs.2.1.symm
      · by_cases insideP : Native.ByteMemory.Inside (place.stackInstruction + 6) 4 position
        · apply FieldRefinement.equal_word_byte final native _ (pointer_fits place valid) _ position insideP
          exact context.ready.top.trans firstReady.top.symm
        · by_cases insideA : Native.ByteMemory.Inside (place.stackInstruction + 2) 4 position
          · apply FieldRefinement.equal_word_byte final native _ (address_fits place valid) _ position insideA
            exact context.ready.addressValue.trans firstReady.addressValue.symm
          · apply trace_frame _ events native final trace owned position
            intro field member
            rw [MultiplyLayout.image_fields] at member
            rcases field_cases place field member with scratch | rfl | rfl | rfl | rfl
            · exact outside field scratch
            · exact insideX
            · exact insideY
            · exact insideP
            · exact insideA

end SmcTuring.Appendix.MultiplyByteCorrect
