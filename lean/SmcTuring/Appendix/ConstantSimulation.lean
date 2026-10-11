module
public import SmcTuring.Appendix.ConstantData

public section
namespace SmcTuring.Appendix.ConstantSimulation

open ConstantRefinement (dependencies)
open FieldRefinement (readField)
abbrev Instruction := ConstantWords.Instruction
abbrev State := ConstantByteExecution.State

@[expose] def Uses (data scratch : Nat) (program : List Instruction) : Prop :=
  ∀ op ∈ program, ∀ field ∈ dependencies op, field = data ∨ field = scratch

theorem shift_uses (data scratch count : Nat) : Uses data scratch (ConstantWords.shift data count) := by
  intro op member field dep
  by_cases zero : count = 0
  · simp [ConstantWords.shift, zero] at member
  · simp [ConstantWords.shift, zero] at member
    subst op
    simp [dependencies, ConstantWords.destination] at dep
    exact Or.inl dep

theorem copy_uses (data scratch : Nat) : Uses data scratch (ConstantWords.copy data scratch) := by
  intro op member field dep
  simp [ConstantWords.copy] at member
  rcases member with rfl | rfl | rfl <;>
    simp_all [dependencies, ConstantWords.destination, FieldRefinement.dependencies,
      FieldRefinement.sources, Machine32.destination]

theorem accumulate_uses (data scratch : Nat) : Uses data scratch (ConstantWords.accumulate data scratch) := by
  intro op member field dep
  simp [ConstantWords.accumulate] at member
  rcases member with rfl | rfl | rfl <;>
    simp_all [dependencies, FieldRefinement.dependencies,
      FieldRefinement.sources, Machine32.destination]

theorem tail_uses (fuel data scratch : Nat) (value : Machine32.Word) :
    Uses data scratch (ConstantWords.tail fuel data scratch value) := by
  induction fuel generalizing value with
  | zero => intro op member; simp [ConstantWords.tail] at member
  | succ fuel ih =>
      intro op member field dep
      rw [ConstantWords.tail] at member
      rcases List.mem_append.mp member with head | rest
      · exact shift_uses data scratch _ op head field dep
      · split at rest
        · simp only [List.mem_singleton] at rest
          subst op
          simpa [dependencies] using dep
        · rcases List.mem_append.mp rest with head | rest
          · exact accumulate_uses data scratch op head field dep
          · exact ih _ op rest field dep

theorem program_uses (data scratch : Nat) (value : Machine32.Word) :
    Uses data scratch (ConstantWords.program data scratch value) := by
  intro op member field dep
  rw [ConstantWords.program] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst op
    simp only [dependencies, FieldRefinement.dependencies, FieldRefinement.sources,
      Machine32.destination, List.mem_singleton] at dep
    exact Or.inl dep
  · rcases List.mem_append.mp member with head | rest
    · exact shift_uses data scratch _ op head field dep
    · split at rest
      · simp at rest
      · rcases List.mem_append.mp rest with head | rest
        · exact copy_uses data scratch op head field dep
        · exact tail_uses 31 data scratch _ op rest field dep

@[expose] def view (native : State) : Machine32.State :=
  { accumulator := native.accumulator, carry := native.carry, memory := readField native }

theorem view_agreement (fields : List Nat) (native : State) :
    FieldRefinement.Agreement fields (view native) native := by
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem compiled_agreement (data scratch : Nat) (value : Machine32.Word) (native : State)
    (layout : FieldRefinement.Layout [data, scratch]) :
    FieldRefinement.Agreement [data, scratch]
      (ConstantWords.run (ConstantWords.program data scratch value) (view native))
      (ConstantRefinement.run (ConstantWords.program data scratch value) native) := by
  apply ConstantRefinement.simulate_run layout _ _ _ (view_agreement _ native) _
    (ConstantWords.program_legal data scratch value)
  intro op member field dep
  rcases program_uses data scratch value op member field dep with rfl | rfl <;> simp

theorem carry (data scratch : Nat) (value : Machine32.Word) (native : State)
    (layout : FieldRefinement.Layout [data, scratch]) :
    (ConstantRefinement.run (ConstantWords.program data scratch value) native).carry =
      (ConstantWords.run (ConstantWords.program data scratch value) (view native)).carry :=
  (compiled_agreement data scratch value native layout).carry

/-- Entire evolving-byte effects, derived from the compiled word program.
    Live fetches are supplied by original_image_correct below. -/
theorem effect (data scratch : Nat) (value : Machine32.Word) (native : State)
    (layout : FieldRefinement.Layout [data, scratch]) (separate : scratch ≠ data) :
    readField (ConstantRefinement.run (ConstantWords.program data scratch value) native) data =
      readField native data * value ∧
    (ConstantRefinement.run (ConstantWords.program data scratch value) native).accumulator = native.accumulator ∧
    (ConstantRefinement.run (ConstantWords.program data scratch value) native).stack = native.stack ∧
    ∀ position, ¬Native.ByteMemory.Inside data 4 position ->
      ¬Native.ByteMemory.Inside scratch 4 position ->
      (ConstantRefinement.run (ConstantWords.program data scratch value) native).memory position = native.memory position := by
  have agreement := compiled_agreement data scratch value native layout
  refine ⟨?_, ?_, ConstantRefinement.run_stack _ native, ?_⟩
  · rw [agreement.words data (by simp), ConstantWords.correct _ _ _ _ separate]
    rfl
  · rw [agreement.accumulator, ConstantWords.accumulator _ _ _ _ separate]
    rfl
  · intro position outsideData outsideScratch
    apply ConstantRefinement.run_frame
    intro op member
    rcases ConstantWords.program_owned data scratch value op member with owned | owned
    · rw [owned, FieldRefinement.address_toNat data (layout.fits data (by simp))]
      exact outsideData
    · rw [owned, FieldRefinement.address_toNat scratch (layout.fits scratch (by simp))]
      exact outsideScratch

theorem two_field_layout (whole : List ConstantImage.Entry)
    (separate : ConstantImage.Separated whole)
    (capacity : ∀ entry ∈ whole, entry.pc + entry.bytes.length ≤ 2 ^ 32)
    (data scratch : Nat) (dataOwned : ConstantImage.Owned whole data)
    (scratchOwned : ConstantImage.Owned whole scratch) : FieldRefinement.Layout [data, scratch] := by
  have layout := ConstantPacking.field_layout whole separate capacity
  have included : ∀ field ∈ [data, scratch], field ∈ ConstantPacking.fields whole := by
    intro field member
    simp at member
    rcases member with equal | equal
    · rw [equal]
      exact (ConstantPacking.fields_owned whole data).mpr dataOwned
    · rw [equal]
      exact (ConstantPacking.fields_owned whole scratch).mpr scratchOwned
  exact ⟨fun field member => layout.fits field (included field member),
    fun first firstMember second secondMember distinct =>
      layout.separate first (included first firstMember) second (included second secondMember) distinct⟩

/-- Positive whole byte-trace contract for every input/constant. Premises are
    original initialization and static complete-packet placement/ownership,
    own-immediate identity and finite capacity. No future fetch/trace/result or
    intermediate state is assumed. ConstantCorrect.correct derives those static identities directly
    from the variable-length constant emitter. -/
theorem original_image_correct (whole : List ConstantImage.Entry) (start data scratch : Nat)
    (value : Machine32.Word) (backing : ConstantImage.Memory) (native : State)
    (separation : ConstantImage.Separated whole)
    (capacity : ∀ entry ∈ whole, entry.pc + entry.bytes.length ≤ 2 ^ 32)
    (dataOwned : ConstantImage.Owned whole data) (scratchOwned : ConstantImage.Owned whole scratch)
    (distinct : scratch ≠ data) (initial : native.memory = ConstantImage.image whole backing)
    (placed : ∀ entry ∈ ConstantData.entries start (ConstantWords.program data scratch value), entry ∈ whole)
    (linked : ConstantData.Linked start (ConstantWords.program data scratch value))
    (codeFits : start + ConstantData.span (ConstantWords.program data scratch value) < 2 ^ 32)
    (location : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native
      (ConstantRefinement.forms (ConstantWords.program data scratch value) native)
      (ConstantRefinement.run (ConstantWords.program data scratch value) native) ∧
    readField (ConstantRefinement.run (ConstantWords.program data scratch value) native) data = readField native data * value ∧
    (ConstantRefinement.run (ConstantWords.program data scratch value) native).accumulator = native.accumulator ∧
    (ConstantRefinement.run (ConstantWords.program data scratch value) native).stack = native.stack ∧
    ConstantByteExecution.OwnedRun (fun word => ConstantImage.Owned whole word.toNat)
      (ConstantRefinement.forms (ConstantWords.program data scratch value) native) native ∧
    ConstantImage.Intact whole (ConstantRefinement.run (ConstantWords.program data scratch value) native).memory ∧
    ∀ position, ¬Native.ByteMemory.Inside data 4 position -> ¬Native.ByteMemory.Inside scratch 4 position ->
      (ConstantRefinement.run (ConstantWords.program data scratch value) native).memory position = native.memory position := by
  have layout := two_field_layout whole separation capacity data scratch dataOwned scratchOwned
  have ownership : ∀ op ∈ ConstantWords.program data scratch value,
      ConstantImage.Owned whole (ConstantWords.destination op) := by
    intro op member
    rcases ConstantWords.program_owned data scratch value op member with owned | owned <;> simp_all
  have dependenciesFit : ∀ op ∈ ConstantWords.program data scratch value,
      ∀ field ∈ ConstantRefinement.dependencies op, field + 4 ≤ 2 ^ 32 := by
    intro op member field dep
    rcases program_uses data scratch value op member field dep with equal | equal
    · rw [equal]
      exact layout.fits data (by simp)
    · rw [equal]
      exact layout.fits scratch (by simp)
  have destFit : ∀ op ∈ ConstantWords.program data scratch value,
      ConstantWords.destination op + 4 ≤ 2 ^ 32 := fun op member =>
    dependenciesFit op member _ (ConstantRefinement.destination_dependency op)
  have effects := effect data scratch value native layout distinct
  refine ⟨ConstantData.image_trace whole _ start backing native separation initial placed linked
    dependenciesFit codeFits ownership location, effects.1, effects.2.1, effects.2.2.1, ?_, ?_, effects.2.2.2⟩
  · apply ConstantRefinement.owned_run
    intro op member
    rw [FieldRefinement.address_toNat _ (destFit op member)]
    exact ownership op member
  · apply ConstantData.run_intact whole _ native separation _ destFit ownership
    rw [initial]
    exact ConstantImage.initialized_intact whole backing separation

end SmcTuring.Appendix.ConstantSimulation
