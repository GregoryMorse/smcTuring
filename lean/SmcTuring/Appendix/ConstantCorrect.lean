module
public import SmcTuring.Appendix.ConstantGeometry
public import SmcTuring.Appendix.ConstantSimulation

public section
namespace SmcTuring.Appendix.ConstantCorrect
open ConstantGeometry
open FieldRefinement (readField)
abbrev State := ConstantByteExecution.State

theorem data_initial (start : Nat) (value input seed : Machine32.Word) (backing : ConstantImage.Memory) (native : State)
    (fits : start + extent value ≤ 2 ^ 32)
    (initial : native.memory = ConstantImage.image (whole start value input seed) backing) :
    readField native (data start value) = input := by
  have layout := two_field_layout start value input seed fits
  rw [←ByteImage.word_at_read_field native _ (layout.fits _ (by simp)), initial]
  have bytes := ConstantImage.image_packet _ backing (separated start value input seed)
    ⟨start + length value + 1, dataOwner start value input⟩ (data_member start value input seed)
  change Native.ByteMemory.bytesAt (ConstantImage.image (whole start value input seed) backing)
    (start + length value + 1) (ByteCode.encode (.immediate .store (FieldRefinement.address (data start value)) input)).length =
    ByteCode.encode (.immediate .store (FieldRefinement.address (data start value)) input) at bytes
  have word := (ByteImage.immediate_words _ _ _ _ _ bytes).2
  have location : data start value = start + length value + 1 + 6 := by unfold data; omega
  rw [location]
  exact word

/-- Complete corrected Listing 6 contract. Original image, entry and a bound
on its complete extent are the only premises. Operand locations, packet
separation, own-immediate identities and all future fetches are derived. -/
theorem correct (start : Nat) (value input seed : Machine32.Word) (backing : ConstantImage.Memory) (native : State)
    (fits : start + extent value ≤ 2 ^ 32)
    (initial : native.memory = ConstantImage.image (whole start value input seed) backing)
    (entry : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native (ConstantRefinement.forms (ops start value) native) (ConstantRefinement.run (ops start value) native) ∧
    readField (ConstantRefinement.run (ops start value) native) (data start value) = input * value ∧
    (ConstantRefinement.run (ops start value) native).accumulator = native.accumulator ∧
    (ConstantRefinement.run (ops start value) native).stack = native.stack ∧
    ConstantByteExecution.OwnedRun (fun word => ConstantImage.Owned (whole start value input seed) word.toNat)
      (ConstantRefinement.forms (ops start value) native) native ∧
    ConstantImage.Intact (whole start value input seed) (ConstantRefinement.run (ops start value) native).memory ∧
    (ConstantRefinement.run (ops start value) native).carry =
      (ConstantWords.run (ops start value) (ConstantSimulation.view native)).carry ∧
    (ConstantRefinement.run (ops start value) native).pc = FieldRefinement.address (start + length value) ∧
    forall position, ¬Native.ByteMemory.Inside (data start value) 4 position ->
      ¬Native.ByteMemory.Inside (scratch start value) 4 position ->
      (ConstantRefinement.run (ops start value) native).memory position = native.memory position := by
  rcases ConstantSimulation.original_image_correct (whole start value input seed) start (data start value) (scratch start value)
    value backing native (separated start value input seed) (capacity start value input seed fits)
    (data_owned start value input seed) (scratch_owned start value input seed) (distinct start value) initial
    (placed start value input seed) (linked start value) (code_fits start value fits) entry with
    ⟨trace, product, acc, stack, owned, intact, frame⟩
  refine ⟨trace, ?_, acc, stack, owned, intact, ?_, ?_, frame⟩
  · rw [data_initial start value input seed backing native fits initial] at product
    exact product
  · exact ConstantSimulation.carry _ _ value native (two_field_layout start value input seed fits)
  · have endpoint := ConstantData.run_pc (ops start value) start native entry
    rwa [ops_span] at endpoint

/-- Reuse requires only the preserved Intact invariant and re-entry. No
initializer is replayed and the ADD immediate is read from current bytes. -/
theorem reusable_trace (start : Nat) (value input seed : Machine32.Word) (native : State)
    (fits : start + extent value ≤ 2 ^ 32)
    (intact : ConstantImage.Intact (whole start value input seed) native.memory)
    (entry : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native (ConstantRefinement.forms (ops start value) native) (ConstantRefinement.run (ops start value) native) := by
  have layout := two_field_layout start value input seed fits
  have depsFit : ∀ op ∈ ops start value, ∀ field ∈ ConstantRefinement.dependencies op, field + 4 ≤ 2 ^ 32 := by
    intro op member field dep
    rcases ConstantSimulation.program_uses (data start value) (scratch start value) value op member field dep with equal | equal
    · rw [equal]; exact layout.fits _ (by simp)
    · rw [equal]; exact layout.fits _ (by simp)
  have owned : ∀ op ∈ ops start value, ConstantImage.Owned (whole start value input seed) (ConstantWords.destination op) := by
    intro op member
    rcases ConstantWords.program_owned (data start value) (scratch start value) value op member with equal | equal
    · rw [equal]; exact data_owned start value input seed
    · rw [equal]; exact scratch_owned start value input seed
  exact ConstantData.constructed_trace _ _ start native (separated start value input seed) intact
    (placed start value input seed) (linked start value) depsFit (code_fits start value fits) owned entry

/-- Complete repeated-use contract for arbitrary current data and scratch
words in the intact image. The invariant retained by correct is sufficient. -/
theorem reusable_correct (start : Nat) (value input seed : Machine32.Word) (native : State)
    (fits : start + extent value ≤ 2 ^ 32)
    (intact : ConstantImage.Intact (whole start value input seed) native.memory)
    (entry : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native (ConstantRefinement.forms (ops start value) native) (ConstantRefinement.run (ops start value) native) ∧
    readField (ConstantRefinement.run (ops start value) native) (data start value) = readField native (data start value) * value ∧
    (ConstantRefinement.run (ops start value) native).accumulator = native.accumulator ∧
    (ConstantRefinement.run (ops start value) native).stack = native.stack ∧
    ConstantByteExecution.OwnedRun (fun word => ConstantImage.Owned (whole start value input seed) word.toNat)
      (ConstantRefinement.forms (ops start value) native) native ∧
    ConstantImage.Intact (whole start value input seed) (ConstantRefinement.run (ops start value) native).memory ∧
    (ConstantRefinement.run (ops start value) native).carry =
      (ConstantWords.run (ops start value) (ConstantSimulation.view native)).carry ∧
    (ConstantRefinement.run (ops start value) native).pc = FieldRefinement.address (start + length value) ∧
    forall position, ¬Native.ByteMemory.Inside (data start value) 4 position ->
      ¬Native.ByteMemory.Inside (scratch start value) 4 position ->
      (ConstantRefinement.run (ops start value) native).memory position = native.memory position := by
  have layout := two_field_layout start value input seed fits
  have ownership : ∀ op ∈ ops start value, ConstantImage.Owned (whole start value input seed) (ConstantWords.destination op) := by
    intro op member
    rcases ConstantWords.program_owned (data start value) (scratch start value) value op member with equal | equal
    · rw [equal]; exact data_owned start value input seed
    · rw [equal]; exact scratch_owned start value input seed
  have destFits : ∀ op ∈ ops start value, ConstantWords.destination op + 4 ≤ 2 ^ 32 := by
    intro op member
    apply layout.fits
    rcases ConstantWords.program_owned (data start value) (scratch start value) value op member with equal | equal
    · rw [equal]; simp
    · rw [equal]; simp
  have effects := ConstantSimulation.effect _ _ value native layout (distinct start value)
  refine ⟨reusable_trace start value input seed native fits intact entry,
    effects.1, effects.2.1, effects.2.2.1, ?_, ?_, ?_, ?_, effects.2.2.2⟩
  · apply ConstantRefinement.owned_run
    intro op member
    rw [FieldRefinement.address_toNat _ (destFits op member)]
    exact ownership op member
  · exact ConstantData.run_intact _ _ native (separated start value input seed) intact destFits ownership
  · exact ConstantSimulation.carry _ _ value native layout
  · have endpoint := ConstantData.run_pc (ops start value) start native entry
    rwa [ops_span] at endpoint

end SmcTuring.Appendix.ConstantCorrect
