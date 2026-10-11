module
public import SmcTuring.SMC.Control
public import SmcTuring.SMC.NumericEncoding

public section

namespace SmcTuring.SMC

/-- Slots: candidate label/value, boundary label/value, zero label/value,
continuation label/value, terminal label/value, mask label/value, subtraction
scratch, selected target, stack-top constant, and return-address code field. -/
structure GuardLayout where
  field : Fin 16 → Int
  injective : Function.Injective field

@[simp] theorem guard_field_eq (layout : GuardLayout) (a b : Fin 16) :
    layout.field a = layout.field b ↔ a = b :=
  ⟨fun equal => layout.injective equal, congrArg layout.field⟩

structure GuardReady (layout : GuardLayout) (s : State) (candidate boundary continuation terminal wordBytes : Int) : Prop where
  candidateLabel : s.memory (layout.field 0) = layout.field 1
  candidateValue : s.memory (layout.field 1) = candidate
  boundaryLabel : s.memory (layout.field 2) = layout.field 3
  boundaryValue : s.memory (layout.field 3) = boundary
  zeroLabel : s.memory (layout.field 4) = layout.field 5
  zeroValue : s.memory (layout.field 5) = 0
  continuationLabel : s.memory (layout.field 6) = layout.field 7
  continuationValue : s.memory (layout.field 7) = continuation
  terminalLabel : s.memory (layout.field 8) = layout.field 9
  terminalValue : s.memory (layout.field 9) = terminal
  maskLabel : s.memory (layout.field 10) = layout.field 11
  stackTop : s.memory (layout.field 14) = layout.field 15 + wordBytes

@[expose] def guardProgram (layout : GuardLayout) : List Header :=
  compareProgram (layout.field 0) (layout.field 2) (layout.field 12) ++
    borrowMaskProgram (layout.field 4) (layout.field 11) ++
    selectionProgram (layout.field 6) (layout.field 8) (layout.field 10) (layout.field 13) ++
    (stackResetProgram (layout.field 14) ++ [.call (.operand (layout.field 13))])

@[expose] def guardCompareResult (layout : GuardLayout) (s : State) (candidate boundary : Int) : State :=
  { s with
    acc := boundary
    memory := write s.memory (layout.field 12) (candidate - boundary)
    carry := decide (candidate < boundary)
    pc := s.pc + 10 }

@[expose] def guardMaskResult (layout : GuardLayout) (s : State) (candidate boundary : Int) : State :=
  { guardCompareResult layout s candidate boundary with
    acc := 0
    memory := write (guardCompareResult layout s candidate boundary).memory (layout.field 11)
      (if candidate < boundary then -1 else 0)
    pc := s.pc + 16 }

@[expose] def guardSelectionResult (layout : GuardLayout) (s : State)
    (candidate boundary continuation terminal : Int) : State :=
  { guardMaskResult layout s candidate boundary with
    acc := continuation
    memory := write (guardMaskResult layout s candidate boundary).memory (layout.field 13)
      (if candidate < boundary then terminal else continuation)
    carry := false
    pc := s.pc + 36 }

theorem guard_compare_correct (layout : GuardLayout) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes) :
    run wordBytes (compareProgram (layout.field 0) (layout.field 2) (layout.field 12)) s =
      guardCompareResult layout s candidate boundary := by
  have stable : StableRead s (layout.field 2) (layout.field 12) := by
    simp [StableRead, ready.boundaryLabel]
  rw [compare_program_correct _ _ _ _ _ stable]
  simp [guardCompareResult, ready.candidateLabel, ready.candidateValue, ready.boundaryLabel, ready.boundaryValue]

theorem guard_mask_correct (layout : GuardLayout) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes) :
    run wordBytes (borrowMaskProgram (layout.field 4) (layout.field 11))
      (guardCompareResult layout s candidate boundary) = guardMaskResult layout s candidate boundary := by
  have zero : (guardCompareResult layout s candidate boundary).memory
      ((guardCompareResult layout s candidate boundary).memory (layout.field 4)) = 0 := by
    simp [guardCompareResult, write, ready.zeroLabel, ready.zeroValue]
  rw [borrow_mask_correct _ _ _ _ zero]
  simp [guardCompareResult, guardMaskResult, Int.add_assoc]

theorem guard_selection_correct (layout : GuardLayout) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes) :
    run wordBytes (selectionProgram (layout.field 6) (layout.field 8) (layout.field 10) (layout.field 13))
      (guardMaskResult layout s candidate boundary) =
      guardSelectionResult layout s candidate boundary continuation terminal := by
  have cs : StableRead (guardMaskResult layout s candidate boundary) (layout.field 6) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.continuationLabel]
  have ts : StableRead (guardMaskResult layout s candidate boundary) (layout.field 8) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.terminalLabel]
  have ms : StableRead (guardMaskResult layout s candidate boundary) (layout.field 10) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.maskLabel]
  have mask : (guardMaskResult layout s candidate boundary).memory
      ((guardMaskResult layout s candidate boundary).memory (layout.field 10)) =
      if decide (candidate < boundary) then -1 else 0 := by
    simp [guardMaskResult, guardCompareResult, write, ready.maskLabel]
  rw [selection_program_correct _ _ _ _ _ _ (decide (candidate < boundary)) cs ts ms mask]
  simp [guardSelectionResult, guardMaskResult, guardCompareResult, write, ready.continuationLabel,
    ready.continuationValue, ready.terminalLabel, ready.terminalValue, Int.add_assoc]

theorem guard_program_correct (layout : GuardLayout) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes) :
    run wordBytes (guardProgram layout) s =
      { guardSelectionResult layout s candidate boundary continuation terminal with
        stack := layout.field 15
        pc := if candidate < boundary then terminal else continuation
        memory := write (guardSelectionResult layout s candidate boundary continuation terminal).memory
          (layout.field 15) (s.pc + 39) } := by
  simp only [guardProgram, run_append]
  rw [guard_compare_correct layout wordBytes s candidate boundary continuation terminal ready,
    guard_mask_correct layout wordBytes s candidate boundary continuation terminal ready,
    guard_selection_correct layout wordBytes s candidate boundary continuation terminal ready]
  have top : (guardSelectionResult layout s candidate boundary continuation terminal).memory (layout.field 14) =
      layout.field 15 + wordBytes := by
    simp [guardSelectionResult, guardMaskResult, guardCompareResult, write, ready.stackTop]
  rw [← run_append wordBytes (stackResetProgram (layout.field 14)) [.call (.operand (layout.field 13))]
    (guardSelectionResult layout s candidate boundary continuation terminal),
    reset_call_operand_correct _ _ _ _ _ top]
  simp [guardSelectionResult, guardMaskResult, guardCompareResult, write, Int.add_assoc]

theorem guard_program_pure (layout : GuardLayout) (codeField : Int → Prop) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes)
    (code : ∀ slot, codeField (layout.field slot)) :
    PureRun codeField wordBytes (guardProgram layout) s := by
  have boundaryStable : StableRead s (layout.field 2) (layout.field 12) := by
    simp [StableRead, ready.boundaryLabel]
  have cs : StableRead (guardMaskResult layout s candidate boundary) (layout.field 6) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.continuationLabel]
  have ts : StableRead (guardMaskResult layout s candidate boundary) (layout.field 8) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.terminalLabel]
  have ms : StableRead (guardMaskResult layout s candidate boundary) (layout.field 10) (layout.field 13) := by
    simp [StableRead, guardMaskResult, guardCompareResult, write, ready.maskLabel]
  have top : (guardSelectionResult layout s candidate boundary continuation terminal).memory (layout.field 14) =
      layout.field 15 + wordBytes := by
    simp [guardSelectionResult, guardMaskResult, guardCompareResult, write, ready.stackTop]
  simp only [guardProgram, pure_append, run_append]
  rw [guard_compare_correct layout wordBytes s candidate boundary continuation terminal ready,
    guard_mask_correct layout wordBytes s candidate boundary continuation terminal ready,
    guard_selection_correct layout wordBytes s candidate boundary continuation terminal ready]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · apply compare_program_pure _ _ _ _ _ _ boundaryStable (code 0) _ (code 2) _ (code 12)
    · simpa only [ready.candidateLabel] using code 1
    · simpa only [ready.boundaryLabel] using code 3
  · apply borrow_mask_pure _ _ _ _ _ (code 4) _ (code 11)
    simpa [guardCompareResult, write, ready.zeroLabel] using code 5
  · apply selection_program_pure _ _ _ _ _ _ _ cs ts ms (code 6) _ (code 8) _ (code 10) _ (code 13)
    · simpa [guardMaskResult, guardCompareResult, write, ready.continuationLabel] using code 7
    · simpa [guardMaskResult, guardCompareResult, write, ready.terminalLabel] using code 9
    · simpa [guardMaskResult, guardCompareResult, write, ready.maskLabel] using code 11
  · exact stack_reset_pure _ _ _ _ (code 14)
  · rw [stack_reset_correct]
    simpa [PureRun, WritesCode, footprint, decode, top] using code 15

theorem guard_memory_frame (layout : GuardLayout) (wordBytes : Int) (s : State)
    (candidate boundary continuation terminal field : Int)
    (ready : GuardReady layout s candidate boundary continuation terminal wordBytes)
    (scratchSeparate : field ≠ layout.field 12) (maskSeparate : field ≠ layout.field 11)
    (targetSeparate : field ≠ layout.field 13) (stackSeparate : field ≠ layout.field 15) :
    (run wordBytes (guardProgram layout) s).memory field = s.memory field := by
  rw [guard_program_correct layout wordBytes s candidate boundary continuation terminal ready]
  simp [guardSelectionResult, guardMaskResult, guardCompareResult, write,
    scratchSeparate, maskSeparate, targetSeparate, stackSeparate]

theorem guard_numeric_rep (layout : GuardLayout) (data : Layout) (wordBytes : Int)
    (source : Dolan.Four.State) (target : State) (candidate boundary continuation terminal : Int)
    (rep : NumericRep data source target)
    (ready : GuardReady layout target candidate boundary continuation terminal wordBytes)
    (outside : ∀ slot ∈ ([12, 11, 13, 15] : List (Fin 16)), ¬ codeField data (layout.field slot)) :
    NumericRep data source (run wordBytes (guardProgram layout) target) := by
  have frame : ∀ field, codeField data field → (run wordBytes (guardProgram layout) target).memory field = target.memory field := by
    intro field code
    apply guard_memory_frame layout wordBytes target candidate boundary continuation terminal field ready
    · exact data_field_separate data _ _ (outside 12 (by simp)) code
    · exact data_field_separate data _ _ (outside 11 (by simp)) code
    · exact data_field_separate data _ _ (outside 13 (by simp)) code
    · exact data_field_separate data _ _ (outside 15 (by simp)) code
  constructor
  · intro r
    rw [frame _ (register_is_code data r)]
    exact rep.1 r
  · intro p
    rw [frame _ (heap_is_code data p)]
    exact rep.2 p

/-- With a Boolean source offset, the guard's actual CALL selects terminal
exactly for an invalid source base. Reached-offset safety is a separate global
invariant, required before using this lemma for fault reflection. -/
theorem guard_typed_address_correct (layout : GuardLayout) (data : Layout) (wordBytes : Int)
    (source : Dolan.Four.State) (target : State) (base offset : Dolan.Four.Register)
    (choice : Bool) (continuation terminal : Int)
    (offsetValue : source.registers offset = .offset choice)
    (ready : GuardReady layout target
      (encodeWord data (source.registers base) + encodeWord data (source.registers offset))
      (heapBase data) continuation terminal wordBytes) :
    (run wordBytes (guardProgram layout) target).pc =
      if Dolan.Four.address source base offset = none then terminal else continuation := by
  rw [guard_program_correct layout wordBytes target _ _ continuation terminal ready]
  cases baseValue : source.registers base with
  | address cell =>
    have high := heap_field_after_base data (cell, choice)
    simp only [offsetValue, indexed_address_correct]
    have valid : ¬ heapField data (cell, choice) < heapBase data := by omega
    simp [valid, Dolan.Four.address, baseValue, offsetValue]
  | offset other =>
    have low := flags_below_heap data other choice
    simp [baseValue, offsetValue, low, Dolan.Four.address]

/-- An offset tag check uses the same code-writing guard with its targets
swapped: low Boolean words continue, and encoded address words terminate.
Together with the base guard this removes a global offset-typing hypothesis. -/
theorem guard_offset_tag_correct (layout : GuardLayout) (data : Layout) (wordBytes : Int)
    (value : Dolan.Mov.Word) (target : State) (continuation terminal : Int)
    (ready : GuardReady layout target (encodeWord data value) (heapBase data) terminal continuation wordBytes) :
    (run wordBytes (guardProgram layout) target).pc =
      if ∃ choice, value = .offset choice then continuation else terminal := by
  rw [guard_program_correct layout wordBytes target _ _ terminal continuation ready]
  simp only [encode_word_below_heap_iff]

end SmcTuring.SMC
