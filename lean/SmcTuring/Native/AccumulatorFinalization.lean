module
public import SmcTuring.Native.AccumulatorImage
public import SmcTuring.Native.TerminalMarker

public section
namespace SmcTuring.Native.AccumulatorFinalization
open Execution AccumulatorLayout AccumulatorEffects ControlImage

@[expose] def finalState (mode : Mode) (layout : Layout) (state : State mode) : State mode :=
  TerminalMarker.finish mode (endPC mode layout) (finish mode layout state)

/-- Current terminal bytes survive the epilogue's only final memory change.
The two earlier pointer stores restore the entire byte-memory function. -/
theorem terminal_current (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue)
    (current : ByteMemory.bytesAt state.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save) :
    ByteMemory.bytesAt (finish mode layout state).memory (endPC mode layout) 10 =
      TerminalMarker.bytes mode (endPC mode layout) := by
  rw [effect mode layout valid state entry]
  have framed := ByteMemory.bytes_at_frame state.memory layout.save
    (LittleEndian.wordEncode mode.wordBytes (load mode state.memory (Arithmetic.encodeNat mode layout.pointer)))
    (endPC mode layout) 10 (by
      intro index
      have bound := index.isLt
      simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
      omega)
  exact framed.trans current

/-- The actual final store is fetched after the three epilogue instructions.
The terminal outcome is the following PC, with all produced output retained. -/
theorem terminal_correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue)
    (capacity : endPC mode layout + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save) :
    DwordStore.step mode (finish mode layout state) = some (finalState mode layout state) ∧
    (finalState mode layout state).pc.toNat = endPC mode layout + 10 ∧
    (finalState mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.save) ∧
    (finalState mode layout state).stack = state.stack ∧
    (finalState mode layout state).carry = state.carry ∧
    (finalState mode layout state).memory = (finish mode layout state).memory := by
  have location : (finish mode layout state).pc = Arithmetic.encodeNat mode (endPC mode layout) := by
    rw [effect mode layout valid state entry]
  have ready := terminal_current mode layout valid state entry current apart
  have result := TerminalMarker.correct mode (endPC mode layout) (finish mode layout state) location capacity ready
  refine ⟨result.1,result.2.1,?_,?_,?_,result.2.2.2.2.2⟩
  · rw [finalState,result.2.2.1,effect mode layout valid state entry]
  · rw [finalState,result.2.2.2.1,effect mode layout valid state entry]
  · rw [finalState,result.2.2.2.2.1,effect mode layout valid state entry]

theorem memory_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue)
    (capacity : endPC mode layout + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save) :
    (finalState mode layout state).memory = ByteMemory.putWord mode state.memory layout.save
      (load mode state.memory (Arithmetic.encodeNat mode layout.pointer)) := by
  rw [(terminal_correct mode layout valid state entry capacity current apart).2.2.2.2.2,
    effect mode layout valid state entry]

theorem output_frame (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue)
    (capacity : endPC mode layout + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save)
    (output count : Nat) (outside : ∀ index : Fin count, ¬ByteMemory.Inside layout.save mode.wordBytes (output + index.val)) :
    ByteMemory.bytesAt (finalState mode layout state).memory output count = ByteMemory.bytesAt state.memory output count := by
  rw [memory_effect mode layout valid state entry capacity current apart]
  exact ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)

theorem live_reuse (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue)
    (capacity : endPC mode layout + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save)
    (whole : List (Entry mode)) (separate : Separated mode whole) (intact : Intact mode whole state.memory)
    (save : Owned mode whole (Arithmetic.encodeNat mode layout.save))
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer)) :
    Intact mode whole (finalState mode layout state).memory ∧
    ByteMemory.bytesAt (finalState mode layout state).memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout) := by
  rw [(terminal_correct mode layout valid state entry capacity current apart).2.2.2.2.2]
  exact ⟨AccumulatorImage.finish_intact mode layout valid state entry whole separate intact save pointer,
    terminal_current mode layout valid state entry current apart⟩

/-- Compose an actual body trace with the printed entry/exit sequence.
Only its two reserved field values, current code and marker are required at
the body boundary; future epilogue and terminal fetches are derived. -/
theorem surround (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (whole : List (Entry mode)) (separate : Separated mode whole)
    (included : ∀ helper ∈ entries mode layout, helper ∈ whole)
    (initial body : State mode) (entry : initial.pc = Arithmetic.encodeNat mode layout.prologue)
    (intact : Intact mode whole initial.memory)
    (save : Owned mode whole (Arithmetic.encodeNat mode layout.save))
    (pointer : Owned mode whole (Arithmetic.encodeNat mode layout.pointer))
    (pointerInitial : load mode initial.memory (Arithmetic.encodeNat mode layout.pointer) = Arithmetic.encodeNat mode layout.save)
    (bodyForms : List (Form mode))
    (bodyTrace : Fetch.Trace mode (saved mode layout initial) bodyForms body)
    (bodyOwned : Writes.OwnedRun mode (Owned mode whole) bodyForms (saved mode layout initial))
    (bodyEntry : body.pc = Arithmetic.encodeNat mode layout.epilogue)
    (bodySave : load mode body.memory (Arithmetic.encodeNat mode layout.save) =
      load mode (saved mode layout initial).memory (Arithmetic.encodeNat mode layout.save))
    (bodyPointer : load mode body.memory (Arithmetic.encodeNat mode layout.pointer) =
      load mode (saved mode layout initial).memory (Arithmetic.encodeNat mode layout.pointer))
    (capacity : endPC mode layout + 10 < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt body.memory (endPC mode layout) 10 = TerminalMarker.bytes mode (endPC mode layout))
    (apart : layout.save + mode.wordBytes ≤ endPC mode layout ∨ endPC mode layout + 10 ≤ layout.save) :
    Fetch.Trace mode initial ([saveForm mode layout] ++ bodyForms ++ program mode layout) (finish mode layout body) ∧
    DwordStore.step mode (finish mode layout body) = some (finalState mode layout body) ∧
    (finalState mode layout body).pc.toNat = endPC mode layout + 10 ∧
    (finalState mode layout body).accumulator = initial.accumulator ∧
    (finalState mode layout body).stack = body.stack ∧
    (finalState mode layout body).carry = body.carry ∧
    (finalState mode layout body).memory = ByteMemory.putWord mode body.memory layout.save (Arithmetic.encodeNat mode layout.save) ∧
    Intact mode whole (finalState mode layout body).memory := by
  have savedIntact := AccumulatorImage.saved_intact mode layout valid initial entry whole separate intact save
  have bodyIntact := trace_intact mode whole (saved mode layout initial) body bodyForms separate savedIntact bodyOwned bodyTrace
  have leading := AccumulatorImage.save_trace mode layout valid initial entry whole included intact
  have trailing := AccumulatorImage.trace mode layout valid body bodyEntry whole included separate bodyIntact save pointer
  have nativeTrace := Fetch.trace_append mode (Fetch.trace_append mode leading bodyTrace) trailing
  have terminal := terminal_correct mode layout valid body bodyEntry capacity current apart
  have original : load mode body.memory (Arithmetic.encodeNat mode layout.save) = initial.accumulator :=
    bodySave.trans (saved_value mode layout valid initial entry)
  have pointerValue : load mode body.memory (Arithmetic.encodeNat mode layout.pointer) = Arithmetic.encodeNat mode layout.save :=
    bodyPointer.trans ((saved_pointer mode layout valid initial entry).trans pointerInitial)
  exact ⟨nativeTrace,terminal.1,terminal.2.1,terminal.2.2.1.trans original,
    terminal.2.2.2.1,terminal.2.2.2.2.1,
    (memory_effect mode layout valid body bodyEntry capacity current apart).trans (by rw [pointerValue]),
    (live_reuse mode layout valid body bodyEntry capacity current apart whole separate bodyIntact save pointer).1⟩

/-- Every native instruction of the prologue/body/epilogue writes to its
declared code operands. The following DWORD terminal footprint is separate. -/
theorem surrounding_pure (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (owns : Word mode → Prop) (initial body : State mode)
    (entry : initial.pc = Arithmetic.encodeNat mode layout.prologue)
    (save : owns (Arithmetic.encodeNat mode layout.save))
    (pointer : owns (Arithmetic.encodeNat mode layout.pointer))
    (bodyForms : List (Form mode))
    (bodyTrace : Fetch.Trace mode (saved mode layout initial) bodyForms body)
    (bodyOwned : Writes.OwnedRun mode owns bodyForms (saved mode layout initial))
    (bodyEntry : body.pc = Arithmetic.encodeNat mode layout.epilogue) :
    Writes.OwnedRun mode owns ([saveForm mode layout] ++ bodyForms ++ program mode layout) initial := by
  have bodyRun := (Fetch.trace_run_eq mode bodyTrace).symm
  change owns (Writes.address mode (saveForm mode layout) initial) ∧
    Writes.OwnedRun mode owns (bodyForms ++ program mode layout) (saved mode layout initial)
  rw [AccumulatorImage.save_address mode layout valid initial entry,Writes.owned_run_append,bodyRun]
  exact ⟨save,bodyOwned,AccumulatorImage.supported_run mode layout valid body bodyEntry owns save pointer⟩

/-- Original declared pointer bytes imply the required save-slot address.
The first instruction establishes the saved accumulator for any entry value. -/
theorem original_prologue (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (whole : List (Entry mode)) (backing : ByteMemory.Memory) (separate : Separated mode whole)
    (included : ∀ helper ∈ entries mode layout, helper ∈ whole)
    (initial : State mode) (initialized : initial.memory = image mode whole backing)
    (entry : initial.pc = Arithmetic.encodeNat mode layout.prologue)
    (save : Owned mode whole (Arithmetic.encodeNat mode layout.save))
    (owner : Nat) (member : (⟨owner,.owned (Arithmetic.encodeNat mode layout.save)⟩ : Entry mode) ∈ whole)
    (field : layout.pointer = owner + moffsOperandOffset mode) :
    Fetch.Trace mode initial [saveForm mode layout] (saved mode layout initial) ∧
    load mode (saved mode layout initial).memory (Arithmetic.encodeNat mode layout.save) = initial.accumulator ∧
    load mode (saved mode layout initial).memory (Arithmetic.encodeNat mode layout.pointer) = Arithmetic.encodeNat mode layout.save ∧
    Intact mode whole (saved mode layout initial).memory := by
  have intact : Intact mode whole initial.memory := by rw [initialized]; exact initialized_intact mode whole backing separate
  have fits : owner + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes) := by
    have bound := valid.pointerFits
    have positive : 0 < mode.wordBytes := by cases mode <;> decide
    rw [field] at bound
    omega
  have value : load mode initial.memory (Arithmetic.encodeNat mode layout.pointer) = Arithmetic.encodeNat mode layout.save := by
    rw [initialized,field]
    exact AccumulatorImage.owner_value mode whole backing separate owner _ member fits
  exact ⟨AccumulatorImage.save_trace mode layout valid initial entry whole included intact,
    saved_value mode layout valid initial entry,
    (saved_pointer mode layout valid initial entry).trans value,
    AccumulatorImage.saved_intact mode layout valid initial entry whole separate intact save⟩

end SmcTuring.Native.AccumulatorFinalization
