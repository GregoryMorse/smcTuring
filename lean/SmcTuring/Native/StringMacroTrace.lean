module
public import SmcTuring.Native.StringMacroEffects

public section
namespace SmcTuring.Native.StringMacroTrace
open StringExecution StringMacroLayout StringMacroEffects ByteMemory

theorem setup_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode state (StringSetup.forms mode p.start p.source p.destination) (setup mode p state) :=
  StringMacroImage.prefix_trace mode p state ready

theorem body_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode (setup mode p state) (StringMoves.forms mode (StringPlan.widths mode p.size)) (copied mode p state) := by
  have positions := field_coordinates mode p
  have total := StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have si : (setup mode p state).sourceIndex.toNat = p.source := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (source_capacity mode p state ready).2.2]
  have di : (setup mode p state).destinationIndex.toNat = p.destination := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (destination_capacity mode p state ready).2.2]
  apply StringMoveTrace.constructed_trace mode _ (bodyStart mode p) _ (StringPlan.legal mode p.size)
  · rw [setup_effect mode p state ready]; exact ready.forward
  · rw [si,total]; exact (source_capacity mode p state ready).1
  · rw [di,total]; exact (destination_capacity mode p state ready).1
  · change bodyStart mode p+(body mode p).length < _
    rw [(coordinates mode p).2.1]
    have fits := ready.codeFits
    omega
  · unfold StringMoveTrace.CodeSeparate
    rw [di,total]
    change p.destination+p.size ≤ bodyStart mode p ∨ bodyStart mode p+(body mode p).length ≤ p.destination
    have outside := ready.destinationOutside
    unfold Outside at outside
    rw [(coordinates mode p).2.1]
    rcases outside with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rw [setup_effect mode p state ready]
  · rw [setup_effect mode p state ready]
    change bytesAt (StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
      (bodyStart mode p) (body mode p).length = body mode p
    rw [StringMacroImage.prepared_window mode p _ _ _ _ _ (Nat.le_refl _)]
    exact (StringMacroImage.windows mode p state ready).2.1

theorem copied_window (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) (observed count : Nat)
    (window : bodyStart mode p ≤ observed ∧ observed+count ≤ endpoint mode p) :
    bytesAt (copied mode p state).principal.memory observed count = bytesAt state.principal.memory observed count := by
  rw [copied_effect mode p state ready]
  unfold StringFields.copied layout
  rw [copy_code_frame mode p state ready _ observed count ⟨by have pos := field_coordinates mode p; omega,window.2⟩]
  exact StringMacroImage.prepared_window mode p _ _ _ observed count window.1

theorem source_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode (copied mode p state)
      (StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size) (sourceRestored mode p state) := by
  have positions := field_coordinates mode p
  have coords := coordinates mode p
  apply StringRestore.trace mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size _
  · rw [copied_effect mode p state ready]
  · exact fun _ => (tail_ranges mode p ready.sizeFits).1
  · exact StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)
  · exact ready.sizeFits
  · change destinationTail mode p < _
    have fits := ready.codeFits
    omega
  · intro index
    unfold Inside
    omega
  · change bytesAt (copied mode p state).principal.memory (sourceTail mode p) (sourceBytes mode p).length = sourceBytes mode p
    rw [copied_window mode p state ready _ _ ⟨positions.2.2.2.1,by omega⟩]
    exact (StringMacroImage.windows mode p state ready).2.2.1

theorem destination_window (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bytesAt (sourceRestored mode p state).principal.memory (destinationTail mode p) (destinationBytes mode p).length = destinationBytes mode p := by
  have positions := field_coordinates mode p
  have coords := coordinates mode p
  rw [source_effect mode p state ready]
  rw [source_cursor_frame mode p _ _ _ _ (by omega),copied_window mode p state ready _ _ ⟨by omega,by omega⟩]
  exact (StringMacroImage.windows mode p state ready).2.2.2

theorem destination_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode (sourceRestored mode p state)
      (StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size) (finish mode p state) := by
  have positions := field_coordinates mode p
  have endPC : StringRestore.endpoint mode (destinationTail mode p) p.size = endpoint mode p := by
    simp only [StringRestore.endpoint,destinationTail,sourceTail,endpoint,StringCodec.endpoint]; omega
  apply StringRestore.trace mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size _
  · rw [source_effect mode p state ready]
  · exact fun _ => (tail_ranges mode p ready.sizeFits).2.2.1
  · exact StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)
  · exact ready.sizeFits
  · rw [endPC]; exact ready.codeFits
  · intro index
    unfold Inside
    omega
  · exact destination_window mode p state ready

/-- Every live fetch follows from one original full macro image and static
resources. No stage-ready premise, future load or address-hit is supplied. -/
theorem trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode state (StringProgram.forms mode p.start p.source p.destination p.size) (finish mode p state) := by
  exact trace_append mode (trace_append mode (trace_append mode (setup_trace mode p state ready)
    (body_trace mode p state ready)) (source_trace mode p state ready)) (destination_trace mode p state ready)

/-- Continuous original-image execution copies the original source bytes,
restores both index words and all code bytes, derives CF=0, retains SP/DF,
and states DEFDATA's actual x86/x64 accumulator behavior explicitly. -/
theorem correct (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode state (StringProgram.forms mode p.start p.source p.destination p.size)
      {state with principal := {state.principal with
        pc := Arithmetic.encodeNat mode (endpoint mode p)
        accumulator := StringInit.accumulator mode p.destination state
        carry := false
        memory := putBytes state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size)}} := by
  rw [←finish_effect mode p state ready]
  exact trace mode p state ready

theorem code_preserved (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bytesAt (finish mode p state).principal.memory p.start (bytes mode p).length = bytes mode p := by
  rw [finish_effect mode p state ready,copy_code_frame mode p state ready _ _ _ ⟨(Nat.le_refl _),by
    have extent := StringCodec.whole_length mode p.start p.source p.destination p.size
    have positions := field_coordinates mode p
    change (bytes mode p).length=endpoint mode p-p.start at extent
    rw [extent]
    omega⟩]
  exact ready.initialized

@[expose] def reenter (mode : Mode) (p : Params) (state : State mode) : State mode :=
  {finish mode p state with principal := {(finish mode p state).principal with pc := Arithmetic.encodeNat mode p.start}}

theorem reusable (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) : Ready mode p (reenter mode p state) := by
  refine ⟨rfl,?_,ready.sizeFits,ready.codeFits,ready.sourceFits,ready.destinationFits,ready.buffers,ready.sourceOutside,ready.destinationOutside,?_⟩
  · change (finish mode p state).backwards=false
    rw [finish_effect mode p state ready]; exact ready.forward
  · exact code_preserved mode p state ready


theorem run_correct (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    run mode (StringProgram.forms mode p.start p.source p.destination p.size) state =
      {state with principal := {state.principal with
        pc := Arithmetic.encodeNat mode (endpoint mode p)
        accumulator := StringInit.accumulator mode p.destination state
        carry := false
        memory := putBytes state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size)}} := by
  rw [program_run]
  exact finish_effect mode p state ready

theorem frame (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) (position : Nat)
    (outside : Not (Inside p.destination p.size position)) :
    (finish mode p state).principal.memory position = state.principal.memory position := by
  rw [finish_effect mode p state ready]
  exact put_frame _ _ _ _ (by simpa only [bytes_at_length] using outside)

theorem source_preserved (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bytesAt (finish mode p state).principal.memory p.source p.size = bytesAt state.principal.memory p.source p.size := by
  rw [finish_effect mode p state ready]
  exact bytes_at_frame _ _ _ _ _ (by simpa only [bytes_at_length] using StringCopy.source_outside p.source p.destination p.size ready.buffers)

theorem reentry_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode (reenter mode p state) (StringProgram.forms mode p.start p.source p.destination p.size)
      (finish mode p (reenter mode p state)) := trace mode p _ (reusable mode p state ready)

end SmcTuring.Native.StringMacroTrace
