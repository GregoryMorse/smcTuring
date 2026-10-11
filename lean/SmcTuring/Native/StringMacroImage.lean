module
public import SmcTuring.Native.StringMacroLayout

public section
namespace SmcTuring.Native.StringMacroImage
open StringExecution StringMacroLayout ByteMemory

/-- One original byte image supplies every stage's complete packet window. -/
theorem windows (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bytesAt state.principal.memory p.start (prefixBytes mode p).length = prefixBytes mode p ∧
    bytesAt state.principal.memory (bodyStart mode p) (body mode p).length = body mode p ∧
    bytesAt state.principal.memory (sourceTail mode p) (sourceBytes mode p).length = sourceBytes mode p ∧
    bytesAt state.principal.memory (destinationTail mode p) (destinationBytes mode p).length = destinationBytes mode p := by
  have original := ready.initialized
  rw [split_bytes mode p ready.sizeFits] at original
  have a := StringWindow.packet_window state.principal.memory p.start [] (prefixBytes mode p) (body mode p++sourceBytes mode p++destinationBytes mode p)
    (by simpa only [List.nil_append,List.append_assoc] using original)
  have b := StringWindow.packet_window state.principal.memory p.start (prefixBytes mode p) (body mode p) (sourceBytes mode p++destinationBytes mode p)
    (by simpa only [List.append_assoc] using original)
  have c := StringWindow.packet_window state.principal.memory p.start (prefixBytes mode p++body mode p) (sourceBytes mode p) (destinationBytes mode p) original
  have d := StringWindow.packet_window state.principal.memory p.start (prefixBytes mode p++body mode p++sourceBytes mode p) (destinationBytes mode p) []
    (by simpa only [List.append_nil] using original)
  have positions := coordinates mode p
  simp only [List.length_nil,Nat.add_zero] at a
  rw [positions.1] at b
  rw [List.length_append,←Nat.add_assoc,positions.1,positions.2.1] at c
  rw [List.length_append,List.length_append,←Nat.add_assoc,←Nat.add_assoc,positions.1,positions.2.1,positions.2.2.1] at d
  exact ⟨a,b,c,d⟩

theorem initializer_windows (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bytesAt state.principal.memory p.start (StringCodec.initialSize mode) = StringInit.bytes mode p.start p.source ∧
    bytesAt state.principal.memory (StringCodec.destinationStart mode p.start) (StringCodec.initialSize mode) =
      StringInit.bytes mode (StringCodec.destinationStart mode p.start) p.destination := by
  have original := (windows mode p state ready).1
  change bytesAt state.principal.memory p.start (StringSetupTrace.bytes mode p.start p.source p.destination).length = StringSetupTrace.bytes mode p.start p.source p.destination at original
  let a := StringInit.bytes mode p.start p.source
  let b := StringCodec.exchangeBytes mode false (p.start+StringCodec.initialSize mode) (StringCodec.sourceField mode p.start)
  let c := StringInit.bytes mode (StringCodec.destinationStart mode p.start) p.destination
  let d := StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode) (StringCodec.destinationField mode p.start)
  change bytesAt state.principal.memory p.start (a++b++c++d).length = a++b++c++d at original
  have first := StringWindow.packet_window state.principal.memory p.start [] a (b++c++d)
    (by simpa only [List.nil_append,List.append_assoc] using original)
  have third := StringWindow.packet_window state.principal.memory p.start (a++b) c d original
  simp only [a,b,c,List.length_nil,Nat.add_zero,StringInit.bytes,StringCodec.initial_length,List.length_append,StringCodec.exchange_length] at first third
  have destinationPC : p.start+(StringCodec.initialSize mode+StringCodec.exchangeSize mode) = StringCodec.destinationStart mode p.start := by
    unfold StringCodec.destinationStart; omega
  rw [destinationPC] at third
  exact ⟨first,third⟩

theorem initialized_pointers (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Execution.load mode state.principal.memory (Arithmetic.encodeNat mode (StringCodec.sourceField mode p.start)) = Arithmetic.encodeNat mode p.source ∧
    Execution.load mode state.principal.memory (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start)) = Arithmetic.encodeNat mode p.destination := by
  have original := initializer_windows mode p state ready
  have fits := StringSetup.initializer_fits mode p.start (prefix_capacity mode p state ready)
  exact ⟨StringInit.initialized_pointer mode p.start p.source state.principal.memory fits.1 original.1,
    StringInit.initialized_pointer mode (StringCodec.destinationStart mode p.start) p.destination state.principal.memory fits.2 original.2⟩

theorem initial_words (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Protected.wordAt mode state.principal.memory (StringCodec.sourceField mode p.start) = Arithmetic.encodeNat mode p.source ∧
    Protected.wordAt mode state.principal.memory (StringCodec.destinationField mode p.start) = Arithmetic.encodeNat mode p.destination := by
  have pointers := initialized_pointers mode p state ready
  have fits := prefix_capacity mode p state ready
  have sourceFits := StringSetup.source_field_fits mode p.start fits
  have destinationFits := StringSetup.destination_field_fits mode p.start fits
  unfold Execution.load at pointers
  rw [Arithmetic.encode_nat_toNat mode _ sourceFits,Arithmetic.encode_nat_toNat mode _ destinationFits] at pointers
  exact pointers

theorem destination_word_outside (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state)
    (index : Fin mode.wordBytes) : ¬Inside (StringCodec.sourceField mode p.start) mode.wordBytes (p.destination+index.val) := by
  have positions := field_coordinates mode p
  have outside := ready.destinationOutside
  have small := index.isLt
  unfold Outside at outside
  unfold Inside
  rcases outside with before | after <;> omega

theorem prefix_effect (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    run mode (StringSetup.forms mode p.start p.source p.destination) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (bodyStart mode p)
        accumulator := StringInit.accumulator mode p.destination state
        memory := StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex}
      sourceIndex := Arithmetic.encodeNat mode p.source
      destinationIndex := Arithmetic.encodeNat mode p.destination} := by
  have original := initializer_windows mode p state ready
  exact StringSetup.effect mode p.start p.source p.destination state ready.entry (prefix_capacity mode p state ready)
    (destination_capacity mode p state ready).2.2 (destination_word_outside mode p state ready) original.1 original.2

theorem prefix_trace (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Trace mode state (StringSetup.forms mode p.start p.source p.destination) (run mode (StringSetup.forms mode p.start p.source p.destination) state) := by
  have positions := field_coordinates mode p
  have source := ready.sourceOutside
  have destination := ready.destinationOutside
  have initFits := StringSetup.initializer_fits mode p.start (prefix_capacity mode p state ready)
  unfold Outside at source destination
  apply StringSetupTrace.initialized_trace mode p.start p.source p.destination state ready.entry (prefix_capacity mode p state ready)
    (source_capacity mode p state ready).2.1 (destination_capacity mode p state ready).2.1
  · rcases source with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by unfold bodyStart StringCodec.bodyStart at positions; omega)
  · rcases destination with before | after
    · exact Or.inl (by unfold StringCodec.destinationStart; omega)
    · have bodyPC := StringCodec.body_coordinate mode p.start
      change StringCodec.destinationStart mode p.start+StringCodec.initialSize mode+StringCodec.exchangeSize mode = bodyStart mode p at bodyPC
      exact Or.inr (by omega)
  · exact (windows mode p state ready).1

theorem prepared_window (mode : Mode) (p : Params) (memory : Memory) (si di : Word mode) (observed count : Nat)
    (later : bodyStart mode p ≤ observed) :
    bytesAt (StringFields.prepared mode (layout mode p) memory si di) observed count = bytesAt memory observed count := by
  unfold StringFields.prepared layout
  rw [destination_cursor_frame mode p observed count _ di later,source_cursor_frame mode p observed count memory si later]

end SmcTuring.Native.StringMacroImage
