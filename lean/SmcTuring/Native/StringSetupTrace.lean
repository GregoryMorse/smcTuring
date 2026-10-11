module
public import SmcTuring.Native.StringSetup

public section
namespace SmcTuring.Native.StringSetupTrace
open StringExecution

@[expose] def bytes (mode : Mode) (start source destination : Nat) : List LittleEndian.Byte :=
  StringInit.bytes mode start source++StringCodec.exchangeBytes mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)++
  StringInit.bytes mode (StringCodec.destinationStart mode start) destination++
  StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)

theorem forms_encoding (mode : Mode) (start source destination : Nat) :
    ((StringSetup.forms mode start source destination).map (StringForm.encode mode)).flatten = bytes mode start source destination := by
  simp only [StringSetup.forms,StringSetup.sourceForms,bytes,List.map_append,List.flatten_append,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,StringInit.forms_encoding,StringOperands.exchange_encoding]

theorem source_field_frame (mode : Mode) (start observed count : Nat) (memory : ByteMemory.Memory) (si : Word mode)
    (later : start+StringCodec.initialSize mode ≤ observed) :
    ByteMemory.bytesAt (ByteMemory.putWord mode memory (StringCodec.sourceField mode start) si) observed count = ByteMemory.bytesAt memory observed count := by
  unfold ByteMemory.putWord
  apply ByteMemory.bytes_at_frame
  intro index
  have endField := StringCodec.field_end mode start
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  omega

theorem source_trace (mode : Mode) (start source : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes))
    (sourceFits : source+mode.wordBytes < 2^(8*mode.wordBytes))
    (separate : source+mode.wordBytes ≤ start ∨ start+StringCodec.initialSize mode ≤ source)
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = StringInit.bytes mode start source)
    (exchangeCurrent : ByteMemory.bytesAt state.principal.memory (start+StringCodec.initialSize mode) (StringCodec.exchangeSize mode) =
      StringCodec.exchangeBytes mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)) :
    Trace mode state (StringSetup.sourceForms mode start source) (run mode (StringSetup.sourceForms mode start source) state) := by
  have initialFits := (StringSetup.initializer_fits mode start fits).1
  have initialTrace := StringInitTrace.trace mode start source state location initialFits sourceFits separate current
  have effect := StringInit.effect mode start source state location initialFits current
  have fetched : StringForm.fetch mode (run mode (StringInit.forms mode start source) state).principal.memory
      (run mode (StringInit.forms mode start source) state).principal.pc.toNat =
        some (StringOperands.exchange mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)) := by
    rw [effect,Arithmetic.encode_nat_toNat mode (start+StringCodec.initialSize mode) initialFits]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [StringOperands.exchange_encoding,StringCodec.exchange_length]
    exact exchangeCurrent
  have exchangeTrace : Trace mode (run mode (StringInit.forms mode start source) state)
      [StringOperands.exchange mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)]
      (execute mode (StringOperands.exchange mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start))
        (run mode (StringInit.forms mode start source) state)) := .step fetched (.nil _)
  have combined := trace_append mode initialTrace exchangeTrace
  simpa only [StringSetup.sourceForms,run_append,run] using combined

/-- Actual entire prefix trace from four original windows only. Saving SI
preserves the second initializer and exchange packets; both DEFDATA readers
restore memory, and all later readiness follows from those executed effects. -/
theorem trace (mode : Mode) (start source destination : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes))
    (sourceFits : source+mode.wordBytes < 2^(8*mode.wordBytes))
    (destinationFits : destination+mode.wordBytes < 2^(8*mode.wordBytes))
    (sourceSeparate : source+mode.wordBytes ≤ start ∨ start+StringCodec.initialSize mode ≤ source)
    (destinationSeparate : destination+mode.wordBytes ≤ StringCodec.destinationStart mode start ∨
      StringCodec.destinationStart mode start+StringCodec.initialSize mode ≤ destination)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = StringInit.bytes mode start source)
    (sourceExchangeCurrent : ByteMemory.bytesAt state.principal.memory (start+StringCodec.initialSize mode) (StringCodec.exchangeSize mode) =
      StringCodec.exchangeBytes mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start))
    (destinationCurrent : ByteMemory.bytesAt state.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) =
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination)
    (destinationExchangeCurrent : ByteMemory.bytesAt state.principal.memory (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.exchangeSize mode) =
      StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)) :
    Trace mode state (StringSetup.forms mode start source destination) (run mode (StringSetup.forms mode start source destination) state) := by
  let saved := run mode (StringSetup.sourceForms mode start source) state
  have firstTrace := source_trace mode start source state location fits sourceFits sourceSeparate sourceCurrent sourceExchangeCurrent
  have savedEffect := StringSetup.source_effect mode start source state location fits sourceCurrent
  have savedPC : saved.principal.pc = Arithmetic.encodeNat mode (StringCodec.destinationStart mode start) := by
    rw [show saved = run mode (StringSetup.sourceForms mode start source) state from rfl,savedEffect]
  have savedCurrent : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) =
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination := by
    rw [show saved = run mode (StringSetup.sourceForms mode start source) state from rfl,savedEffect,StringSetup.destination_window,destinationCurrent]
  have savedExchange : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.exchangeSize mode) =
      StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start) := by
    rw [show saved = run mode (StringSetup.sourceForms mode start source) state from rfl,savedEffect,
      source_field_frame mode start _ _ state.principal.memory state.sourceIndex (by unfold StringCodec.destinationStart; omega),destinationExchangeCurrent]
  have initialFits := (StringSetup.initializer_fits mode start fits).2
  have middleTrace := StringInitTrace.trace mode (StringCodec.destinationStart mode start) destination saved savedPC initialFits destinationFits destinationSeparate savedCurrent
  have middleEffect := StringInit.effect mode (StringCodec.destinationStart mode start) destination saved savedPC initialFits savedCurrent
  have fetched : StringForm.fetch mode (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved).principal.memory
      (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved).principal.pc.toNat =
        some (StringOperands.exchange mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)) := by
    rw [middleEffect,Arithmetic.encode_nat_toNat mode _ initialFits]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [StringOperands.exchange_encoding,StringCodec.exchange_length]
    exact savedExchange
  have lastTrace : Trace mode (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved)
      [StringOperands.exchange mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)]
      (execute mode (StringOperands.exchange mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start))
        (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved)) := .step fetched (.nil _)
  have combined := trace_append mode (trace_append mode firstTrace middleTrace) lastTrace
  simpa only [StringSetup.forms,run_append,run] using combined

/-- A single prefix window supplies all original packet windows above. -/
theorem initialized_trace (mode : Mode) (start source destination : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes))
    (sourceFits : source+mode.wordBytes < 2^(8*mode.wordBytes))
    (destinationFits : destination+mode.wordBytes < 2^(8*mode.wordBytes))
    (sourceSeparate : source+mode.wordBytes ≤ start ∨ start+StringCodec.initialSize mode ≤ source)
    (destinationSeparate : destination+mode.wordBytes ≤ StringCodec.destinationStart mode start ∨
      StringCodec.destinationStart mode start+StringCodec.initialSize mode ≤ destination)
    (current : ByteMemory.bytesAt state.principal.memory start (bytes mode start source destination).length = bytes mode start source destination) :
    Trace mode state (StringSetup.forms mode start source destination) (run mode (StringSetup.forms mode start source destination) state) := by
  let a := StringInit.bytes mode start source
  let b := StringCodec.exchangeBytes mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)
  let c := StringInit.bytes mode (StringCodec.destinationStart mode start) destination
  let d := StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)
  have original : ByteMemory.bytesAt state.principal.memory start (a++b++c++d).length = a++b++c++d := current
  have first := StringWindow.packet_window state.principal.memory start [] a (b++c++d)
    (by simpa only [List.nil_append,List.append_assoc] using original)
  have second := StringWindow.packet_window state.principal.memory start a b (c++d) (by simpa only [List.append_assoc] using original)
  have third := StringWindow.packet_window state.principal.memory start (a++b) c d original
  have last := StringWindow.packet_window state.principal.memory start (a++b++c) d [] (by simpa only [List.append_nil] using original)
  simp only [a,b,c,d,List.length_nil,Nat.add_zero,StringInit.bytes,StringCodec.initial_length,List.length_append,StringCodec.exchange_length] at first second third last
  have thirdPC : start+(StringCodec.initialSize mode+StringCodec.exchangeSize mode) = StringCodec.destinationStart mode start := by unfold StringCodec.destinationStart; omega
  have lastPC : start+(StringCodec.initialSize mode+StringCodec.exchangeSize mode+StringCodec.initialSize mode) = StringCodec.destinationStart mode start+StringCodec.initialSize mode := by unfold StringCodec.destinationStart; omega
  change ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = a at first
  change ByteMemory.bytesAt state.principal.memory (start+StringCodec.initialSize mode) (StringCodec.exchangeSize mode) = b at second
  change ByteMemory.bytesAt state.principal.memory (start+(StringCodec.initialSize mode+StringCodec.exchangeSize mode)) (StringCodec.initialSize mode) = c at third
  change ByteMemory.bytesAt state.principal.memory (start+(StringCodec.initialSize mode+StringCodec.exchangeSize mode+StringCodec.initialSize mode)) (StringCodec.exchangeSize mode) = d at last
  rw [thirdPC] at third
  rw [lastPC] at last
  exact trace mode start source destination state location fits sourceFits destinationFits sourceSeparate destinationSeparate first second third last

end SmcTuring.Native.StringSetupTrace
