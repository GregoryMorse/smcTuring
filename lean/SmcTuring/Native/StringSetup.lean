module
public import SmcTuring.Native.StringInitTrace

public section
namespace SmcTuring.Native.StringSetup
open StringExecution

@[expose] def sourceForms (mode : Mode) (start source : Nat) : List (StringForm.Form mode) :=
  StringInit.forms mode start source++[StringOperands.exchange mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)]
@[expose] def forms (mode : Mode) (start source destination : Nat) : List (StringForm.Form mode) :=
  sourceForms mode start source++StringInit.forms mode (StringCodec.destinationStart mode start) destination++
    [StringOperands.exchange mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)]

theorem cursor_range (mode : Mode) (start : Nat) :
    mode = .x64 -> Relocation.SignedDelta (start+StringCodec.initialSize mode+StringCodec.exchangeSize mode) (StringInit.field mode start) := by
  intro long
  subst mode
  change Relocation.SignedDelta (start+27+7) (start+19)
  unfold Relocation.SignedDelta Relocation.delta
  constructor <;> omega

theorem source_field_fits (mode : Mode) (start : Nat)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes)) :
    StringCodec.sourceField mode start < 2^(8*mode.wordBytes) := by
  cases mode <;> simp [StringCodec.bodyStart,StringCodec.initialSize,StringCodec.exchangeSize,StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at * <;> omega

theorem destination_field_fits (mode : Mode) (start : Nat)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes)) :
    StringCodec.destinationField mode start < 2^(8*mode.wordBytes) := by
  cases mode <;> simp [StringCodec.bodyStart,StringCodec.initialSize,StringCodec.exchangeSize,StringCodec.destinationField,StringCodec.destinationStart,StringCodec.fieldOffset,Mode.wordBytes] at * <;> omega

theorem initializer_fits (mode : Mode) (start : Nat)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes)) :
    start+StringCodec.initialSize mode < 2^(8*mode.wordBytes) ∧
    StringCodec.destinationStart mode start+StringCodec.initialSize mode < 2^(8*mode.wordBytes) := by
  unfold StringCodec.bodyStart StringCodec.destinationStart at *
  constructor <;> omega

theorem source_effect (mode : Mode) (start source : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = StringInit.bytes mode start source) :
    run mode (sourceForms mode start source) state = { state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (StringCodec.destinationStart mode start)
        accumulator := StringInit.accumulator mode source state
        memory := ByteMemory.putWord mode state.principal.memory (StringCodec.sourceField mode start) state.sourceIndex}
      sourceIndex := Arithmetic.encodeNat mode source} := by
  have initialFits := (initializer_fits mode start fits).1
  have initial := StringInit.effect mode start source state location initialFits current
  have pointer := StringInit.initialized_pointer mode start source state.principal.memory initialFits current
  have initialPC : (run mode (StringInit.forms mode start source) state).principal.pc = Arithmetic.encodeNat mode (start+StringCodec.initialSize mode) := by rw [initial]
  unfold sourceForms
  rw [run_append]
  change execute mode (StringOperands.exchange mode false (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start))
    (run mode (StringInit.forms mode start source) state) = _
  change Execution.load mode state.principal.memory (Arithmetic.encodeNat mode (StringCodec.sourceField mode start)) = Arithmetic.encodeNat mode source at pointer
  rw [StringOperands.source_effect mode (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start) _ initialPC (cursor_range mode start) (source_field_fits mode start fits),initial,pointer]
  rfl

/-- Saving SI cannot reach the second initializer, including any live address
or immediate byte. This derives its current packet window from original memory. -/
theorem destination_window (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) (si : Word mode) :
    ByteMemory.bytesAt (ByteMemory.putWord mode memory (StringCodec.sourceField mode start) si)
      (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) =
      ByteMemory.bytesAt memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) := by
  unfold ByteMemory.putWord
  apply ByteMemory.bytes_at_frame
  intro index
  have endField := StringCodec.field_end mode start
  have small := index.isLt
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  unfold StringCodec.destinationStart
  omega

/-- Complete literal initializer/exchange setup: both intended pointers are
loaded, full old SI/DI values are saved in their declared cursor fields and all
other memory is retained. The actual x64 AX result is the original destination
word; no accumulator preservation is inferred from restoring SI/DI. -/
theorem effect (mode : Mode) (start source destination : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start < 2^(8*mode.wordBytes))
    (destinationFits : destination < 2^(8*mode.wordBytes))
    (destinationSeparate : ∀ index : Fin mode.wordBytes,
      ¬ByteMemory.Inside (StringCodec.sourceField mode start) mode.wordBytes (destination+index.val))
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = StringInit.bytes mode start source)
    (destinationCurrent : ByteMemory.bytesAt state.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) =
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination) :
    run mode (forms mode start source destination) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (StringCodec.bodyStart mode start)
        accumulator := StringInit.accumulator mode destination state
        memory := ByteMemory.putWord mode (ByteMemory.putWord mode state.principal.memory (StringCodec.sourceField mode start) state.sourceIndex)
          (StringCodec.destinationField mode start) state.destinationIndex}
      sourceIndex := Arithmetic.encodeNat mode source
      destinationIndex := Arithmetic.encodeNat mode destination} := by
  let saved := run mode (sourceForms mode start source) state
  have savedEffect := source_effect mode start source state location fits sourceCurrent
  have savedPC : saved.principal.pc = Arithmetic.encodeNat mode (StringCodec.destinationStart mode start) := by rw [show saved = run mode (sourceForms mode start source) state from rfl,savedEffect]
  have savedCurrent : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode) =
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination := by
    rw [show saved = run mode (sourceForms mode start source) state from rfl,savedEffect,destination_window,destinationCurrent]
  have initialFits := (initializer_fits mode start fits).2
  have initialized := StringInit.effect mode (StringCodec.destinationStart mode start) destination saved savedPC initialFits savedCurrent
  have pointer := StringInit.initialized_pointer mode (StringCodec.destinationStart mode start) destination saved.principal.memory initialFits savedCurrent
  have initializedPC : (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved).principal.pc =
      Arithmetic.encodeNat mode (StringCodec.destinationStart mode start+StringCodec.initialSize mode) := by rw [initialized]
  have ax : StringInit.accumulator mode destination saved = StringInit.accumulator mode destination state := by
    rw [show saved = run mode (sourceForms mode start source) state from rfl,savedEffect]
    cases mode with
    | x86 => rfl
    | x64 => exact StringWindow.load_frame .x64 state.principal.memory (StringCodec.sourceField .x64 start) destination state.sourceIndex destinationFits destinationSeparate
  unfold forms
  rw [run_append,run_append]
  change execute mode (StringOperands.exchange mode true (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start))
    (run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved) = _
  change Execution.load mode saved.principal.memory (Arithmetic.encodeNat mode (StringCodec.destinationField mode start)) = Arithmetic.encodeNat mode destination at pointer
  rw [StringOperands.destination_effect mode (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start) _ initializedPC (cursor_range mode (StringCodec.destinationStart mode start))
    (destination_field_fits mode start fits),initialized,pointer,ax]
  rw [show saved = run mode (sourceForms mode start source) state from rfl,savedEffect]
  rw [StringCodec.body_coordinate]

end SmcTuring.Native.StringSetup
