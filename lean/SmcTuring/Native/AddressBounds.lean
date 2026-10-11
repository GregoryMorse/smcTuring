module
public import SmcTuring.Native.OffsetGuardBounds
public import SmcTuring.Native.PointerBounds

public section

namespace SmcTuring.Native.AddressBounds

open Execution MemoryRegion RegionExecution AddressImage

/-- The malformed-offset path stops after the first contained guard. For a
Boolean offset, pointer construction and the complete base guard remain bounded,
even when the base is rejected. No computed pointer is dereferenced here. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state)
    (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (code : PlacedBounds.ControlWithin mode region layout.offset.guard.setup.origin layout.offset.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.offset.guard)
    (data : SourceAccess.DataWithin mode region layout.offset.guard.setup.gridBase layout.offset.cells)
    (pointer : region.Contains (Arithmetic.encodeNat mode (pointerPosition mode layout)).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout source state) state := by
  have first := OffsetGuardBounds.safe_run mode region layout.offset state ready.offsetSetup code fields data
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [program, offset, SourceValues.isOffset] using first
  | offset choice =>
    have pointerReady := pointer_ready mode layout source state ready rep choice offset
    have second := PointerBounds.safe_run mode region (pointerLayout mode layout) (afterOffset mode layout state)
      pointerReady code data fields.top fields.slot pointer fields.candidate
    have baseFields : SourceAccess.GuardFields mode region (baseGuard mode layout) :=
      ⟨fields.top, fields.slot, fields.resume, fields.scratch, fields.candidate, fields.boundary,
        fields.zero, fields.mask, fields.selected, fields.terminal⟩
    have third := SourceAccess.invocation_safe mode region (guardLayout mode layout) (afterPointer mode layout state)
      (guard_ready mode layout source state ready rep choice offset) code baseFields
    have firstTrace := OffsetGuardImage.trace mode layout.offset state ready.offsetSetup
    have secondTrace := PointerImage.trace mode (pointerLayout mode layout) (afterOffset mode layout state) pointerReady
    have allSafe := PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode firstTrace secondTrace)
      (PlacedBounds.safe_trace_append mode region firstTrace first second) third
    simpa [program, offset, SourceValues.isOffset, acceptedProgram] using allSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state)
    (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (code : PlacedBounds.ControlWithin mode region layout.offset.guard.setup.origin layout.offset.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.offset.guard)
    (data : SourceAccess.DataWithin mode region layout.offset.guard.setup.gridBase layout.offset.cells)
    (pointer : region.Contains (Arithmetic.encodeNat mode (pointerPosition mode layout)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout source state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout source state) :=
  LoadedExecution.trace_complete mode region (AddressImage.trace mode layout source state ready rep)
    (safe_run mode region layout source state ready rep code fields data pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.AddressBounds
