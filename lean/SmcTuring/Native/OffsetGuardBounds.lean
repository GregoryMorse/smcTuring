module
public import SmcTuring.Native.SourceAccess

public section

namespace SmcTuring.Native.OffsetGuardBounds

open Execution MemoryRegion RegionExecution OffsetGuardImage

/-- Even a rejected source offset never produces an unbounded dereference:
its read is a contained register word and the entire tag guard is contained. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.guard.setup.origin layout.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.guard)
    (data : SourceAccess.DataWithin mode region layout.guard.setup.gridBase layout.cells) :
    SafeRun mode region (program mode layout state) state := by
  have pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.readerCallee)).toNat mode.wordBytes := by
    rw [ready.sourcePointer]; exact data.registers layout.offset
  have first := PlacedBounds.read_scalar_safe mode region .store (readLayout mode layout) state ready.readSetup
    code fields.top fields.slot pointer fields.candidate
  have second := SourceAccess.invocation_safe mode region (guardLayout mode layout) (afterRead mode layout state)
    (guard_ready mode layout state ready) code fields
  exact PlacedBounds.safe_trace_append mode region (ReadScalarImage.trace mode .store (readLayout mode layout) state ready.readSetup) first second

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.guard.setup.origin layout.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.guard)
    (data : SourceAccess.DataWithin mode region layout.guard.setup.gridBase layout.cells) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (OffsetGuardImage.trace mode layout state ready)
    (safe_run mode region layout state ready code fields data) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.OffsetGuardBounds
