module
public import SmcTuring.Native.SourceAccess

public section

namespace SmcTuring.Native.ImmediateBounds

open Execution MemoryRegion RegionExecution ImmediateImage

/-- The literal immediate MOV reads its contained code-owned constant word
and writes exactly its contained logical register destination. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.unit.reader.origin layout.unit.reader.whole)
    (data : SourceAccess.DataWithin mode region layout.unit.reader.gridBase layout.cells)
    (top : region.Contains (Arithmetic.encodeNat mode layout.unit.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.unit.reader.slot).toNat mode.wordBytes)
    (constant : region.Contains (Arithmetic.encodeNat mode layout.constant).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.unit.reader.callee)).toNat mode.wordBytes := by
    rw [ready.points]; exact constant
  have target : region.Contains (Arithmetic.encodeNat mode layout.unit.target).toNat mode.wordBytes := by
    rw [ready.target]; exact data.registers layout.destination
  exact PlacedBounds.read_scalar_safe mode region .store layout.unit state ready.unit code top slot pointer target

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.unit.reader.origin layout.unit.reader.whole)
    (data : SourceAccess.DataWithin mode region layout.unit.reader.gridBase layout.cells)
    (top : region.Contains (Arithmetic.encodeNat mode layout.unit.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.unit.reader.slot).toNat mode.wordBytes)
    (constant : region.Contains (Arithmetic.encodeNat mode layout.constant).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (ReadScalarImage.trace mode .store layout.unit state ready.unit)
    (safe_run mode region layout state ready code data top slot constant) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ImmediateBounds
