module
public import SmcTuring.Native.ReadInvocationBounds
public import SmcTuring.Native.ScalarBounds
public import SmcTuring.Native.ReadScalarImage

public section

namespace SmcTuring.Native.ReadScalarBounds

open Execution MemoryRegion RegionExecution ReadScalarImage

/-- The complete read round trip followed by a scalar is safe from initial
pointer and static interval bounds; no intermediate readiness is assumed. -/
theorem safe_run (mode : Mode) (region : Region) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode)
    (ready : Ready mode op layout state)
    (callerCode : region.Contains layout.reader.caller (CallsImage.totalSize mode (.relative layout.reader.callee) + 15))
    (calleeCode : region.Contains layout.reader.callee (ReadCalleeImage.totalSize mode + 15))
    (scalarCode : region.Contains (scalarStart mode layout) 15)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.reader.callee)).toNat mode.wordBytes)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    SafeRun mode region (program mode op layout state) state := by
  have readSafe := ReadInvocationBounds.safe_run mode region layout.reader state ready.readReady callerCode calleeCode top slot pointer
  have scalarSafe := ScalarBounds.safe_run mode region op (scalarLayout mode layout) (afterRead mode layout state)
    (scalar_ready mode op layout state ready) scalarCode target
  apply WindowBounds.safe_run_append mode region _ _ state readSafe
  exact scalarSafe

theorem loaded (mode : Mode) (region : Region) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode)
    (ready : Ready mode op layout state)
    (callerCode : region.Contains layout.reader.caller (CallsImage.totalSize mode (.relative layout.reader.callee) + 15))
    (calleeCode : region.Contains layout.reader.callee (ReadCalleeImage.totalSize mode + 15))
    (scalarCode : region.Contains (scalarStart mode layout) 15)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.reader.callee)).toNat mode.wordBytes)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode op layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode op layout state) :=
  LoadedExecution.trace_complete mode region (ReadScalarImage.trace mode op layout state ready)
    (safe_run mode region op layout state ready callerCode calleeCode scalarCode top slot pointer target)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ReadScalarBounds
