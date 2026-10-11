module
public import SmcTuring.Native.StoreCalleeBounds
public import SmcTuring.Native.StoreInvocationImage

public section

namespace SmcTuring.Native.StoreInvocationBounds

open Execution MemoryRegion RegionExecution StoreInvocationImage

/-- The actual caller push preserves the bounded dynamic operand; the store
callee and return therefore inherit its complete-word destination bound. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.body)).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have callerSafe := PlacedBounds.calls_safe mode region layout.origin layout.caller layout.top layout.slot layout.whole
    (.relative (entryPC mode layout)) state ready.location ready.callerRanges ready.callerFits ready.topValue ready.callerWithin code top slot trivial
  have laterPointer : region.Contains
      (StoreCalleeImage.target mode (calleeLayout mode layout) (afterCaller mode layout state)).toNat mode.wordBytes := by
    change region.Contains (load mode (afterCaller mode layout state).memory (ReaderImage.label mode layout.body)).toNat mode.wordBytes
    rw [caller_label mode layout state ready]; exact pointer
  have calleeSafe := StoreCalleeBounds.safe_run mode region (calleeLayout mode layout) (afterCaller mode layout state)
    (callee_ready mode layout state ready) code top slot laterPointer
  exact PlacedBounds.safe_trace_append mode region (caller_trace mode layout state ready) callerSafe calleeSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.body)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (StoreInvocationImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.StoreInvocationBounds
