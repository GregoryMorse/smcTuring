module
public import SmcTuring.Native.GuardBounds
public import SmcTuring.Native.GuardInvocationImage

public section

namespace SmcTuring.Native.GuardInvocationBounds

open Execution MemoryRegion RegionExecution GuardInvocationImage

/-- The outer caller's actual push preserves the guard setup. Every access of
the complete eighty-nine-instruction invocation is bounded by static intervals. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.guard.setup.origin layout.guard.setup.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.boundary).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.guard.zero).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.guard.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.guard.selected).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.guard.terminal).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have callerSafe := PlacedBounds.calls_safe mode region layout.guard.setup.origin layout.caller layout.guard.setup.top
    layout.guard.setup.slot layout.guard.setup.whole (.relative layout.guard.setup.start) state ready.location ready.callerRanges ready.callerFits
    ready.bodySetup.setupReady.candidateSetup.topValue ready.callerWithin code top slot trivial
  have bodySafe := GuardBounds.safe_run mode region layout.guard (afterCaller mode layout state) (body_ready mode layout state ready)
    code top slot resume scratch candidate boundary zero mask selected terminal
  exact PlacedBounds.safe_trace_append mode region (caller_trace mode layout state ready) callerSafe bodySafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.guard.setup.origin layout.guard.setup.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.guard.setup.boundary).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.guard.zero).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.guard.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.guard.selected).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.guard.terminal).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (GuardInvocationImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot resume scratch candidate boundary zero mask selected terminal)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.GuardInvocationBounds
