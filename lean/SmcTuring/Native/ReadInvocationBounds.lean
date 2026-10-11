module
public import SmcTuring.Native.ReadCalleeBounds
public import SmcTuring.Native.ReadInvocationImage

public section

namespace SmcTuring.Native.ReadInvocationBounds

open Execution MemoryRegion RegionExecution ReadInvocationImage

/-- The actual caller push preserves the original bounded reader pointer and
StackTop; both later callee bounds follow from those proved frames. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state)
    (callerCode : region.Contains layout.caller (CallsImage.totalSize mode (.relative layout.callee) + 15))
    (calleeCode : region.Contains layout.callee (ReadCalleeImage.totalSize mode + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.callee)).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have callerSafe := CallsBounds.safe_run mode region layout.caller layout.top layout.slot (.relative layout.callee)
    state ready.location ready.callerRanges ready.callerFits ready.topValue callerCode topInside slotInside trivial
  have pointerLater : region.Contains (load mode (afterCaller mode layout state).memory
      (ReaderImage.label mode layout.callee)).toNat mode.wordBytes := by
    rw [caller_label mode layout state ready]; exact pointer
  have calleeSafe := ReadCalleeBounds.safe_run mode region layout.callee layout.top layout.slot (afterCaller mode layout state)
    (caller_pc mode layout state ready) ready.calleeRanges ready.calleeFits (caller_top mode layout state ready)
    calleeCode topInside slotInside pointerLater
  apply WindowBounds.safe_run_append mode region _ _ state callerSafe
  exact calleeSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state)
    (callerCode : region.Contains layout.caller (CallsImage.totalSize mode (.relative layout.callee) + 15))
    (calleeCode : region.Contains layout.callee (ReadCalleeImage.totalSize mode + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.callee)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (ReadInvocationImage.trace mode layout state ready)
    (safe_run mode region layout state ready callerCode calleeCode topInside slotInside pointer)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ReadInvocationBounds
