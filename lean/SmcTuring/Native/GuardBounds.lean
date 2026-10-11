module
public import SmcTuring.Native.GuardSetupBounds
public import SmcTuring.Native.BorrowMaskBounds
public import SmcTuring.Native.GuardSelectionBounds
public import SmcTuring.Native.GuardImage

public section

namespace SmcTuring.Native.GuardBounds

open Execution MemoryRegion RegionExecution GuardImage

/-- Compose every access of the complete guard, including both continuation
orientations. All stage readiness and pointer values come from the initial Ready. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.setup.origin layout.setup.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.setup.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.setup.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.setup.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.setup.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.setup.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.setup.boundary).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.zero).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.selected).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.terminal).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have setupSafe := GuardSetupBounds.safe_run mode region layout.setup state ready.setupReady code top slot resume scratch candidate boundary
  have borrowSafe := BorrowMaskBounds.safe_run mode region (borrowLayout mode layout) (afterSetup mode layout state)
    (borrow_ready mode layout state ready) code top slot scratch mask zero
  have continuation : region.Contains (Arithmetic.encodeNat mode (continuationField layout)).toNat mode.wordBytes := by
    cases sense : layout.sense <;> simp only [continuationField, sense]
    · exact resume
    · exact terminal
  have alternative : region.Contains (Arithmetic.encodeNat mode (terminalField layout)).toNat mode.wordBytes := by
    cases sense : layout.sense <;> simp only [terminalField, sense]
    · exact terminal
    · exact resume
  have selectionSafe := GuardSelectionBounds.safe_run mode region (selectionLayout mode layout) (afterBorrow mode layout state)
    (selection_ready mode layout state ready) code top slot continuation alternative mask selected
  have setupTrace := GuardSetupImage.trace mode layout.setup state ready.setupReady
  have borrowTrace := BorrowMaskImage.trace mode (borrowLayout mode layout) (afterSetup mode layout state) (borrow_ready mode layout state ready)
  exact PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode setupTrace borrowTrace)
    (PlacedBounds.safe_trace_append mode region setupTrace setupSafe borrowSafe) selectionSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.setup.origin layout.setup.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.setup.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.setup.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.setup.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.setup.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.setup.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.setup.boundary).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.zero).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.selected).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.terminal).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (GuardImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot resume scratch candidate boundary zero mask selected terminal)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.GuardBounds
