module
public import SmcTuring.Native.PlacedBounds
public import SmcTuring.Native.BorrowMaskImage

public section

namespace SmcTuring.Native.BorrowMaskBounds

open Execution MemoryRegion RegionExecution BorrowMaskImage

/-- Derive all thirteen SUB/read-zero/store/SBB access bounds from the initial
setup and full metadata words. The subtraction preserves the reader pointer. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state)
    (code : PlacedBounds.ControlWithin mode region layout.reader.origin layout.reader.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.scratch).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.zero).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have subSafe := PlacedBounds.scalar_safe mode region .subtract (subLayout mode layout) state ready.subReady code scratch
  have pointer : region.Contains (load mode (subtracted mode layout state).memory (ReaderImage.label mode layout.reader.callee)).toNat mode.wordBytes := by
    rw [sub_label mode layout state ready, ready.pointer]; exact zero
  have readSafe := PlacedBounds.reader_invocation_safe mode region layout.reader (subtracted mode layout state)
    (read_ready mode layout state ready) code top slot pointer
  have storeSafe := PlacedBounds.scalar_safe mode region .store (storeLayout mode layout) (afterRead mode layout state)
    (store_ready mode layout state ready) code mask
  have sbbSafe := PlacedBounds.scalar_safe mode region .subtractBorrowZero (sbbLayout mode layout) (maskStored mode layout state)
    (sbb_ready mode layout state ready) code mask
  have subTrace := ScalarImage.trace mode .subtract (subLayout mode layout) state ready.subReady
  have readTrace := ReadInvocationImage.trace mode layout.reader (subtracted mode layout state) (read_ready mode layout state ready)
  have storeTrace := ScalarImage.trace mode .store (storeLayout mode layout) (afterRead mode layout state) (store_ready mode layout state ready)
  exact PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode (Fetch.trace_append mode subTrace readTrace) storeTrace)
    (PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode subTrace readTrace)
      (PlacedBounds.safe_trace_append mode region subTrace subSafe readSafe) storeSafe) sbbSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state)
    (code : PlacedBounds.ControlWithin mode region layout.reader.origin layout.reader.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.scratch).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (zero : region.Contains (Arithmetic.encodeNat mode layout.zero).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (BorrowMaskImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot scratch mask zero) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.BorrowMaskBounds
