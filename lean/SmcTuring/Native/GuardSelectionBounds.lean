module
public import SmcTuring.Native.PlacedBounds
public import SmcTuring.Native.GuardSelectionImage

public section

namespace SmcTuring.Native.GuardSelectionBounds

open Execution MemoryRegion RegionExecution GuardSelectionImage

/-- All four read/update stages preserve the bounded metadata reader pointers.
The final indirect CALL reads the selected word before writing the return slot. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (continuation : region.Contains (Arithmetic.encodeNat mode layout.continuation).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.terminal).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.selected).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have pointer1 : region.Contains (load mode state.memory (ReaderImage.label mode layout.continuationCallee)).toNat mode.wordBytes := by
    rw [ready.continuationPointer]; exact continuation
  have pointer2 : region.Contains (load mode (first mode layout state).memory (ReaderImage.label mode layout.terminalCallee)).toNat mode.wordBytes := by
    rw [first_load_frame mode layout state ready (ReaderImage.label mode layout.terminalCallee)
      (ReadInvocationImage.label_owned mode (secondLayout mode layout).reader _ ready.secondSetup.readReady)
      ready.terminalLabelNotSelected ready.secondSetup.readReady.labelDifferent, ready.terminalPointer]
    exact terminal
  have pointer3 : region.Contains (load mode (second mode layout state).memory (ReaderImage.label mode layout.maskCallee)).toNat mode.wordBytes := by
    rw [second_load_frame mode layout state ready (ReaderImage.label mode layout.maskCallee)
      (ReadInvocationImage.label_owned mode (thirdLayout mode layout).reader _ ready.thirdSetup.readReady)
      ready.maskLabelNotSelected ready.thirdSetup.readReady.labelDifferent, ready.maskPointer]
    exact mask
  have pointer4 : region.Contains (load mode (third mode layout state).memory (ReaderImage.label mode layout.continuationCallee)).toNat mode.wordBytes := by
    rw [third_load_frame mode layout state ready (ReaderImage.label mode layout.continuationCallee)
      (ReadInvocationImage.label_owned mode (fourthLayout mode layout).reader _ ready.fourthSetup.readReady)
      ready.continuationLabelNotSelected ready.fourthSetup.readReady.labelDifferent, ready.continuationPointer]
    exact continuation
  have firstSafe := PlacedBounds.read_scalar_safe mode region .store (firstLayout mode layout) state ready.firstReady code top slot pointer1 selected
  have secondSafe := PlacedBounds.read_scalar_safe mode region .bitXor (secondLayout mode layout) (first mode layout state)
    (second_ready mode layout state ready) code top slot pointer2 selected
  have thirdSafe := PlacedBounds.read_scalar_safe mode region .bitAnd (thirdLayout mode layout) (second mode layout state)
    (third_ready mode layout state ready) code top slot pointer3 selected
  have fourthSafe := PlacedBounds.read_scalar_safe mode region .bitXor (fourthLayout mode layout) (third mode layout state)
    (fourth_ready mode layout state ready) code top slot pointer4 selected
  have callSafe := PlacedBounds.calls_safe mode region layout.origin (callStart mode layout) layout.top layout.slot layout.whole
    (.indirect layout.selected) (fourth mode layout state) (call_location mode layout state ready) ready.callRanges ready.callFits
    (call_top mode layout state ready) ready.callWithin code top slot selected
  have firstTrace := ReadScalarImage.trace mode .store (firstLayout mode layout) state ready.firstReady
  have secondTrace := ReadScalarImage.trace mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready)
  have thirdTrace := ReadScalarImage.trace mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready)
  have prefix1 := Fetch.trace_append mode firstTrace secondTrace
  have prefix2 := Fetch.trace_append mode prefix1 thirdTrace
  have beforeSafe := PlacedBounds.safe_trace_append mode region prefix2
    (PlacedBounds.safe_trace_append mode region prefix1
      (PlacedBounds.safe_trace_append mode region firstTrace firstSafe secondSafe) thirdSafe) fourthSafe
  exact PlacedBounds.safe_trace_append mode region (before_trace mode layout state ready) beforeSafe callSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (continuation : region.Contains (Arithmetic.encodeNat mode layout.continuation).toNat mode.wordBytes)
    (terminal : region.Contains (Arithmetic.encodeNat mode layout.terminal).toNat mode.wordBytes)
    (mask : region.Contains (Arithmetic.encodeNat mode layout.mask).toNat mode.wordBytes)
    (selected : region.Contains (Arithmetic.encodeNat mode layout.selected).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (GuardSelectionImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot continuation terminal mask selected) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.GuardSelectionBounds
