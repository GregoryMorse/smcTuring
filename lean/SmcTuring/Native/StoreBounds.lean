module
public import SmcTuring.Native.AddressBounds
public import SmcTuring.Native.StoreInvocationBounds

public section

namespace SmcTuring.Native.StoreBounds

open Execution MemoryRegion RegionExecution StoreImage

/-- The successful store reads a contained logical register; its actual final
MOFFS destination is the represented selected finite heap word. Rejected source
addresses stop after their bounded guard path, before any heap dereference. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (code : PlacedBounds.ControlWithin mode region layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.address.offset.guard)
    (data : SourceAccess.DataWithin mode region layout.address.offset.guard.setup.gridBase layout.address.offset.cells)
    (pointer : region.Contains (Arithmetic.encodeNat mode (AddressImage.pointerPosition mode layout.address)).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout source state) state := by
  have addressSafe := AddressBounds.safe_run mode region layout.address source state ready.addressSetup rep code fields data pointer
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa only [program, valid] using addressSafe
  | some position =>
    have sourcePointer : region.Contains (load mode (afterAddress mode layout source state).memory
        (ReaderImage.label mode layout.readerCallee)).toNat mode.wordBytes := by
      rw [source_label_frame mode layout source state ready rep, ready.sourcePointer]
      exact data.registers layout.source
    have readSafe := PlacedBounds.reader_invocation_safe mode region (readLayout mode layout) (afterAddress mode layout source state)
      (read_ready mode layout source state ready bounds rep position valid) code fields.top fields.slot sourcePointer
    have heapPointer : region.Contains (load mode (afterRead mode layout source state).memory
        (ReaderImage.label mode layout.address.pointerCallee)).toNat mode.wordBytes := by
      rw [pointer_after_read mode layout source state ready bounds rep position valid]
      exact data.heap position (pointer_inside mode layout source bounds position valid)
    have storeSafe := StoreInvocationBounds.safe_run mode region (storeLayout mode layout) (afterRead mode layout source state)
      (store_ready mode layout source state ready bounds rep position valid) code fields.top fields.slot heapPointer
    have addressTrace := AddressImage.trace mode layout.address source state ready.addressSetup rep
    have readTrace := ReadInvocationImage.trace mode (readLayout mode layout) (afterAddress mode layout source state)
      (read_ready mode layout source state ready bounds rep position valid)
    have allSafe := PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode addressTrace readTrace)
      (PlacedBounds.safe_trace_append mode region addressTrace addressSafe readSafe) storeSafe
    simpa only [program, valid, acceptedProgram] using allSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (code : PlacedBounds.ControlWithin mode region layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.whole)
    (fields : SourceAccess.GuardFields mode region layout.address.offset.guard)
    (data : SourceAccess.DataWithin mode region layout.address.offset.guard.setup.gridBase layout.address.offset.cells)
    (pointer : region.Contains (Arithmetic.encodeNat mode (AddressImage.pointerPosition mode layout.address)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout source state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout source state) :=
  LoadedExecution.trace_complete mode region (StoreImage.trace mode layout source state ready bounds rep)
    (safe_run mode region layout source state ready bounds rep code fields data pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.StoreBounds
