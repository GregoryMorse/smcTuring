module
public import SmcTuring.Native.AddressBounds

public section

namespace SmcTuring.Native.LoadBounds

open Execution MemoryRegion RegionExecution LoadImage

/-- A rejected address has only the bounded guard path. A successful load's
actual mutable operand points to the contained selected heap word, as derived
from representation and the existing finite-cell bounds. -/
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
    have heapPointer : region.Contains (load mode (afterAddress mode layout source state).memory
        (ReaderImage.label mode layout.address.pointerCallee)).toNat mode.wordBytes := by
      rw [afterAddress, AddressImage.pointer mode layout.address source state ready.addressSetup rep position valid]
      exact data.heap position (pointer_inside mode layout source bounds position valid)
    have readSafe := PlacedBounds.read_scalar_safe mode region .store (readLayout mode layout) (afterAddress mode layout source state)
      (read_ready mode layout source state ready bounds rep position valid) code fields.top fields.slot heapPointer (data.registers layout.destination)
    have addressTrace := AddressImage.trace mode layout.address source state ready.addressSetup rep
    simpa only [program, valid] using PlacedBounds.safe_trace_append mode region addressTrace addressSafe readSafe

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
  LoadedExecution.trace_complete mode region (LoadImage.trace mode layout source state ready bounds rep)
    (safe_run mode region layout source state ready bounds rep code fields data pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.LoadBounds
