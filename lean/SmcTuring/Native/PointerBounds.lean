module
public import SmcTuring.Native.SourceAccess

public section

namespace SmcTuring.Native.PointerBounds

open Execution MemoryRegion RegionExecution PointerImage

/-- Pointer construction reads two contained logical registers and then the
contained operand word itself. It never dereferences the computed value. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.reader.origin layout.reader.whole)
    (data : SourceAccess.DataWithin mode region layout.reader.gridBase layout.cells)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (pointer : region.Contains (Arithmetic.encodeNat mode layout.pointer).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.candidate).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have basePointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.reader.callee)).toNat mode.wordBytes := by
    rw [ready.basePointer]; exact data.registers layout.base
  have offsetPointer : region.Contains (load mode (afterBase mode layout state).memory (ReaderImage.label mode layout.offsetCallee)).toNat mode.wordBytes := by
    rw [base_load_frame mode layout state ready (ReaderImage.label mode layout.offsetCallee)
      (metadata_owned mode layout state ready .offsetReader) (ready.metadataDifferent .offsetReader .pointer)
      (ready.metadataDifferent .offsetReader .slot), ready.offsetPointer]
    exact data.registers layout.offset
  have wordPointer : region.Contains (load mode (afterOffset mode layout state).memory (ReaderImage.label mode layout.wordCallee)).toNat mode.wordBytes := by
    rw [offset_load_frame mode layout state ready (ReaderImage.label mode layout.wordCallee)
      (metadata_owned mode layout state ready .wordReader) (ready.metadataDifferent .wordReader .pointer)
      (ready.metadataDifferent .wordReader .slot), ready.wordPointer]
    exact pointer
  have first := PlacedBounds.read_scalar_safe mode region .store (baseLayout mode layout) state ready.baseSetup code top slot basePointer pointer
  have second := PlacedBounds.read_scalar_safe mode region .add (offsetLayout mode layout) (afterBase mode layout state)
    (offset_ready mode layout state ready) code top slot offsetPointer pointer
  have third := PlacedBounds.read_scalar_safe mode region .store (wordLayout mode layout) (afterOffset mode layout state)
    (word_ready mode layout state ready) code top slot wordPointer candidate
  have firstTrace := ReadScalarImage.trace mode .store (baseLayout mode layout) state ready.baseSetup
  have secondTrace := ReadScalarImage.trace mode .add (offsetLayout mode layout) (afterBase mode layout state) (offset_ready mode layout state ready)
  exact PlacedBounds.safe_trace_append mode region (Fetch.trace_append mode firstTrace secondTrace)
    (PlacedBounds.safe_trace_append mode region firstTrace first second) third

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.reader.origin layout.reader.whole)
    (data : SourceAccess.DataWithin mode region layout.reader.gridBase layout.cells)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (pointer : region.Contains (Arithmetic.encodeNat mode layout.pointer).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.candidate).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (PointerImage.trace mode layout state ready)
    (safe_run mode region layout state ready code data top slot pointer candidate) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.PointerBounds
