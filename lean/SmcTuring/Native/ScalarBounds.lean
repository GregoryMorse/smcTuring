module
public import SmcTuring.Native.WindowBounds
public import SmcTuring.Native.ScalarImage
public import SmcTuring.Native.LoadedExecution

public section

namespace SmcTuring.Native.ScalarBounds

open Execution MemoryRegion RegionExecution ScalarImage

/-- Every selected scalar's data read and full word write use the same proved
relocated destination. Ordinary stores require no destination read. -/
theorem safe_run (mode : Mode) (region : Region) (op : Op) (layout : Layout mode) (state : State mode)
    (ready : Ready mode op layout state) (code : region.Contains layout.start 15)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    SafeRun mode region (program mode op layout) state := by
  have address := hits mode op layout state ready
  have instruction : Safe mode region (form mode op layout) state := by
    apply WindowBounds.safe mode region
    · rw [ready.location, Arithmetic.encode_nat_toNat mode layout.start (by have bound := ready.codeFits; omega)]
      exact code
    · cases mode <;> cases op <;> simp only [ReadWithin, readAddress, form, memoryOp]
      all_goals first | exact trivial | (simp only [form, memoryOp] at address; rw [address]; exact target)
    · rw [written_address mode op layout state ready]; exact target
  exact ⟨instruction, trivial⟩

/-- Fetch and execute the literal scalar packet in a finite loaded image. -/
theorem loaded (mode : Mode) (region : Region) (op : Op) (layout : Layout mode) (state : State mode)
    (ready : Ready mode op layout state) (code : region.Contains layout.start 15)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode op layout) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode op layout state) :=
  LoadedExecution.trace_complete mode region (ScalarImage.trace mode op layout state ready)
    (safe_run mode region op layout state ready code target) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ScalarBounds
