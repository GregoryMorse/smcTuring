module
public import SmcTuring.Native.PlacedBounds
public import SmcTuring.Native.StoreCalleeImage

public section

namespace SmcTuring.Native.StoreCalleeBounds

open Execution MemoryRegion RegionExecution StoreCalleeImage

/-- The mutable MOFFS store and code-backed return have bounded footprints.
The return-slot read is distinct from the contained dynamic store destination. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (target mode layout state).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have localMember : ReaderImage.lastEntry mode layout.body layout.initial ∈
      ControlPacking.place mode layout.body (ReaderImage.packets mode layout.body layout.initial) := by
    rw [ReaderImage.placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have member := ready.within _ (ReadCalleeImage.reader_within mode layout.body layout.top layout.slot layout.initial _ localMember)
  have codeEntry := PlacedBounds.entry_window mode region layout.origin layout.whole _ code member
  have entryFits : entryPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have bound := ready.bodyFits
    cases mode <;> simp only [entryPC, ReaderImage.prefixSize, ReadCalleeImage.totalSize, Mode.wordBytes] at * <;> omega
  have storeSafe : Safe mode region (.moffs (target mode layout state)) state := by
    apply WindowBounds.safe mode region
    · rw [ready.location, Arithmetic.encode_nat_toNat mode _ entryFits]; exact codeEntry
    · trivial
    · exact pointer
  have callSafe := PlacedBounds.calls_safe mode region layout.origin (ReadCalleeImage.callStart mode layout.body)
    layout.top layout.slot layout.whole (.indirect layout.slot) (stored mode layout state) (store_pc mode layout state ready)
    ready.ranges (ReadCalleeImage.call_fits mode layout.body layout.slot ready.bodyFits) (store_top mode layout state ready)
    (Fragment.within_trans mode _ _ _ (ReadCalleeImage.call_within mode layout.body layout.top layout.slot layout.initial) ready.within)
    code top slot slot
  have storeTrace : Fetch.Trace mode state [.moffs (target mode layout state)] (stored mode layout state) :=
    .step (store_fetch mode layout state ready) (.nil _)
  exact PlacedBounds.safe_trace_append mode region storeTrace ⟨storeSafe, trivial⟩ callSafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (target mode layout state).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (StoreCalleeImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.StoreCalleeBounds
