module
public import SmcTuring.Native.PlacedBounds
public import SmcTuring.Native.GuardSetupImage

public section

namespace SmcTuring.Native.GuardSetupBounds

open Execution MemoryRegion RegionExecution GuardSetupImage

/-- Capture/restoration and the two metadata reads preserve their bounded
initial pointers despite the intervening resume, scratch and return writes. -/
theorem safe_run (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.boundary).toNat mode.wordBytes) :
    SafeRun mode region (program mode layout state) state := by
  have captureCode := PlacedBounds.snippet_window mode region _ _ _ _ code (by simp [ReaderImage.packets]) ready.captureWithin
  rw [ReaderImage.packet_size] at captureCode
  have capturePointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.start)).toNat mode.wordBytes := by
    rw [ready.capturePointer]; exact slot
  have captureSafe := ReaderBounds.safe_run mode region layout.start state ready.location ready.captureFits captureCode capturePointer
  have resumeSafe := PlacedBounds.scalar_safe mode region .store (resumeLayout mode layout) (captured mode layout state)
    (resume_ready mode layout state ready) code resume
  have candidatePointer : region.Contains (load mode (resumed mode layout state).memory (ReaderImage.label mode layout.candidateCallee)).toNat mode.wordBytes := by
    rw [resumed_load_frame mode layout state ready (ReaderImage.label mode layout.candidateCallee)
      (ReadInvocationImage.label_owned mode (candidateLayout mode layout) _ ready.candidateSetup) ready.resumeNotCandidateLabel,
      ready.candidatePointer]
    exact candidate
  have candidateSafe := PlacedBounds.reader_invocation_safe mode region (candidateLayout mode layout) (resumed mode layout state)
    (candidate_ready mode layout state ready) code top slot candidatePointer
  have scratchSafe := PlacedBounds.scalar_safe mode region .store (scratchLayout mode layout) (candidateRead mode layout state)
    (scratch_ready mode layout state ready) code scratch
  have boundaryPointer : region.Contains (load mode (scratched mode layout state).memory (ReaderImage.label mode layout.boundaryCallee)).toNat mode.wordBytes := by
    rw [scratched_load_frame mode layout state ready (ReaderImage.label mode layout.boundaryCallee)
      (ReadInvocationImage.label_owned mode (boundaryLayout mode layout) _ ready.boundarySetup)
      ready.resumeNotBoundaryLabel ready.boundarySetup.labelDifferent ready.scratchNotBoundaryLabel, ready.boundaryPointer]
    exact boundary
  have boundarySafe := PlacedBounds.reader_invocation_safe mode region (boundaryLayout mode layout) (scratched mode layout state)
    (boundary_ready mode layout state ready) code top slot boundaryPointer
  have captureTrace := capture_trace mode layout state ready
  have resumeTrace := ScalarImage.trace mode .store (resumeLayout mode layout) (captured mode layout state) (resume_ready mode layout state ready)
  have candidateTrace := ReadInvocationImage.trace mode (candidateLayout mode layout) (resumed mode layout state) (candidate_ready mode layout state ready)
  have scratchTrace := ScalarImage.trace mode .store (scratchLayout mode layout) (candidateRead mode layout state) (scratch_ready mode layout state ready)
  have prefix1 := Fetch.trace_append mode captureTrace resumeTrace
  have prefix2 := Fetch.trace_append mode prefix1 candidateTrace
  have prefix3 := Fetch.trace_append mode prefix2 scratchTrace
  exact PlacedBounds.safe_trace_append mode region prefix3
    (PlacedBounds.safe_trace_append mode region prefix2
      (PlacedBounds.safe_trace_append mode region prefix1
        (PlacedBounds.safe_trace_append mode region captureTrace captureSafe resumeSafe) candidateSafe) scratchSafe) boundarySafe

theorem loaded (mode : Mode) (region : Region) (layout : Layout mode) (state : State mode)
    (ready : Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (resume : region.Contains (Arithmetic.encodeNat mode layout.resume).toNat mode.wordBytes)
    (scratch : region.Contains (Arithmetic.encodeNat mode layout.scratch).toNat mode.wordBytes)
    (candidate : region.Contains (Arithmetic.encodeNat mode layout.candidate).toNat mode.wordBytes)
    (boundary : region.Contains (Arithmetic.encodeNat mode layout.boundary).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode layout state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode layout state) :=
  LoadedExecution.trace_complete mode region (GuardSetupImage.trace mode layout state ready)
    (safe_run mode region layout state ready code top slot resume scratch candidate boundary) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.GuardSetupBounds
