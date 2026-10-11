module
public import SmcTuring.Native.BorrowMaskImage

public section

namespace SmcTuring.Native.GuardSetupImage

open Execution ControlImage

/-- One shared placement context for the guard's inline capture, two fixed
stores, and two complete reader invocations. Caller locations are computed. -/
structure Layout (mode : Mode) where
  start : Nat
  candidateCallee : Nat
  boundaryCallee : Nat
  top : Nat
  slot : Nat
  resume : Nat
  scratch : Nat
  candidate : Nat
  boundary : Nat
  origin : Nat
  gridBase : Nat
  whole : List (SpacedPacking.Piece mode)
  captureInitial : Word mode
  candidateInitial : Word mode
  boundaryInitial : Word mode

@[expose] def resumeStart (mode : Mode) (layout : Layout mode) : Nat := layout.start + ReaderImage.totalSize mode
@[expose] def candidateStart (mode : Mode) (layout : Layout mode) : Nat := resumeStart mode layout + ScalarImage.size mode .store
@[expose] def scratchStart (mode : Mode) (layout : Layout mode) : Nat :=
  candidateStart mode layout + CallsImage.totalSize mode (.relative layout.candidateCallee)
@[expose] def boundaryStart (mode : Mode) (layout : Layout mode) : Nat := scratchStart mode layout + ScalarImage.size mode .store
@[expose] def endPosition (mode : Mode) (layout : Layout mode) : Nat :=
  boundaryStart mode layout + CallsImage.totalSize mode (.relative layout.boundaryCallee)

@[expose] def resumeLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨resumeStart mode layout, layout.resume, layout.origin, layout.gridBase, layout.whole⟩
@[expose] def scratchLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨scratchStart mode layout, layout.scratch, layout.origin, layout.gridBase, layout.whole⟩
@[expose] def candidateLayout (mode : Mode) (layout : Layout mode) : ReadInvocationImage.Layout mode :=
  ⟨candidateStart mode layout, layout.candidateCallee, layout.top, layout.slot,
    layout.origin, layout.gridBase, layout.candidateInitial, layout.whole⟩
@[expose] def boundaryLayout (mode : Mode) (layout : Layout mode) : ReadInvocationImage.Layout mode :=
  ⟨boundaryStart mode layout, layout.boundaryCallee, layout.top, layout.slot,
    layout.origin, layout.gridBase, layout.boundaryInitial, layout.whole⟩

/-- A proof-only initial-memory view used to state static placement setup. -/
@[expose] def viewAt (mode : Mode) (state : State mode) (position : Nat) : State mode :=
  { state with pc := Arithmetic.encodeNat mode position }
@[expose] def captured (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Reader.finish mode state (ReaderImage.label mode layout.start) (ReaderImage.firstDisp mode layout.start) (ReaderImage.secondDisp mode)
@[expose] def resumed (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode .store (resumeLayout mode layout) (captured mode layout state)
@[expose] def candidateRead (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadInvocationImage.finish mode (candidateLayout mode layout) (resumed mode layout state)
@[expose] def scratched (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode .store (scratchLayout mode layout) (candidateRead mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadInvocationImage.finish mode (boundaryLayout mode layout) (scratched mode layout state)

@[expose] def captureProgram (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  [.memory .exchangeAcc (ReaderImage.firstDisp mode layout.start),
    Reader.storeForm mode (ReaderImage.label mode layout.start) (ReaderImage.secondDisp mode),
    .exchangeIndirect, .moffs (load mode state.memory (ReaderImage.label mode layout.start))]
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  captureProgram mode layout state ++ ScalarImage.program mode .store (resumeLayout mode layout) ++
    ReadInvocationImage.program mode (candidateLayout mode layout) (resumed mode layout state) ++
    ScalarImage.program mode .store (scratchLayout mode layout) ++
    ReadInvocationImage.program mode (boundaryLayout mode layout) (scratched mode layout state)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode layout.start
  captureFits : layout.start + ReaderImage.totalSize mode < 2 ^ (8 * mode.wordBytes)
  captureWithin : Fragment.Within mode
    (ControlPacking.place mode layout.start (ReaderImage.packets mode layout.start layout.captureInitial))
    (SpacedPacking.place mode layout.origin layout.whole)
  capturePointer : load mode state.memory (ReaderImage.label mode layout.start) = Arithmetic.encodeNat mode layout.slot
  resumeSetup : ScalarImage.Ready mode .store (resumeLayout mode layout) (viewAt mode state (resumeStart mode layout))
  candidateSetup : ReadInvocationImage.Ready mode (candidateLayout mode layout) (viewAt mode state (candidateStart mode layout))
  scratchSetup : ScalarImage.Ready mode .store (scratchLayout mode layout) (viewAt mode state (scratchStart mode layout))
  boundarySetup : ReadInvocationImage.Ready mode (boundaryLayout mode layout) (viewAt mode state (boundaryStart mode layout))
  candidatePointer : load mode state.memory (ReaderImage.label mode layout.candidateCallee) = Arithmetic.encodeNat mode layout.candidate
  boundaryPointer : load mode state.memory (ReaderImage.label mode layout.boundaryCallee) = Arithmetic.encodeNat mode layout.boundary
  candidateNotSlot : Not (Arithmetic.encodeNat mode layout.candidate = Arithmetic.encodeNat mode layout.slot)
  boundaryNotSlot : Not (Arithmetic.encodeNat mode layout.boundary = Arithmetic.encodeNat mode layout.slot)
  resumeNotTop : Not (Arithmetic.encodeNat mode layout.top = Arithmetic.encodeNat mode layout.resume)
  resumeNotCandidateLabel : Not (ReaderImage.label mode layout.candidateCallee = Arithmetic.encodeNat mode layout.resume)
  resumeNotCandidate : Not (Arithmetic.encodeNat mode layout.candidate = Arithmetic.encodeNat mode layout.resume)
  resumeNotBoundaryLabel : Not (ReaderImage.label mode layout.boundaryCallee = Arithmetic.encodeNat mode layout.resume)
  resumeNotBoundary : Not (Arithmetic.encodeNat mode layout.boundary = Arithmetic.encodeNat mode layout.resume)
  scratchNotTop : Not (Arithmetic.encodeNat mode layout.top = Arithmetic.encodeNat mode layout.scratch)
  scratchNotBoundaryLabel : Not (ReaderImage.label mode layout.boundaryCallee = Arithmetic.encodeNat mode layout.scratch)
  scratchNotBoundary : Not (Arithmetic.encodeNat mode layout.boundary = Arithmetic.encodeNat mode layout.scratch)
  scratchNotResume : Not (Arithmetic.encodeNat mode layout.resume = Arithmetic.encodeNat mode layout.scratch)
  resumeNotSlot : Not (Arithmetic.encodeNat mode layout.resume = Arithmetic.encodeNat mode layout.slot)
  scratchNotSlot : Not (Arithmetic.encodeNat mode layout.scratch = Arithmetic.encodeNat mode layout.slot)

/-- Static setup transfers across memory changes that preserve its three reader
labels and reusable top. All later stages still derive their executed states. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.start)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.top) = load mode original.memory (Arithmetic.encodeNat mode layout.top))
    (captureFrame : load mode actual.memory (ReaderImage.label mode layout.start) = load mode original.memory (ReaderImage.label mode layout.start))
    (candidateFrame : load mode actual.memory (ReaderImage.label mode layout.candidateCallee) = load mode original.memory (ReaderImage.label mode layout.candidateCallee))
    (boundaryFrame : load mode actual.memory (ReaderImage.label mode layout.boundaryCallee) = load mode original.memory (ReaderImage.label mode layout.boundaryCallee)) :
    Ready mode layout actual := by
  exact {
    location := location
    captureFits := ready.captureFits
    captureWithin := ready.captureWithin
    capturePointer := captureFrame.trans ready.capturePointer
    resumeSetup := ScalarImage.transport_ready mode .store (resumeLayout mode layout) _ _ ready.resumeSetup rfl intact
    candidateSetup := ReadInvocationImage.transport_ready mode (candidateLayout mode layout) _ _ ready.candidateSetup rfl intact topFrame candidateFrame
    scratchSetup := ScalarImage.transport_ready mode .store (scratchLayout mode layout) _ _ ready.scratchSetup rfl intact
    boundarySetup := ReadInvocationImage.transport_ready mode (boundaryLayout mode layout) _ _ ready.boundarySetup rfl intact topFrame boundaryFrame
    candidatePointer := candidateFrame.trans ready.candidatePointer
    boundaryPointer := boundaryFrame.trans ready.boundaryPointer
    candidateNotSlot := ready.candidateNotSlot
    boundaryNotSlot := ready.boundaryNotSlot
    resumeNotTop := ready.resumeNotTop
    resumeNotCandidateLabel := ready.resumeNotCandidateLabel
    resumeNotCandidate := ready.resumeNotCandidate
    resumeNotBoundaryLabel := ready.resumeNotBoundaryLabel
    resumeNotBoundary := ready.resumeNotBoundary
    scratchNotTop := ready.scratchNotTop
    scratchNotBoundaryLabel := ready.scratchNotBoundaryLabel
    scratchNotBoundary := ready.scratchNotBoundary
    scratchNotResume := ready.scratchNotResume
    resumeNotSlot := ready.resumeNotSlot
    scratchNotSlot := ready.scratchNotSlot }

theorem capture_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (captured mode layout state).memory = state.memory :=
  Reader.finish_memory mode state _ _ _ (ReaderImage.first_hits mode layout.start state ready.location)
    (ReaderImage.second_hits mode layout.start state ready.location)

theorem capture_accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (captured mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.slot) := by
  rw [captured, Reader.finish_accumulator mode state _ _ _ (ReaderImage.first_hits mode layout.start state ready.location)
    (ReaderImage.second_hits mode layout.start state ready.location), ready.capturePointer]

theorem capture_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (captureProgram mode layout state) (captured mode layout state) := by
  apply ReaderView.trace mode layout.start layout.origin layout.gridBase layout.captureInitial layout.whole state
    ready.location ready.captureFits ready.candidateSetup.enough ready.candidateSetup.gap ready.captureWithin ready.candidateSetup.intact
  rw [ready.capturePointer]
  exact ready.candidateSetup.slotOwned

theorem capture_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase)
      (captureProgram mode layout state) state := by
  apply ReaderView.owned_run mode layout.start layout.origin layout.gridBase layout.captureInitial layout.whole state
    ready.location ready.captureFits ready.captureWithin
  rw [ready.capturePointer]
  exact ready.candidateSetup.slotOwned

theorem resume_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ScalarImage.Ready mode .store (resumeLayout mode layout) (captured mode layout state) := by
  apply ScalarImage.transport_ready mode .store (resumeLayout mode layout) _ _ ready.resumeSetup
  · exact ReaderImage.finish_pc mode layout.start state ready.location
  · rw [capture_memory mode layout state ready]
    exact ready.candidateSetup.intact

theorem resumed_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (different : Not (observed = Arithmetic.encodeNat mode layout.resume)) :
    load mode (resumed mode layout state).memory observed = load mode state.memory observed := by
  rw [resumed, ScalarImage.load_frame mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready) observed owned different,
    capture_memory mode layout state ready]

theorem candidate_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadInvocationImage.Ready mode (candidateLayout mode layout) (resumed mode layout state) := by
  apply ReadInvocationImage.transport_ready mode (candidateLayout mode layout) _ _ ready.candidateSetup
  · exact ScalarImage.pc mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)
  · exact ScalarImage.finish_intact mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)
  · exact resumed_load_frame mode layout state ready _ ready.candidateSetup.topOwned ready.resumeNotTop
  · exact resumed_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (candidateLayout mode layout) _ ready.candidateSetup) ready.resumeNotCandidateLabel

theorem candidate_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.candidate) := by
  have owns := ready.candidateSetup.pointerOwned
  change SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.candidateCallee)) at owns
  rw [ready.candidatePointer] at owns
  exact owns

theorem candidate_accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (candidateRead mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.candidate) := by
  rw [candidateRead, ReadInvocationImage.accumulator mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready)]
  have labelFrame := resumed_load_frame mode layout state ready _
    (ReadInvocationImage.label_owned mode (candidateLayout mode layout) _ ready.candidateSetup) ready.resumeNotCandidateLabel
  change load mode (resumed mode layout state).memory (ReaderImage.label mode layout.candidateCallee) =
    load mode state.memory (ReaderImage.label mode layout.candidateCallee) at labelFrame
  change (if load mode (resumed mode layout state).memory (ReaderImage.label mode layout.candidateCallee) = Arithmetic.encodeNat mode layout.slot
    then ReadInvocationImage.callerEnd mode (candidateLayout mode layout)
    else load mode (resumed mode layout state).memory (load mode (resumed mode layout state).memory (ReaderImage.label mode layout.candidateCallee))) =
    load mode state.memory (Arithmetic.encodeNat mode layout.candidate)
  rw [labelFrame, ready.candidatePointer, ite_eq_right ready.candidateNotSlot]
  exact resumed_load_frame mode layout state ready _ (candidate_owned mode layout state ready) ready.resumeNotCandidate

theorem scratch_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ScalarImage.Ready mode .store (scratchLayout mode layout) (candidateRead mode layout state) := by
  apply ScalarImage.transport_ready mode .store (scratchLayout mode layout) _ _ ready.scratchSetup
  · exact ReadInvocationImage.return_pc mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready)
  · exact ReadInvocationImage.finish_intact mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready)

theorem scratched_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notResume : Not (observed = Arithmetic.encodeNat mode layout.resume))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot))
    (notScratch : Not (observed = Arithmetic.encodeNat mode layout.scratch)) :
    load mode (scratched mode layout state).memory observed = load mode state.memory observed := by
  rw [scratched, ScalarImage.load_frame mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready) observed owned notScratch,
    candidateRead, ReadInvocationImage.load_frame mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready) observed owned notSlot]
  exact resumed_load_frame mode layout state ready observed owned notResume

theorem boundary_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadInvocationImage.Ready mode (boundaryLayout mode layout) (scratched mode layout state) := by
  apply ReadInvocationImage.transport_ready mode (boundaryLayout mode layout) _ _ ready.boundarySetup
  · exact ScalarImage.pc mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)
  · exact ScalarImage.finish_intact mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)
  · exact scratched_load_frame mode layout state ready _ ready.boundarySetup.topOwned
      ready.resumeNotTop ready.boundarySetup.topDifferent ready.scratchNotTop
  · exact scratched_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (boundaryLayout mode layout) _ ready.boundarySetup)
      ready.resumeNotBoundaryLabel ready.boundarySetup.labelDifferent ready.scratchNotBoundaryLabel

theorem boundary_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.boundary) := by
  have owns := ready.boundarySetup.pointerOwned
  change SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.boundaryCallee)) at owns
  rw [ready.boundaryPointer] at owns
  exact owns

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.boundary) := by
  rw [finish, ReadInvocationImage.accumulator mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)]
  have labelFrame := scratched_load_frame mode layout state ready _
    (ReadInvocationImage.label_owned mode (boundaryLayout mode layout) _ ready.boundarySetup)
    ready.resumeNotBoundaryLabel ready.boundarySetup.labelDifferent ready.scratchNotBoundaryLabel
  change load mode (scratched mode layout state).memory (ReaderImage.label mode layout.boundaryCallee) =
    load mode state.memory (ReaderImage.label mode layout.boundaryCallee) at labelFrame
  change (if load mode (scratched mode layout state).memory (ReaderImage.label mode layout.boundaryCallee) = Arithmetic.encodeNat mode layout.slot
    then ReadInvocationImage.callerEnd mode (boundaryLayout mode layout)
    else load mode (scratched mode layout state).memory (load mode (scratched mode layout state).memory (ReaderImage.label mode layout.boundaryCallee))) =
    load mode state.memory (Arithmetic.encodeNat mode layout.boundary)
  rw [labelFrame, ready.boundaryPointer, ite_eq_right ready.boundaryNotSlot]
  exact scratched_load_frame mode layout state ready _ (boundary_owned mode layout state ready)
    ready.resumeNotBoundary ready.boundaryNotSlot ready.scratchNotBoundary

theorem saved_resume (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.resume) =
      load mode state.memory (Arithmetic.encodeNat mode layout.slot) := by
  have resumeOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.resume) :=
    ready.resumeSetup.owned
  rw [finish, ReadInvocationImage.load_frame mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready) _ resumeOwned ready.resumeNotSlot,
    scratched, ScalarImage.load_frame mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready) _ resumeOwned ready.scratchNotResume,
    candidateRead, ReadInvocationImage.load_frame mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready) _ resumeOwned ready.resumeNotSlot]
  change load mode (ScalarImage.finish mode .store (resumeLayout mode layout) (captured mode layout state)).memory
    (Arithmetic.encodeNat mode (resumeLayout mode layout).target) = _
  rw [ScalarImage.written_value mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)]
  exact capture_accumulator mode layout state ready

theorem saved_candidate (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.scratch) =
      load mode state.memory (Arithmetic.encodeNat mode layout.candidate) := by
  have scratchOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.scratch) :=
    ready.scratchSetup.owned
  rw [finish, ReadInvocationImage.load_frame mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready) _ scratchOwned ready.scratchNotSlot]
  change load mode (ScalarImage.finish mode .store (scratchLayout mode layout) (candidateRead mode layout state)).memory
    (Arithmetic.encodeNat mode (scratchLayout mode layout).target) = _
  rw [ScalarImage.written_value mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)]
  exact candidate_accumulator mode layout state ready

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.slot :=
  ReadInvocationImage.stack mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).carry = state.carry := by
  rw [finish, ReadInvocationImage.carry mode (boundaryLayout mode layout) _,
    scratched, ScalarImage.store_carry, candidateRead, ReadInvocationImage.carry mode (candidateLayout mode layout) _,
    resumed, ScalarImage.store_carry, captured, Reader.finish_carry]

theorem pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = Arithmetic.encodeNat mode (endPosition mode layout) :=
  ReadInvocationImage.return_pc mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)

theorem position (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc.toNat = endPosition mode layout :=
  ReadInvocationImage.return_position mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode layout state).memory :=
  ReadInvocationImage.finish_intact mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  ReadInvocationImage.top_reusable mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)

theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notResume : Not (observed = Arithmetic.encodeNat mode layout.resume))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot))
    (notScratch : Not (observed = Arithmetic.encodeNat mode layout.scratch)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [finish, ReadInvocationImage.load_frame mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready) observed owned notSlot]
  exact scratched_load_frame mode layout state ready observed owned notResume notSlot notScratch

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode
    (Fetch.trace_append mode
      (Fetch.trace_append mode
        (Fetch.trace_append mode (capture_trace mode layout state ready)
          (ScalarImage.trace mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)))
        (ReadInvocationImage.trace mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready)))
      (ScalarImage.trace mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)))
    (ReadInvocationImage.trace mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready))

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode layout state) state := by
  have captureRun := (Fetch.trace_run_eq mode (capture_trace mode layout state ready)).symm
  have firstTrace := Fetch.trace_append mode (capture_trace mode layout state ready)
    (ScalarImage.trace mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready))
  have firstRun : runForms mode (captureProgram mode layout state ++ ScalarImage.program mode .store (resumeLayout mode layout)) state =
      resumed mode layout state := (Fetch.trace_run_eq mode firstTrace).symm
  have secondTrace := Fetch.trace_append mode firstTrace
    (ReadInvocationImage.trace mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready))
  have secondRun : runForms mode (captureProgram mode layout state ++ ScalarImage.program mode .store (resumeLayout mode layout) ++
      ReadInvocationImage.program mode (candidateLayout mode layout) (resumed mode layout state)) state =
      candidateRead mode layout state := (Fetch.trace_run_eq mode secondTrace).symm
  have thirdTrace := Fetch.trace_append mode secondTrace
    (ScalarImage.trace mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready))
  have thirdRun : runForms mode (captureProgram mode layout state ++ ScalarImage.program mode .store (resumeLayout mode layout) ++
      ReadInvocationImage.program mode (candidateLayout mode layout) (resumed mode layout state) ++
      ScalarImage.program mode .store (scratchLayout mode layout)) state = scratched mode layout state :=
    (Fetch.trace_run_eq mode thirdTrace).symm
  rw [program, Writes.owned_run_append, thirdRun, Writes.owned_run_append, secondRun,
    Writes.owned_run_append, firstRun, Writes.owned_run_append, captureRun]
  exact ⟨⟨⟨⟨capture_owned_run mode layout state ready,
    ScalarImage.owned_run mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)⟩,
    ReadInvocationImage.owned_run mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready)⟩,
    ScalarImage.owned_run mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)⟩,
    ReadInvocationImage.owned_run mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready)⟩

/-- The two calls overwrite Slot in sequence; the inline capture itself
restores all memory. Keeping both Slot stores records the exact byte effects. -/
theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode
        (ByteMemory.putWord mode
          (ByteMemory.putWord mode state.memory layout.resume (load mode state.memory (Arithmetic.encodeNat mode layout.slot)))
          layout.slot (ReadInvocationImage.calleeEnd mode (candidateLayout mode layout)))
        layout.scratch (load mode state.memory (Arithmetic.encodeNat mode layout.candidate)))
      layout.slot (ReadInvocationImage.calleeEnd mode (boundaryLayout mode layout)) := by
  rw [finish, ReadInvocationImage.memory_effect mode (boundaryLayout mode layout) _ (boundary_ready mode layout state ready),
    scratched, ScalarImage.memory_effect mode .store (scratchLayout mode layout) _ (scratch_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (candidateRead mode layout state).memory layout.scratch
    (candidateRead mode layout state).accumulator) layout.slot _ = _
  rw [candidate_accumulator mode layout state ready, candidateRead,
    ReadInvocationImage.memory_effect mode (candidateLayout mode layout) _ (candidate_ready mode layout state ready),
    resumed, ScalarImage.memory_effect mode .store (resumeLayout mode layout) _ (resume_ready mode layout state ready)]
  change ByteMemory.putWord mode
    (ByteMemory.putWord mode (ByteMemory.putWord mode (ByteMemory.putWord mode (captured mode layout state).memory layout.resume
      (captured mode layout state).accumulator) layout.slot _) layout.scratch _) layout.slot _ = _
  rw [capture_memory mode layout state ready, capture_accumulator mode layout state ready]

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideResume : Not (ByteMemory.Inside layout.resume mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.slot mode.wordBytes position))
    (outsideScratch : Not (ByteMemory.Inside layout.scratch mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [memory_effect mode layout state ready]
  unfold ByteMemory.putWord
  rw [ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideScratch),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideResume)]

theorem boundary_value_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.boundary) =
      load mode state.memory (Arithmetic.encodeNat mode layout.boundary) :=
  load_frame mode layout state ready _ (boundary_owned mode layout state ready)
    ready.resumeNotBoundary ready.boundaryNotSlot ready.scratchNotBoundary

theorem boundary_pointer_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (ReaderImage.label mode layout.boundaryCallee) = Arithmetic.encodeNat mode layout.boundary := by
  have labelOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.boundaryCallee) :=
    ReadInvocationImage.label_owned mode (boundaryLayout mode layout) _ ready.boundarySetup
  rw [load_frame mode layout state ready _ labelOwned
    ready.resumeNotBoundaryLabel ready.boundarySetup.labelDifferent ready.scratchNotBoundaryLabel]
  exact ready.boundaryPointer

theorem run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    runForms mode (program mode layout state) state = finish mode layout state :=
  (Fetch.trace_run_eq mode (trace mode layout state ready)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) :
    (program mode layout state).length = 26 := by
  simp only [program, List.length_append, ScalarImage.program_count, ReadInvocationImage.program_count,
    captureProgram, List.length_cons, List.length_nil]

end SmcTuring.Native.GuardSetupImage
