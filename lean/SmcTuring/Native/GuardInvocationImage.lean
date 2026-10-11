module
public import SmcTuring.Native.GuardImage

public section

namespace SmcTuring.Native.GuardInvocationImage

open Execution ControlImage

structure Layout (mode : Mode) where
  caller : Nat
  guard : GuardImage.Layout mode

@[expose] def callerTarget (mode : Mode) (layout : Layout mode) : Calls.Target :=
  CallsImage.callTarget mode layout.caller (.relative layout.guard.setup.start)
@[expose] def callerProgram (mode : Mode) (layout : Layout mode) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode layout.caller layout.guard.setup.top)
    (CallsImage.secondDisp mode layout.caller layout.guard.setup.top) (callerTarget mode layout)
@[expose] def afterCaller (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Calls.called mode state (CallsImage.firstDisp mode layout.caller layout.guard.setup.top)
    (CallsImage.secondDisp mode layout.caller layout.guard.setup.top) (callerTarget mode layout)
@[expose] def bodyView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  GuardSetupImage.viewAt mode state layout.guard.setup.start
@[expose] def callerEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (layout.caller + CallsImage.totalSize mode (.relative layout.guard.setup.start))
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  GuardImage.finish mode layout.guard (afterCaller mode layout state)
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  callerProgram mode layout ++ GuardImage.program mode layout.guard (afterCaller mode layout state)
@[expose] def borrowed (mode : Mode) (layout : Layout mode) (state : State mode) : Bool :=
  GuardImage.borrowed mode layout.guard state

/-- Original-memory placement setup only. The actual post-call guard setup is
derived below from the caller's owned slot write and byte disjointness. -/
structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode layout.caller
  callerRanges : CallsImage.Ranges mode layout.caller layout.guard.setup.top (.relative layout.guard.setup.start)
  callerFits : layout.caller + CallsImage.totalSize mode (.relative layout.guard.setup.start) < 2 ^ (8 * mode.wordBytes)
  callerWithin : Fragment.Within mode
    (ControlPacking.place mode layout.caller (CallsImage.packets mode layout.caller layout.guard.setup.top (.relative layout.guard.setup.start)))
    (SpacedPacking.place mode layout.guard.setup.origin layout.guard.setup.whole)
  bodySetup : GuardImage.Ready mode layout.guard (bodyView mode layout state)
  captureDifferent : Not (ReaderImage.label mode layout.guard.setup.start = Arithmetic.encodeNat mode layout.guard.setup.slot)

theorem caller_run (mode : Mode) (layout : Layout mode) (state : State mode) :
    runForms mode (callerProgram mode layout) state = afterCaller mode layout state := rfl

theorem caller_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Calls.StackReady mode state (Arithmetic.encodeNat mode layout.guard.setup.top) (Arithmetic.encodeNat mode layout.guard.setup.slot)
      (CallsImage.firstDisp mode layout.caller layout.guard.setup.top) (CallsImage.secondDisp mode layout.caller layout.guard.setup.top) :=
  CallsImage.stack_ready mode layout.caller layout.guard.setup.top layout.guard.setup.slot (.relative layout.guard.setup.start) state
    ready.location ready.callerRanges ready.bodySetup.setupReady.candidateSetup.topValue

theorem caller_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).pc = Arithmetic.encodeNat mode layout.guard.setup.start :=
  CallsImage.target_pc mode layout.caller layout.guard.setup.top (.relative layout.guard.setup.start) state ready.location ready.callerRanges

theorem caller_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).memory = ByteMemory.putWord mode state.memory
      (Arithmetic.encodeNat mode layout.guard.setup.slot).toNat (callerEnd mode layout) := by
  rw [afterCaller, Calls.called_memory mode state _ _ _ _ _ (caller_ready mode layout state ready)]
  unfold callerTarget
  rw [CallsImage.return_next mode layout.caller layout.guard.setup.top (.relative layout.guard.setup.start) state ready.location]
  rfl

theorem caller_memory_nat (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).memory = ByteMemory.putWord mode state.memory layout.guard.setup.slot (callerEnd mode layout) := by
  rw [caller_memory mode layout state ready, Arithmetic.encode_nat_toNat mode layout.guard.setup.slot ready.bodySetup.setupReady.candidateSetup.slotFits]

theorem caller_return_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.slot) = callerEnd mode layout := by
  rw [caller_memory mode layout state ready, load_put_word]

theorem caller_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (callerProgram mode layout) (afterCaller mode layout state) :=
  CallsImage.trace mode layout.caller layout.guard.setup.top layout.guard.setup.origin layout.guard.setup.gridBase
    (.relative layout.guard.setup.start) layout.guard.setup.whole state ready.location ready.callerRanges ready.callerFits
    ready.bodySetup.setupReady.candidateSetup.enough ready.bodySetup.setupReady.candidateSetup.gap ready.callerWithin
    ready.bodySetup.setupReady.candidateSetup.intact ready.bodySetup.setupReady.candidateSetup.topOwned

theorem caller_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase)
      (callerProgram mode layout) state :=
  CallsImage.owned_run mode layout.caller layout.guard.setup.top layout.guard.setup.slot layout.guard.setup.origin layout.guard.setup.gridBase
    (.relative layout.guard.setup.start) layout.guard.setup.whole state ready.location ready.callerRanges
    ready.bodySetup.setupReady.candidateSetup.topValue ready.bodySetup.setupReady.candidateSetup.topOwned ready.bodySetup.setupReady.candidateSetup.slotOwned

theorem caller_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase (afterCaller mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase state _ _
    ready.bodySetup.setupReady.candidateSetup.enough ready.bodySetup.setupReady.candidateSetup.gap ready.bodySetup.setupReady.candidateSetup.intact
    (caller_owned_run mode layout state ready) (caller_trace mode layout state ready)

theorem caller_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase observed)
    (different : Not (observed = Arithmetic.encodeNat mode layout.guard.setup.slot)) :
    load mode (afterCaller mode layout state).memory observed = load mode state.memory observed := by
  rw [caller_memory mode layout state ready]
  exact Writes.load_frame mode state.memory _ _ _ (Fragment.owned_fields_separate mode layout.guard.setup.whole
    layout.guard.setup.origin layout.guard.setup.gridBase _ _ ready.bodySetup.setupReady.candidateSetup.gap owned
    ready.bodySetup.setupReady.candidateSetup.slotOwned different)

theorem caller_role_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : GuardImage.Role)
    (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase (GuardImage.roleWord mode layout.guard observed))
    (different : Not (observed = .slot)) :
    load mode (afterCaller mode layout state).memory (GuardImage.roleWord mode layout.guard observed) =
      load mode state.memory (GuardImage.roleWord mode layout.guard observed) :=
  caller_load_frame mode layout state ready _ owned (GuardImage.different_roles mode layout.guard _ ready.bodySetup observed .slot different)

theorem capture_label_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase
      (ReaderImage.label mode layout.guard.setup.start) :=
  Or.inl (ReaderView.label_owned mode layout.guard.setup.start layout.guard.setup.origin layout.guard.setup.captureInitial
    layout.guard.setup.whole ready.bodySetup.setupReady.captureFits ready.bodySetup.setupReady.captureWithin)

/-- Read-only guard metadata, including the comparison boundary and failure
target needed to retain the source-level branch meaning across a prefix. -/
inductive Metadata where
  | top | capture | candidateReader | boundaryReader | zeroReader | zero
  | continuationReader | alternativeReader | maskReader | boundary | terminal
  deriving DecidableEq

@[expose] def metadataWord (mode : Mode) (layout : Layout mode) : Metadata -> Word mode
  | .top => Arithmetic.encodeNat mode layout.guard.setup.top
  | .capture => ReaderImage.label mode layout.guard.setup.start
  | .candidateReader => ReaderImage.label mode layout.guard.setup.candidateCallee
  | .boundaryReader => ReaderImage.label mode layout.guard.setup.boundaryCallee
  | .zeroReader => ReaderImage.label mode layout.guard.zeroCallee
  | .zero => Arithmetic.encodeNat mode layout.guard.zero
  | .continuationReader => ReaderImage.label mode (GuardImage.continuationCallee layout.guard)
  | .alternativeReader => ReaderImage.label mode (GuardImage.alternativeCallee layout.guard)
  | .maskReader => ReaderImage.label mode layout.guard.maskCallee
  | .boundary => Arithmetic.encodeNat mode layout.guard.setup.boundary
  | .terminal => Arithmetic.encodeNat mode layout.guard.terminal

theorem metadata_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Metadata) :
    SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase (metadataWord mode layout observed) := by
  cases observed with
  | top => exact ready.bodySetup.setupReady.candidateSetup.topOwned
  | capture => exact capture_label_owned mode layout state ready
  | candidateReader => exact ReadInvocationImage.label_owned mode (GuardSetupImage.candidateLayout mode layout.guard.setup) _ ready.bodySetup.setupReady.candidateSetup
  | boundaryReader => exact ReadInvocationImage.label_owned mode (GuardSetupImage.boundaryLayout mode layout.guard.setup) _ ready.bodySetup.setupReady.boundarySetup
  | zeroReader => exact ReadInvocationImage.label_owned mode (GuardImage.borrowLayout mode layout.guard).reader _ ready.bodySetup.borrowSetup.readSetup
  | zero => exact BorrowMaskImage.zero_owned mode (GuardImage.borrowLayout mode layout.guard) _ ready.bodySetup.borrowSetup
  | continuationReader => exact ReadInvocationImage.label_owned mode (GuardSelectionImage.firstLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.firstReady.readReady
  | alternativeReader => exact ReadInvocationImage.label_owned mode (GuardSelectionImage.secondLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.secondSetup.readReady
  | maskReader => exact ReadInvocationImage.label_owned mode (GuardSelectionImage.thirdLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.thirdSetup.readReady
  | boundary => exact GuardSetupImage.boundary_owned mode layout.guard.setup _ ready.bodySetup.setupReady
  | terminal => exact GuardImage.terminal_owned mode layout.guard _ ready.bodySetup

theorem metadata_not_slot (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Metadata) : Not (metadataWord mode layout observed = Arithmetic.encodeNat mode layout.guard.setup.slot) := by
  cases observed with
  | top => exact ready.bodySetup.setupReady.candidateSetup.topDifferent
  | capture => exact ready.captureDifferent
  | candidateReader => exact ready.bodySetup.setupReady.candidateSetup.labelDifferent
  | boundaryReader => exact ready.bodySetup.setupReady.boundarySetup.labelDifferent
  | zeroReader => exact ready.bodySetup.borrowSetup.readSetup.labelDifferent
  | zero => exact GuardImage.different_roles mode layout.guard _ ready.bodySetup .zero .slot (by decide)
  | continuationReader => exact ready.bodySetup.selectionSetup.firstReady.readReady.labelDifferent
  | alternativeReader => exact ready.bodySetup.selectionSetup.secondSetup.readReady.labelDifferent
  | maskReader => exact ready.bodySetup.selectionSetup.thirdSetup.readReady.labelDifferent
  | boundary => exact ready.bodySetup.setupReady.boundaryNotSlot
  | terminal => exact GuardImage.different_roles mode layout.guard _ ready.bodySetup .terminal .slot (by decide)

/-- Transfer original-memory placement setup to an executed prefix result.
No guard trace, candidate value, mask or selected target is supplied. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.caller)
    (intact : SpacedCombinedImage.Intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase actual.memory)
    (frames : forall observed, load mode actual.memory (metadataWord mode layout observed) = load mode original.memory (metadataWord mode layout observed)) :
    Ready mode layout actual := by
  refine ⟨location, ready.callerRanges, ready.callerFits, ready.callerWithin, ?_, ready.captureDifferent⟩
  apply GuardImage.transport_ready mode layout.guard _ _ ready.bodySetup
  · rfl
  · exact intact
  · exact frames .top
  · exact frames .capture
  · exact frames .candidateReader
  · exact frames .boundaryReader
  · exact frames .zeroReader
  · exact frames .zero
  · exact frames .continuationReader
  · exact frames .alternativeReader
  · exact frames .maskReader

theorem body_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    GuardImage.Ready mode layout.guard (afterCaller mode layout state) := by
  apply GuardImage.transport_ready mode layout.guard _ _ ready.bodySetup
  · exact caller_pc mode layout state ready
  · exact caller_intact mode layout state ready
  · exact caller_role_frame mode layout state ready .top ready.bodySetup.setupReady.candidateSetup.topOwned (by decide)
  · exact caller_load_frame mode layout state ready _ (capture_label_owned mode layout state ready) ready.captureDifferent
  · exact caller_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (GuardSetupImage.candidateLayout mode layout.guard.setup) _ ready.bodySetup.setupReady.candidateSetup)
      ready.bodySetup.setupReady.candidateSetup.labelDifferent
  · exact caller_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (GuardSetupImage.boundaryLayout mode layout.guard.setup) _ ready.bodySetup.setupReady.boundarySetup)
      ready.bodySetup.setupReady.boundarySetup.labelDifferent
  · exact caller_role_frame mode layout state ready .zeroLabel
      (ReadInvocationImage.label_owned mode (GuardImage.borrowLayout mode layout.guard).reader _ ready.bodySetup.borrowSetup.readSetup) (by decide)
  · exact caller_role_frame mode layout state ready .zero
      (BorrowMaskImage.zero_owned mode (GuardImage.borrowLayout mode layout.guard) _ ready.bodySetup.borrowSetup) (by decide)
  · exact caller_role_frame mode layout state ready .continuationLabel
      (ReadInvocationImage.label_owned mode (GuardSelectionImage.firstLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.firstReady.readReady) (by decide)
  · exact caller_role_frame mode layout state ready .alternativeLabel
      (ReadInvocationImage.label_owned mode (GuardSelectionImage.secondLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.secondSetup.readReady) (by decide)
  · exact caller_role_frame mode layout state ready .maskLabel
      (ReadInvocationImage.label_owned mode (GuardSelectionImage.thirdLayout mode (GuardImage.selectionLayout mode layout.guard)).reader _ ready.bodySetup.selectionSetup.thirdSetup.readReady) (by decide)

theorem candidate_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) =
      load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) :=
  caller_load_frame mode layout state ready _ (GuardSetupImage.candidate_owned mode layout.guard.setup _ ready.bodySetup.setupReady)
    ready.bodySetup.setupReady.candidateNotSlot

theorem boundary_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) =
      load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) :=
  caller_load_frame mode layout state ready _ (GuardSetupImage.boundary_owned mode layout.guard.setup _ ready.bodySetup.setupReady)
    ready.bodySetup.setupReady.boundaryNotSlot

theorem borrowed_after_caller (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    GuardImage.borrowed mode layout.guard (afterCaller mode layout state) = borrowed mode layout state := by
  unfold GuardImage.borrowed borrowed
  rw [candidate_value mode layout state ready, boundary_value mode layout state ready]
  rfl

theorem terminal_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.guard.terminal) =
      load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) :=
  caller_role_frame mode layout state ready .terminal (GuardImage.terminal_owned mode layout.guard _ ready.bodySetup) (by decide)

/-- The successful branch reaches the computed outer return address. Failure
reaches the original terminal word, with Base/Offset polarities reversed. -/
theorem pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = match layout.guard.sense with
      | .base => if borrowed mode layout state then load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) else callerEnd mode layout
      | .offset => if borrowed mode layout state then callerEnd mode layout else load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [finish, GuardImage.pc mode layout.guard _ (body_ready mode layout state ready), borrowed_after_caller mode layout state ready,
    terminal_value mode layout state ready, caller_return_word mode layout state ready]
  rfl

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (caller_trace mode layout state ready) (GuardImage.trace mode layout.guard _ (body_ready mode layout state ready))

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase)
      (program mode layout state) state := by
  rw [program, Writes.owned_run_append, caller_run]
  exact ⟨caller_owned_run mode layout state ready, GuardImage.owned_run mode layout.guard _ (body_ready mode layout state ready)⟩

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.guard.setup.slot :=
  GuardImage.stack mode layout.guard _ (body_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).carry = false := GuardImage.carry mode layout.guard _ (body_ready mode layout state ready)

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = match layout.guard.sense with
      | .base => callerEnd mode layout
      | .offset => load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [finish, GuardImage.accumulator mode layout.guard _ (body_ready mode layout state ready),
    caller_return_word mode layout state ready, terminal_value mode layout state ready]
  rfl

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase (finish mode layout state).memory :=
  GuardImage.finish_intact mode layout.guard _ (body_ready mode layout state ready)

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.top) =
      Arithmetic.encodeNat mode layout.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  GuardImage.top_reusable mode layout.guard _ (body_ready mode layout state ready)

theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase observed)
    (notResume : Not (observed = Arithmetic.encodeNat mode layout.guard.setup.resume))
    (notScratch : Not (observed = Arithmetic.encodeNat mode layout.guard.setup.scratch))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.guard.setup.slot))
    (notMask : Not (observed = Arithmetic.encodeNat mode layout.guard.mask))
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.guard.selected)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [finish, GuardImage.load_frame mode layout.guard _ (body_ready mode layout state ready) observed owned notResume notScratch notSlot notMask notSelected]
  exact caller_load_frame mode layout state ready observed owned notSlot

theorem selected_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.selected) = (finish mode layout state).pc :=
  GuardImage.selected_word mode layout.guard _ (body_ready mode layout state ready)

theorem slot_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.slot) =
      GuardSelectionImage.callerEnd mode (GuardImage.selectionLayout mode layout.guard) :=
  GuardImage.slot_word mode layout.guard _ (body_ready mode layout state ready)

theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode
        (ByteMemory.putWord mode
          (ByteMemory.putWord mode
            (ByteMemory.putWord mode (GuardImage.afterSetup mode layout.guard (afterCaller mode layout state)).memory layout.guard.setup.scratch
              (load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) - load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary)))
            layout.guard.setup.slot (ReadInvocationImage.calleeEnd mode (GuardImage.borrowLayout mode layout.guard).reader))
          layout.guard.mask (Arithmetic.sbbZero mode (borrowed mode layout state)))
        layout.guard.setup.slot (GuardSelectionImage.callerEnd mode (GuardImage.selectionLayout mode layout.guard)))
      layout.guard.selected (finish mode layout state).pc := by
  rw [finish, GuardImage.memory_effect mode layout.guard _ (body_ready mode layout state ready),
    candidate_value mode layout state ready, boundary_value mode layout state ready, borrowed_after_caller mode layout state ready]

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideResume : Not (ByteMemory.Inside layout.guard.setup.resume mode.wordBytes position))
    (outsideScratch : Not (ByteMemory.Inside layout.guard.setup.scratch mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.guard.setup.slot mode.wordBytes position))
    (outsideMask : Not (ByteMemory.Inside layout.guard.mask mode.wordBytes position))
    (outsideSelected : Not (ByteMemory.Inside layout.guard.selected mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [finish, GuardImage.memory_frame mode layout.guard _ (body_ready mode layout state ready) position outsideResume outsideScratch outsideSlot outsideMask outsideSelected,
    caller_memory_nat mode layout state ready]
  apply ByteMemory.put_frame
  simpa using outsideSlot

theorem run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    runForms mode (program mode layout state) state = finish mode layout state := (Fetch.trace_run_eq mode (trace mode layout state ready)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 89 := by
  simp only [program, List.length_append, GuardImage.program_count]
  rfl

end SmcTuring.Native.GuardInvocationImage
