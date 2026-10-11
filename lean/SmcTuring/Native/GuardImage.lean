module
public import SmcTuring.Native.GuardSetupImage
public import SmcTuring.Native.GuardSelectionImage

public section

namespace SmcTuring.Native.GuardImage

open Execution ControlImage

inductive Sense where | base | offset deriving DecidableEq

/-- All three stages derive their positions and placement context from the
same setup. Only the Base/Offset continuation/terminal orientation changes. -/
structure Layout (mode : Mode) where
  setup : GuardSetupImage.Layout mode
  sense : Sense
  zero : Nat
  mask : Nat
  selected : Nat
  terminal : Nat
  zeroCallee : Nat
  resumeCallee : Nat
  terminalCallee : Nat
  maskCallee : Nat
  zeroInitial : Word mode
  resumeInitial : Word mode
  terminalInitial : Word mode
  maskInitial : Word mode

@[expose] def borrowLayout (mode : Mode) (layout : Layout mode) : BorrowMaskImage.Layout mode :=
  ⟨GuardSetupImage.endPosition mode layout.setup, layout.setup.scratch, layout.mask, layout.zero,
    ⟨GuardSetupImage.endPosition mode layout.setup + ScalarImage.size mode .subtract, layout.zeroCallee,
      layout.setup.top, layout.setup.slot, layout.setup.origin, layout.setup.gridBase, layout.zeroInitial, layout.setup.whole⟩⟩
@[expose] def selectionStart (mode : Mode) (layout : Layout mode) : Nat :=
  BorrowMaskImage.storeStart mode (borrowLayout mode layout) + ScalarImage.size mode .store + ScalarImage.size mode .subtractBorrowZero
@[expose] def continuationField {mode : Mode} (layout : Layout mode) : Nat := match layout.sense with | .base => layout.setup.resume | .offset => layout.terminal
@[expose] def terminalField {mode : Mode} (layout : Layout mode) : Nat := match layout.sense with | .base => layout.terminal | .offset => layout.setup.resume
@[expose] def continuationCallee {mode : Mode} (layout : Layout mode) : Nat := match layout.sense with | .base => layout.resumeCallee | .offset => layout.terminalCallee
@[expose] def alternativeCallee {mode : Mode} (layout : Layout mode) : Nat := match layout.sense with | .base => layout.terminalCallee | .offset => layout.resumeCallee
@[expose] def continuationInitial {mode : Mode} (layout : Layout mode) : Word mode := match layout.sense with | .base => layout.resumeInitial | .offset => layout.terminalInitial
@[expose] def alternativeInitial {mode : Mode} (layout : Layout mode) : Word mode := match layout.sense with | .base => layout.terminalInitial | .offset => layout.resumeInitial
@[expose] def selectionLayout (mode : Mode) (layout : Layout mode) : GuardSelectionImage.Layout mode :=
  ⟨selectionStart mode layout, continuationCallee layout, alternativeCallee layout, layout.maskCallee,
    continuationField layout, terminalField layout, layout.mask, layout.selected, layout.setup.top, layout.setup.slot,
    layout.setup.origin, layout.setup.gridBase, layout.setup.whole, continuationInitial layout, alternativeInitial layout, layout.maskInitial⟩
@[expose] def borrowView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (GuardSetupImage.endPosition mode layout.setup) }
@[expose] def selectionView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (selectionStart mode layout) }
@[expose] def afterSetup (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := GuardSetupImage.finish mode layout.setup state
@[expose] def afterBorrow (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := BorrowMaskImage.finish mode (borrowLayout mode layout) (afterSetup mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := GuardSelectionImage.finish mode (selectionLayout mode layout) (afterBorrow mode layout state)
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  GuardSetupImage.program mode layout.setup state ++ BorrowMaskImage.program mode (borrowLayout mode layout) (afterSetup mode layout state) ++
    GuardSelectionImage.program mode (selectionLayout mode layout) (afterBorrow mode layout state)
@[expose] def borrowed (mode : Mode) (layout : Layout mode) (state : State mode) : Bool := Arithmetic.unsignedBorrow
  (load mode state.memory (Arithmetic.encodeNat mode layout.setup.candidate)) (load mode state.memory (Arithmetic.encodeNat mode layout.setup.boundary))

/-- These are physical current-code operand addresses, including the three
reader labels used by this guard's chosen orientation. -/
inductive Role where
  | top | slot | resume | scratch | zero | mask | selected | terminal
  | zeroLabel | continuationLabel | alternativeLabel | maskLabel
  deriving DecidableEq
@[expose] def roleWord (mode : Mode) (layout : Layout mode) : Role -> Word mode
  | .top => Arithmetic.encodeNat mode layout.setup.top
  | .slot => Arithmetic.encodeNat mode layout.setup.slot
  | .resume => Arithmetic.encodeNat mode layout.setup.resume
  | .scratch => Arithmetic.encodeNat mode layout.setup.scratch
  | .zero => Arithmetic.encodeNat mode layout.zero
  | .mask => Arithmetic.encodeNat mode layout.mask
  | .selected => Arithmetic.encodeNat mode layout.selected
  | .terminal => Arithmetic.encodeNat mode layout.terminal
  | .zeroLabel => ReaderImage.label mode layout.zeroCallee
  | .continuationLabel => ReaderImage.label mode (continuationCallee layout)
  | .alternativeLabel => ReaderImage.label mode (alternativeCallee layout)
  | .maskLabel => ReaderImage.label mode layout.maskCallee

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  setupReady : GuardSetupImage.Ready mode layout.setup state
  borrowSetup : BorrowMaskImage.Ready mode (borrowLayout mode layout) (borrowView mode layout state)
  selectionSetup : GuardSelectionImage.Ready mode (selectionLayout mode layout) (selectionView mode layout state)
  roles : Function.Injective (roleWord mode layout)

/-- Preserve only static reader metadata across an incoming caller push;
candidate, boundary and return values are read from the actual new memory. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.setup.start)
    (intact : SpacedCombinedImage.Intact mode layout.setup.whole layout.setup.origin layout.setup.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.setup.top) = load mode original.memory (Arithmetic.encodeNat mode layout.setup.top))
    (captureFrame : load mode actual.memory (ReaderImage.label mode layout.setup.start) = load mode original.memory (ReaderImage.label mode layout.setup.start))
    (candidateFrame : load mode actual.memory (ReaderImage.label mode layout.setup.candidateCallee) = load mode original.memory (ReaderImage.label mode layout.setup.candidateCallee))
    (boundaryFrame : load mode actual.memory (ReaderImage.label mode layout.setup.boundaryCallee) = load mode original.memory (ReaderImage.label mode layout.setup.boundaryCallee))
    (zeroLabelFrame : load mode actual.memory (ReaderImage.label mode layout.zeroCallee) = load mode original.memory (ReaderImage.label mode layout.zeroCallee))
    (zeroFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.zero) = load mode original.memory (Arithmetic.encodeNat mode layout.zero))
    (continuationFrame : load mode actual.memory (ReaderImage.label mode (continuationCallee layout)) = load mode original.memory (ReaderImage.label mode (continuationCallee layout)))
    (alternativeFrame : load mode actual.memory (ReaderImage.label mode (alternativeCallee layout)) = load mode original.memory (ReaderImage.label mode (alternativeCallee layout)))
    (maskFrame : load mode actual.memory (ReaderImage.label mode layout.maskCallee) = load mode original.memory (ReaderImage.label mode layout.maskCallee)) :
    Ready mode layout actual := by
  exact {
    setupReady := GuardSetupImage.transport_ready mode layout.setup _ _ ready.setupReady location intact topFrame captureFrame candidateFrame boundaryFrame
    borrowSetup := BorrowMaskImage.transport_ready mode (borrowLayout mode layout) _ _ ready.borrowSetup rfl intact topFrame zeroLabelFrame zeroFrame
    selectionSetup := GuardSelectionImage.transport_ready mode (selectionLayout mode layout) _ _ ready.selectionSetup rfl intact topFrame continuationFrame alternativeFrame maskFrame
    roles := ready.roles }

theorem different_roles (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (first second : Role) (different : Not (first = second)) : Not (roleWord mode layout first = roleWord mode layout second) :=
  fun same => different (ready.roles same)

theorem setup_frame_role (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Role) (owned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout observed))
    (notResume : Not (observed = .resume)) (notScratch : Not (observed = .scratch)) (notSlot : Not (observed = .slot)) :
    load mode (afterSetup mode layout state).memory (roleWord mode layout observed) = load mode state.memory (roleWord mode layout observed) :=
  GuardSetupImage.load_frame mode layout.setup state ready.setupReady _ owned
    (different_roles mode layout state ready observed .resume notResume) (different_roles mode layout state ready observed .slot notSlot)
    (different_roles mode layout state ready observed .scratch notScratch)

theorem borrow_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    BorrowMaskImage.Ready mode (borrowLayout mode layout) (afterSetup mode layout state) := by
  apply BorrowMaskImage.transport_ready mode (borrowLayout mode layout) _ _ ready.borrowSetup
  · exact GuardSetupImage.pc mode layout.setup state ready.setupReady
  · exact GuardSetupImage.finish_intact mode layout.setup state ready.setupReady
  · exact setup_frame_role mode layout state ready .top ready.setupReady.candidateSetup.topOwned (by decide) (by decide) (by decide)
  · have labelOwned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .zeroLabel) :=
      ReadInvocationImage.label_owned mode (borrowLayout mode layout).reader _ ready.borrowSetup.readSetup
    exact setup_frame_role mode layout state ready .zeroLabel labelOwned (by decide) (by decide) (by decide)
  · have zeroOwned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .zero) :=
      BorrowMaskImage.zero_owned mode (borrowLayout mode layout) _ ready.borrowSetup
    exact setup_frame_role mode layout state ready .zero zeroOwned (by decide) (by decide) (by decide)

theorem borrow_frame_role (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Role) (owned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout observed))
    (notResume : Not (observed = .resume)) (notScratch : Not (observed = .scratch)) (notSlot : Not (observed = .slot)) (notMask : Not (observed = .mask)) :
    load mode (afterBorrow mode layout state).memory (roleWord mode layout observed) = load mode state.memory (roleWord mode layout observed) := by
  rw [afterBorrow, BorrowMaskImage.load_frame mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready) _ owned
    (different_roles mode layout state ready observed .scratch notScratch) (different_roles mode layout state ready observed .slot notSlot)
    (different_roles mode layout state ready observed .mask notMask)]
  exact setup_frame_role mode layout state ready observed owned notResume notScratch notSlot

theorem selection_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    GuardSelectionImage.Ready mode (selectionLayout mode layout) (afterBorrow mode layout state) := by
  apply GuardSelectionImage.transport_ready mode (selectionLayout mode layout) _ _ ready.selectionSetup
  · exact ScalarImage.pc mode .subtractBorrowZero (BorrowMaskImage.sbbLayout mode (borrowLayout mode layout))
      (BorrowMaskImage.maskStored mode (borrowLayout mode layout) (afterSetup mode layout state))
      (BorrowMaskImage.sbb_ready mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready))
  · exact BorrowMaskImage.finish_intact mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)
  · exact borrow_frame_role mode layout state ready .top ready.setupReady.candidateSetup.topOwned (by decide) (by decide) (by decide) (by decide)
  · have labelOwned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .continuationLabel) :=
      ReadInvocationImage.label_owned mode (GuardSelectionImage.firstLayout mode (selectionLayout mode layout)).reader _ ready.selectionSetup.firstReady.readReady
    exact borrow_frame_role mode layout state ready .continuationLabel labelOwned (by decide) (by decide) (by decide) (by decide)
  · have labelOwned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .alternativeLabel) :=
      ReadInvocationImage.label_owned mode (GuardSelectionImage.secondLayout mode (selectionLayout mode layout)).reader _ ready.selectionSetup.secondSetup.readReady
    exact borrow_frame_role mode layout state ready .alternativeLabel labelOwned (by decide) (by decide) (by decide) (by decide)
  · have labelOwned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .maskLabel) :=
      ReadInvocationImage.label_owned mode (GuardSelectionImage.thirdLayout mode (selectionLayout mode layout)).reader _ ready.selectionSetup.thirdSetup.readReady
    exact borrow_frame_role mode layout state ready .maskLabel labelOwned (by decide) (by decide) (by decide) (by decide)

theorem borrow_carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterBorrow mode layout state).carry = borrowed mode layout state := by
  rw [afterBorrow, BorrowMaskImage.carry mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)]
  change Arithmetic.unsignedBorrow (load mode (afterSetup mode layout state).memory (Arithmetic.encodeNat mode layout.setup.scratch))
    (afterSetup mode layout state).accumulator = _
  rw [afterSetup, GuardSetupImage.saved_candidate mode layout.setup state ready.setupReady, GuardSetupImage.accumulator mode layout.setup state ready.setupReady]
  rfl

theorem mask_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode layout.mask) = Arithmetic.sbbZero mode (borrowed mode layout state) := by
  change load mode (BorrowMaskImage.finish mode (borrowLayout mode layout) (afterSetup mode layout state)).memory
    (Arithmetic.encodeNat mode (borrowLayout mode layout).mask) = _
  rw [BorrowMaskImage.mask mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)]
  change Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow
    (load mode (afterSetup mode layout state).memory (Arithmetic.encodeNat mode layout.setup.scratch)) (afterSetup mode layout state).accumulator) = _
  rw [afterSetup, GuardSetupImage.saved_candidate mode layout.setup state ready.setupReady, GuardSetupImage.accumulator mode layout.setup state ready.setupReady]
  rfl

theorem saved_resume (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode layout.setup.resume) = load mode state.memory (Arithmetic.encodeNat mode layout.setup.slot) := by
  have owned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (Arithmetic.encodeNat mode layout.setup.resume) := ready.setupReady.resumeSetup.owned
  rw [afterBorrow, BorrowMaskImage.load_frame mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready) _ owned
    (different_roles mode layout state ready .resume .scratch (by decide)) (different_roles mode layout state ready .resume .slot (by decide))
    (different_roles mode layout state ready .resume .mask (by decide))]
  exact GuardSetupImage.saved_resume mode layout.setup state ready.setupReady


theorem terminal_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase (roleWord mode layout .terminal) := by
  cases kind : layout.sense with
  | base =>
    have owns := GuardSelectionImage.terminal_owned mode (selectionLayout mode layout) (selectionView mode layout state) ready.selectionSetup
    simpa only [selectionLayout, terminalField, kind, roleWord] using owns
  | offset =>
    have owns := GuardSelectionImage.continuation_owned mode (selectionLayout mode layout) (selectionView mode layout state) ready.selectionSetup
    simpa only [selectionLayout, continuationField, kind, roleWord] using owns

theorem terminal_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode layout.terminal) =
      load mode state.memory (Arithmetic.encodeNat mode layout.terminal) :=
  borrow_frame_role mode layout state ready .terminal (terminal_owned mode layout state ready) (by decide) (by decide) (by decide) (by decide)

theorem pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = match layout.sense with
      | .base => if borrowed mode layout state then load mode state.memory (Arithmetic.encodeNat mode layout.terminal)
        else load mode state.memory (Arithmetic.encodeNat mode layout.setup.slot)
      | .offset => if borrowed mode layout state then load mode state.memory (Arithmetic.encodeNat mode layout.setup.slot)
        else load mode state.memory (Arithmetic.encodeNat mode layout.terminal) := by
  have chosen := GuardSelectionImage.selects mode (selectionLayout mode layout) (afterBorrow mode layout state)
    (selection_ready mode layout state ready) (borrowed mode layout state) (mask_value mode layout state ready)
  cases kind : layout.sense with
  | base =>
    change (finish mode layout state).pc = if borrowed mode layout state then
      load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode (terminalField layout))
      else load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode (continuationField layout)) at chosen
    have term : terminalField layout = layout.terminal := by simp only [terminalField, kind]
    have cont : continuationField layout = layout.setup.resume := by simp only [continuationField, kind]
    rw [term, cont, terminal_value mode layout state ready, saved_resume mode layout state ready] at chosen
    exact chosen
  | offset =>
    change (finish mode layout state).pc = if borrowed mode layout state then
      load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode (terminalField layout))
      else load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode (continuationField layout)) at chosen
    have term : terminalField layout = layout.setup.resume := by simp only [terminalField, kind]
    have cont : continuationField layout = layout.terminal := by simp only [continuationField, kind]
    rw [term, cont, terminal_value mode layout state ready, saved_resume mode layout state ready] at chosen
    exact chosen

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (Fetch.trace_append mode (GuardSetupImage.trace mode layout.setup state ready.setupReady)
    (BorrowMaskImage.trace mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)))
    (GuardSelectionImage.trace mode (selectionLayout mode layout) _ (selection_ready mode layout state ready))

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase) (program mode layout state) state := by
  have setupRun : runForms mode (GuardSetupImage.program mode layout.setup state) state = afterSetup mode layout state :=
    GuardSetupImage.run mode layout.setup state ready.setupReady
  have borrowRun : runForms mode (GuardSetupImage.program mode layout.setup state ++
      BorrowMaskImage.program mode (borrowLayout mode layout) (afterSetup mode layout state)) state = afterBorrow mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (GuardSetupImage.trace mode layout.setup state ready.setupReady)
      (BorrowMaskImage.trace mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)))).symm
  rw [program, Writes.owned_run_append, borrowRun, Writes.owned_run_append, setupRun]
  exact ⟨⟨GuardSetupImage.owned_run mode layout.setup state ready.setupReady,
    BorrowMaskImage.owned_run mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)⟩,
    GuardSelectionImage.owned_run mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)⟩

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.setup.slot :=
  GuardSelectionImage.stack mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).carry = false := GuardSelectionImage.carry mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = match layout.sense with
      | .base => load mode state.memory (Arithmetic.encodeNat mode layout.setup.slot)
      | .offset => load mode state.memory (Arithmetic.encodeNat mode layout.terminal) := by
  have acc := GuardSelectionImage.accumulator mode (selectionLayout mode layout) (afterBorrow mode layout state) (selection_ready mode layout state ready)
  change (finish mode layout state).accumulator = load mode (afterBorrow mode layout state).memory (Arithmetic.encodeNat mode (continuationField layout)) at acc
  cases kind : layout.sense with
  | base =>
    have cont : continuationField layout = layout.setup.resume := by simp only [continuationField, kind]
    rw [cont, saved_resume mode layout state ready] at acc
    exact acc
  | offset =>
    have cont : continuationField layout = layout.terminal := by simp only [continuationField, kind]
    rw [cont, terminal_value mode layout state ready] at acc
    exact acc

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.setup.whole layout.setup.origin layout.setup.gridBase (finish mode layout state).memory :=
  GuardSelectionImage.finish_intact mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.setup.top) =
      Arithmetic.encodeNat mode layout.setup.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  GuardSelectionImage.top_reusable mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)

theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.setup.whole layout.setup.origin layout.setup.gridBase observed)
    (notResume : Not (observed = Arithmetic.encodeNat mode layout.setup.resume))
    (notScratch : Not (observed = Arithmetic.encodeNat mode layout.setup.scratch))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.setup.slot))
    (notMask : Not (observed = Arithmetic.encodeNat mode layout.mask))
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [finish, GuardSelectionImage.load_frame mode (selectionLayout mode layout) _ (selection_ready mode layout state ready) observed owned notSelected notSlot,
    afterBorrow, BorrowMaskImage.load_frame mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready) observed owned notScratch notSlot notMask]
  exact GuardSetupImage.load_frame mode layout.setup state ready.setupReady observed owned notResume notSlot notScratch

theorem selected_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = (finish mode layout state).pc := by
  change load mode (GuardSelectionImage.finish mode (selectionLayout mode layout) (afterBorrow mode layout state)).memory
    (Arithmetic.encodeNat mode (selectionLayout mode layout).selected) = _
  rw [GuardSelectionImage.selected_word mode (selectionLayout mode layout) _ (selection_ready mode layout state ready),
    finish, GuardSelectionImage.pc mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)]

theorem slot_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.setup.slot) = GuardSelectionImage.callerEnd mode (selectionLayout mode layout) :=
  GuardSelectionImage.slot_word mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)

/-- Ordered byte effects of the complete guard. Setup's two saved words
are followed by the scratch SUB, zero-reader return, mask, final return and
selected target. The setup memory is itself exactly computed from the input. -/
theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode
        (ByteMemory.putWord mode
          (ByteMemory.putWord mode
            (ByteMemory.putWord mode (afterSetup mode layout state).memory layout.setup.scratch
              (load mode state.memory (Arithmetic.encodeNat mode layout.setup.candidate) - load mode state.memory (Arithmetic.encodeNat mode layout.setup.boundary)))
            layout.setup.slot (ReadInvocationImage.calleeEnd mode (borrowLayout mode layout).reader))
          layout.mask (Arithmetic.sbbZero mode (borrowed mode layout state)))
        layout.setup.slot (GuardSelectionImage.callerEnd mode (selectionLayout mode layout)))
      layout.selected (finish mode layout state).pc := by
  rw [finish, GuardSelectionImage.memory_effect mode (selectionLayout mode layout) _ (selection_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (afterBorrow mode layout state).memory layout.setup.slot _)
    layout.selected (GuardSelectionImage.selectedValue mode (selectionLayout mode layout) (afterBorrow mode layout state)) = _
  rw [← GuardSelectionImage.pc mode (selectionLayout mode layout) _ (selection_ready mode layout state ready), afterBorrow,
    BorrowMaskImage.memory_effect mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready)]
  change ByteMemory.putWord mode
    (ByteMemory.putWord mode (ByteMemory.putWord mode
      (ByteMemory.putWord mode (ByteMemory.putWord mode (afterSetup mode layout state).memory layout.setup.scratch
        (load mode (afterSetup mode layout state).memory (Arithmetic.encodeNat mode layout.setup.scratch) - (afterSetup mode layout state).accumulator))
        layout.setup.slot _) layout.mask
      (Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow
        (load mode (afterSetup mode layout state).memory (Arithmetic.encodeNat mode layout.setup.scratch)) (afterSetup mode layout state).accumulator)))
      layout.setup.slot _) layout.selected _ = _
  rw [afterSetup, GuardSetupImage.saved_candidate mode layout.setup state ready.setupReady, GuardSetupImage.accumulator mode layout.setup state ready.setupReady]
  rfl

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideResume : Not (ByteMemory.Inside layout.setup.resume mode.wordBytes position))
    (outsideScratch : Not (ByteMemory.Inside layout.setup.scratch mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.setup.slot mode.wordBytes position))
    (outsideMask : Not (ByteMemory.Inside layout.mask mode.wordBytes position))
    (outsideSelected : Not (ByteMemory.Inside layout.selected mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [finish, GuardSelectionImage.memory_frame mode (selectionLayout mode layout) _ (selection_ready mode layout state ready) position outsideSelected outsideSlot,
    afterBorrow, BorrowMaskImage.memory_frame mode (borrowLayout mode layout) _ (borrow_ready mode layout state ready) position outsideScratch outsideSlot outsideMask]
  exact GuardSetupImage.memory_frame mode layout.setup state ready.setupReady position outsideResume outsideSlot outsideScratch

theorem run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    runForms mode (program mode layout state) state = finish mode layout state := (Fetch.trace_run_eq mode (trace mode layout state ready)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 86 := by
  simp only [program, List.length_append, GuardSetupImage.program_count, BorrowMaskImage.program_count, GuardSelectionImage.program_count]

end SmcTuring.Native.GuardImage
