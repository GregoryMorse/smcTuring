module
public import SmcTuring.Native.OffsetGuardImage
public import SmcTuring.Native.PointerImage

public section

namespace SmcTuring.Native.AddressImage

open Execution

/-- Both guards share the generator's control fields and helper readers.
The Base guard has its own capture entry and the opposite selector orientation.
The computed pointer is the one active operand shared by load and store. -/
structure Layout (mode : Mode) where
  offset : OffsetGuardImage.Layout mode
  baseCallee : Nat
  wordCallee : Nat
  pointerCallee : Nat
  guardStart : Nat
  baseInitial : Word mode
  wordInitial : Word mode
  base : Dolan.Mov.Register

@[expose] def pointerPosition (mode : Mode) (layout : Layout mode) : Nat := layout.pointerCallee + ReaderImage.labelOffset mode
@[expose] def pointerStart (mode : Mode) (layout : Layout mode) : Nat :=
  (OffsetGuardImage.guardLayout mode layout.offset).caller + CallsImage.totalSize mode (.relative layout.offset.guard.setup.start)
@[expose] def pointerLayout (mode : Mode) (layout : Layout mode) : PointerImage.Layout mode :=
  ⟨⟨pointerStart mode layout, layout.baseCallee, layout.offset.guard.setup.top, layout.offset.guard.setup.slot,
    layout.offset.guard.setup.origin, layout.offset.guard.setup.gridBase, layout.baseInitial, layout.offset.guard.setup.whole⟩,
    layout.offset.readerCallee, layout.wordCallee, layout.offset.readerInitial, layout.wordInitial, pointerPosition mode layout,
    layout.offset.guard.setup.candidate, layout.base, layout.offset.offset, layout.offset.cells⟩
@[expose] def baseGuard (mode : Mode) (layout : Layout mode) : GuardImage.Layout mode :=
  { layout.offset.guard with setup := { layout.offset.guard.setup with start := layout.guardStart }, sense := .base }
@[expose] def guardLayout (mode : Mode) (layout : Layout mode) : GuardInvocationImage.Layout mode :=
  ⟨PointerImage.endPosition mode (pointerLayout mode layout), baseGuard mode layout⟩
@[expose] def pointerView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (pointerStart mode layout) }
@[expose] def guardView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (guardLayout mode layout).caller }
@[expose] def afterOffset (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := OffsetGuardImage.finish mode layout.offset state
@[expose] def afterPointer (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := PointerImage.finish mode (pointerLayout mode layout) (afterOffset mode layout state)
@[expose] def acceptedFinish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := GuardInvocationImage.finish mode (guardLayout mode layout) (afterPointer mode layout state)
@[expose] def acceptedProgram (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  OffsetGuardImage.program mode layout.offset state ++ PointerImage.program mode (pointerLayout mode layout) (afterOffset mode layout state) ++
    GuardInvocationImage.program mode (guardLayout mode layout) (afterPointer mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  if SourceValues.isOffset (source.registers layout.offset.offset) then acceptedFinish mode layout state else afterOffset mode layout state
@[expose] def program (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : List (Form mode) :=
  if SourceValues.isOffset (source.registers layout.offset.offset) then acceptedProgram mode layout state else OffsetGuardImage.program mode layout.offset state
@[expose] def continuation (mode : Mode) (layout : Layout mode) : Word mode := GuardInvocationImage.callerEnd mode (guardLayout mode layout)
@[expose] def accepts {mode : Mode} (layout : Layout mode) (source : Dolan.Mov.State) : Bool :=
  (Dolan.Mov.address source layout.base layout.offset.offset).isSome

/-- Original-memory setup and separation of physical metadata only. The
second and third stages' executed setup is derived from the first guard's
actual result. In particular a rejected offset never reaches pointer setup. -/
structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  offsetSetup : OffsetGuardImage.Ready mode layout.offset state
  pointerSetup : PointerImage.Ready mode (pointerLayout mode layout) (pointerView mode layout state)
  guardSetup : GuardInvocationImage.Ready mode (guardLayout mode layout) (guardView mode layout state)
  pointerMetadataSeparate : forall observed field,
    Not (PointerImage.metadataWord mode (pointerLayout mode layout) observed = Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress layout.offset field))
  guardOffsetSeparate : forall observed field,
    Not (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed = Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress layout.offset field))
  guardPointerSeparate : forall observed field,
    Not (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed = Arithmetic.encodeNat mode (PointerImage.fieldAddress (pointerLayout mode layout) field))
  pointerSeparate : forall field, Not (Arithmetic.encodeNat mode (pointerPosition mode layout) = Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress layout.offset field))

theorem pointer_metadata_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) (observed : PointerImage.Metadata) :
    load mode (afterOffset mode layout state).memory (PointerImage.metadataWord mode (pointerLayout mode layout) observed) =
      load mode state.memory (PointerImage.metadataWord mode (pointerLayout mode layout) observed) :=
  OffsetGuardImage.load_frame mode layout.offset state ready.offsetSetup _
    (PointerImage.metadata_owned mode (pointerLayout mode layout) _ ready.pointerSetup observed) (ready.pointerMetadataSeparate observed)

theorem pointer_ready (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    PointerImage.Ready mode (pointerLayout mode layout) (afterOffset mode layout state) := by
  apply PointerImage.transport_ready mode (pointerLayout mode layout) _ _ ready.pointerSetup
  · have inside : (match source.registers layout.offset.offset with | .address cell => cell < layout.offset.cells | .offset _ => True) := by rw [offset]; trivial
    have location := OffsetGuardImage.pc mode layout.offset source state ready.offsetSetup rep inside
    simpa [afterOffset, offset, SourceValues.isOffset, OffsetGuardImage.continuation, OffsetGuardImage.guardLayout, GuardInvocationImage.callerEnd, pointerLayout, pointerStart] using location
  · exact OffsetGuardImage.finish_intact mode layout.offset state ready.offsetSetup
  · exact pointer_metadata_frame mode layout state ready

theorem guard_metadata_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) (observed : GuardInvocationImage.Metadata) :
    load mode (afterPointer mode layout state).memory (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed) =
      load mode state.memory (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed) := by
  have owned : SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase
      (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed) := GuardInvocationImage.metadata_owned mode (guardLayout mode layout) _ ready.guardSetup observed
  rw [afterPointer, PointerImage.load_frame mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset) _ owned (ready.guardPointerSeparate observed)]
  exact OffsetGuardImage.load_frame mode layout.offset state ready.offsetSetup _ owned (ready.guardOffsetSeparate observed)

theorem guard_ready (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    GuardInvocationImage.Ready mode (guardLayout mode layout) (afterPointer mode layout state) := by
  apply GuardInvocationImage.transport_ready mode (guardLayout mode layout) _ _ ready.guardSetup
  · exact PointerImage.pc mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset)
  · exact PointerImage.finish_intact mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset)
  · exact guard_metadata_frame mode layout source state ready rep choice offset

theorem candidate (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    load mode (afterPointer mode layout state).memory (Arithmetic.encodeNat mode layout.offset.guard.setup.candidate) =
      SourceValues.encodeWord mode layout.offset.guard.setup.gridBase (source.registers layout.base) + Arithmetic.encodeOffset mode choice := by
  have result := PointerImage.candidate mode (pointerLayout mode layout) source _ (pointer_ready mode layout source state ready rep choice offset)
    (OffsetGuardImage.represented mode layout.offset source state ready.offsetSetup rep)
  change load mode (afterPointer mode layout state).memory (Arithmetic.encodeNat mode layout.offset.guard.setup.candidate) =
    SourceValues.encodeWord mode layout.offset.guard.setup.gridBase (source.registers layout.base) + SourceValues.encodeWord mode layout.offset.guard.setup.gridBase (source.registers layout.offset.offset) at result
  rw [offset] at result
  exact result

theorem boundary (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    load mode (afterPointer mode layout state).memory (Arithmetic.encodeNat mode layout.offset.guard.setup.boundary) =
      Arithmetic.encodeNat mode (Native.Layout.heapBase mode layout.offset.guard.setup.gridBase) :=
  (guard_metadata_frame mode layout source state ready rep choice offset .boundary).trans ready.offsetSetup.boundary

theorem terminal (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    load mode (afterPointer mode layout state).memory (Arithmetic.encodeNat mode layout.offset.guard.terminal) =
      load mode state.memory (Arithmetic.encodeNat mode layout.offset.guard.terminal) :=
  guard_metadata_frame mode layout source state ready rep choice offset .terminal

theorem accepted_pc (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice)
    (inside : match source.registers layout.base with | .address cell => cell < layout.offset.cells | .offset _ => True) :
    (acceptedFinish mode layout state).pc = if SourceValues.accepts .base (source.registers layout.base) then continuation mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.offset.guard.terminal) := by
  have result := SourceValues.address_guard_pc mode (guardLayout mode layout) layout.offset.guard.setup.gridBase _ (source.registers layout.base) choice
    (guard_ready mode layout source state ready rep choice offset) rfl (candidate mode layout source state ready rep choice offset)
    (boundary mode layout source state ready rep choice offset)
    (SourceData.boundary_fits mode layout.offset.guard.setup.gridBase layout.offset.cells ready.offsetSetup.capacity ready.offsetSetup.positive)
    (SourceData.address_fits mode layout.offset.guard.setup.gridBase layout.offset.cells (source.registers layout.base) choice ready.offsetSetup.capacity inside)
  change (acceptedFinish mode layout state).pc = if SourceValues.accepts .base (source.registers layout.base) then continuation mode layout
    else load mode (afterPointer mode layout state).memory (Arithmetic.encodeNat mode layout.offset.guard.terminal) at result
  rw [terminal mode layout source state ready rep choice offset] at result
  exact result

theorem pc (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (offsetInside : match source.registers layout.offset.offset with | .address cell => cell < layout.offset.cells | .offset _ => True)
    (baseInside : match source.registers layout.base with | .address cell => cell < layout.offset.cells | .offset _ => True) :
    (finish mode layout source state).pc = if accepts layout source then continuation mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.offset.guard.terminal) := by
  cases offset : source.registers layout.offset.offset with
  | address cell =>
    have result := OffsetGuardImage.pc mode layout.offset source state ready.offsetSetup rep offsetInside
    simpa [finish, afterOffset, offset, SourceValues.isOffset, accepts, Dolan.Mov.address] using result
  | offset choice =>
    have result := accepted_pc mode layout source state ready rep choice offset baseInside
    cases base : source.registers layout.base <;>
      simpa [finish, offset, base, SourceValues.isOffset, SourceValues.accepts, accepts, Dolan.Mov.address] using result

theorem accepted_trace (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    Fetch.Trace mode state (acceptedProgram mode layout state) (acceptedFinish mode layout state) :=
  Fetch.trace_append mode (Fetch.trace_append mode (OffsetGuardImage.trace mode layout.offset state ready.offsetSetup)
    (PointerImage.trace mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset)))
    (GuardInvocationImage.trace mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset))

theorem trace (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    Fetch.Trace mode state (program mode layout source state) (finish mode layout source state) := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [program, finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.trace mode layout.offset state ready.offsetSetup
  | offset choice => simpa [program, finish, offset, SourceValues.isOffset] using accepted_trace mode layout source state ready rep choice offset

theorem accepted_owned_run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase)
      (acceptedProgram mode layout state) state := by
  have firstRun : runForms mode (OffsetGuardImage.program mode layout.offset state) state = afterOffset mode layout state := OffsetGuardImage.run mode layout.offset state ready.offsetSetup
  have prefixRun : runForms mode (OffsetGuardImage.program mode layout.offset state ++ PointerImage.program mode (pointerLayout mode layout) (afterOffset mode layout state)) state = afterPointer mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (OffsetGuardImage.trace mode layout.offset state ready.offsetSetup)
      (PointerImage.trace mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset)))).symm
  rw [acceptedProgram, Writes.owned_run_append, prefixRun, Writes.owned_run_append, firstRun]
  exact ⟨⟨OffsetGuardImage.owned_run mode layout.offset state ready.offsetSetup,
    PointerImage.owned_run mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset)⟩,
    GuardInvocationImage.owned_run mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset)⟩

theorem owned_run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase)
      (program mode layout source state) state := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [program, offset, SourceValues.isOffset] using OffsetGuardImage.owned_run mode layout.offset state ready.offsetSetup
  | offset choice => simpa [program, offset, SourceValues.isOffset] using accepted_owned_run mode layout source state ready rep choice offset

theorem accepted_data_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase observed)
    (above : layout.offset.guard.setup.gridBase <= observed.toNat) :
    load mode (acceptedFinish mode layout state).memory observed = load mode (afterPointer mode layout state).memory observed :=
  GuardInvocationImage.load_frame mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset) observed owned
    (OffsetGuardImage.data_not_field mode layout.offset state ready.offsetSetup observed above .resume)
    (OffsetGuardImage.data_not_field mode layout.offset state ready.offsetSetup observed above .scratch)
    (OffsetGuardImage.data_not_field mode layout.offset state ready.offsetSetup observed above .slot)
    (OffsetGuardImage.data_not_field mode layout.offset state ready.offsetSetup observed above .mask)
    (OffsetGuardImage.data_not_field mode layout.offset state ready.offsetSetup observed above .selected)

theorem accepted_represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (choice : Bool) (offset : source.registers layout.offset.offset = .offset choice) :
    SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source (acceptedFinish mode layout state).memory := by
  have pointerRep := PointerImage.represented mode (pointerLayout mode layout) source _ (pointer_ready mode layout source state ready rep choice offset)
    (OffsetGuardImage.represented mode layout.offset source state ready.offsetSetup rep)
  constructor
  · intro register
    rw [accepted_data_frame mode layout source state ready rep choice offset _
      (SourceData.register_owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase layout.offset.cells register ready.offsetSetup.capacity)
      (by rw [SourceData.register_toNat mode layout.offset.guard.setup.gridBase layout.offset.cells register ready.offsetSetup.capacity]; exact Nat.le_add_right _ _)]
    exact pointerRep.registers register
  · intro position inside
    rw [accepted_data_frame mode layout source state ready rep choice offset _
      (SourceData.heap_owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase layout.offset.cells position ready.offsetSetup.capacity inside)
      (by rw [SourceData.heap_toNat mode layout.offset.guard.setup.gridBase layout.offset.cells position ready.offsetSetup.capacity inside]; exact Nat.le_add_right _ _)]
    exact pointerRep.heap position inside

theorem represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source (finish mode layout source state).memory := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.represented mode layout.offset source state ready.offsetSetup rep
  | offset choice => simpa [finish, offset, SourceValues.isOffset] using accepted_represented mode layout source state ready rep choice offset

theorem pointer (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (position : Nat × Bool) (valid : Dolan.Mov.address source layout.base layout.offset.offset = some position) :
    load mode (finish mode layout source state).memory (ReaderImage.label mode layout.pointerCallee) = SourceData.heapWord mode layout.offset.guard.setup.gridBase position := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simp [Dolan.Mov.address, offset] at valid
  | offset choice =>
    have owned : SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase
        (Arithmetic.encodeNat mode (pointerPosition mode layout)) := ready.pointerSetup.baseSetup.scalarSetup.owned
    have frame := GuardInvocationImage.load_frame mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset) _ owned
      (ready.pointerSeparate .resume) (ready.pointerSeparate .scratch) (ready.pointerSeparate .slot) (ready.pointerSeparate .mask) (ready.pointerSeparate .selected)
    have pointerValue := PointerImage.source_address mode (pointerLayout mode layout) source _ (pointer_ready mode layout source state ready rep choice offset)
      (OffsetGuardImage.represented mode layout.offset source state ready.offsetSetup rep) position valid
    simpa [finish, offset, SourceValues.isOffset, acceptedFinish, ReaderImage.label, pointerPosition, pointerLayout] using frame.trans pointerValue

theorem finish_intact (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    SpacedCombinedImage.Intact mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase (finish mode layout source state).memory := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.finish_intact mode layout.offset state ready.offsetSetup
  | offset choice => simpa [finish, acceptedFinish, guardLayout, baseGuard, offset, SourceValues.isOffset] using GuardInvocationImage.finish_intact mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset)

theorem carry (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) : (finish mode layout source state).carry = false := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.carry mode layout.offset state ready.offsetSetup
  | offset choice => simpa [finish, acceptedFinish, offset, SourceValues.isOffset] using GuardInvocationImage.carry mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset)

/-- The complete address prefix writes only the six guard fields and the
single shared pointer operand; other owned metadata remains available. -/
inductive Field where | control (field : OffsetGuardImage.Field) | pointer deriving DecidableEq
@[expose] def fieldAddress {mode : Mode} (layout : Layout mode) : Field -> Nat
  | .control field => OffsetGuardImage.fieldAddress layout.offset field
  | .pointer => pointerPosition mode layout

theorem load_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase observed)
    (different : forall field, Not (observed = Arithmetic.encodeNat mode (fieldAddress layout field))) :
    load mode (finish mode layout source state).memory observed = load mode state.memory observed := by
  cases offset : source.registers layout.offset.offset with
  | address cell =>
    simpa [finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.load_frame mode layout.offset state ready.offsetSetup observed owned (fun field => different (.control field))
  | offset choice =>
    have guardFrame := GuardInvocationImage.load_frame mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset) observed owned
      (different (.control .resume)) (different (.control .scratch)) (different (.control .slot)) (different (.control .mask)) (different (.control .selected))
    have pointerDifferent : forall field, Not (observed = Arithmetic.encodeNat mode (PointerImage.fieldAddress (pointerLayout mode layout) field)) := by
      intro field
      cases field with
      | pointer => exact different .pointer
      | candidate => exact different (.control .candidate)
      | slot => exact different (.control .slot)
    have pointerFrame := PointerImage.load_frame mode (pointerLayout mode layout) _ (pointer_ready mode layout source state ready rep choice offset) observed owned pointerDifferent
    have offsetFrame := OffsetGuardImage.load_frame mode layout.offset state ready.offsetSetup observed owned (fun field => different (.control field))
    simpa [finish, acceptedFinish, offset, SourceValues.isOffset] using guardFrame.trans (pointerFrame.trans offsetFrame)

theorem top_reusable (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    load mode (finish mode layout source state).memory (Arithmetic.encodeNat mode layout.offset.guard.setup.top) =
      Arithmetic.encodeNat mode layout.offset.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  have different : forall field, Not (Arithmetic.encodeNat mode layout.offset.guard.setup.top = Arithmetic.encodeNat mode (fieldAddress layout field)) := by
    intro field
    cases field with
    | control field => exact ready.pointerMetadataSeparate .top field
    | pointer => exact ready.pointerSetup.metadataDifferent .top .pointer
  have owned : SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase
      (Arithmetic.encodeNat mode layout.offset.guard.setup.top) := ready.offsetSetup.readSetup.readReady.topOwned
  rw [load_frame mode layout source state ready rep (Arithmetic.encodeNat mode layout.offset.guard.setup.top) owned different]
  exact ready.offsetSetup.readSetup.readReady.topValue

theorem stack (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    (finish mode layout source state).stack = Arithmetic.encodeNat mode layout.offset.guard.setup.slot := by
  cases offset : source.registers layout.offset.offset with
  | address cell => simpa [finish, afterOffset, offset, SourceValues.isOffset] using OffsetGuardImage.stack mode layout.offset state ready.offsetSetup
  | offset choice => simpa [finish, acceptedFinish, guardLayout, baseGuard, offset, SourceValues.isOffset] using GuardInvocationImage.stack mode (guardLayout mode layout) _ (guard_ready mode layout source state ready rep choice offset)

theorem run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory) :
    runForms mode (program mode layout source state) state = finish mode layout source state := (Fetch.trace_run_eq mode (trace mode layout source state ready rep)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) :
    (program mode layout source state).length = if SourceValues.isOffset (source.registers layout.offset.offset) then 222 else 100 := by
  cases offset : source.registers layout.offset.offset <;>
    simp [program, acceptedProgram, offset, SourceValues.isOffset, OffsetGuardImage.program_count, PointerImage.program_count, GuardInvocationImage.program_count]

structure Spec (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (start stop : State mode) : Prop where
  represented : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source stop.memory
  trace : Fetch.Trace mode start (program mode layout source start) stop
  owned : Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase) (program mode layout source start) start
  pc : stop.pc = if accepts layout source then continuation mode layout else load mode start.memory (Arithmetic.encodeNat mode layout.offset.guard.terminal)
  pointer : forall position, Dolan.Mov.address source layout.base layout.offset.offset = some position ->
    load mode stop.memory (ReaderImage.label mode layout.pointerCallee) = SourceData.heapWord mode layout.offset.guard.setup.gridBase position
  intact : SpacedCombinedImage.Intact mode layout.offset.guard.setup.whole layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase stop.memory
  carry : stop.carry = false
  stack : stop.stack = Arithmetic.encodeNat mode layout.offset.guard.setup.slot
  top : load mode stop.memory (Arithmetic.encodeNat mode layout.offset.guard.setup.top) = Arithmetic.encodeNat mode layout.offset.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes

theorem correct (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.offset.guard.setup.gridBase layout.offset.cells source state.memory)
    (offsetInside : match source.registers layout.offset.offset with | .address cell => cell < layout.offset.cells | .offset _ => True)
    (baseInside : match source.registers layout.base with | .address cell => cell < layout.offset.cells | .offset _ => True) :
    Spec mode layout source state (finish mode layout source state) :=
  ⟨represented mode layout source state ready rep, trace mode layout source state ready rep, owned_run mode layout source state ready rep,
    pc mode layout source state ready rep offsetInside baseInside, pointer mode layout source state ready rep,
    finish_intact mode layout source state ready rep, carry mode layout source state ready rep,
    stack mode layout source state ready rep, top_reusable mode layout source state ready rep⟩

end SmcTuring.Native.AddressImage
