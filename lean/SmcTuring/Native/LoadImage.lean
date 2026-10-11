module
public import SmcTuring.Native.AddressImage
public import SmcTuring.Native.SourceWriteImage

public section

namespace SmcTuring.Native.LoadImage

open Execution

structure Layout (mode : Mode) where
  address : AddressImage.Layout mode
  destination : Dolan.Mov.Register
  pointerInitial : Word mode

@[expose] def readStart (mode : Mode) (layout : Layout mode) : Nat :=
  (AddressImage.guardLayout mode layout.address).caller + CallsImage.totalSize mode (.relative layout.address.guardStart)
@[expose] def readLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  ⟨⟨readStart mode layout, layout.address.pointerCallee, layout.address.offset.guard.setup.top, layout.address.offset.guard.setup.slot,
    layout.address.offset.guard.setup.origin, layout.address.offset.guard.setup.gridBase, layout.pointerInitial, layout.address.offset.guard.setup.whole⟩,
    SourceData.registerAddress mode layout.address.offset.guard.setup.gridBase layout.destination⟩
@[expose] def readView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (readStart mode layout) }
@[expose] def afterAddress (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  AddressImage.finish mode layout.address source state
@[expose] def sourceResult {mode : Mode} (layout : Layout mode) (source : Dolan.Mov.State) : Dolan.Mov.State :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => source
  | some position => SourceWriteImage.registerResult source layout.destination (source.memory position)
@[expose] def finish (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => afterAddress mode layout source state
  | some _ => ReadScalarImage.finish mode .store (readLayout mode layout) (afterAddress mode layout source state)
@[expose] def program (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : List (Form mode) :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => AddressImage.program mode layout.address source state
  | some _ => AddressImage.program mode layout.address source state ++
      ReadScalarImage.program mode .store (readLayout mode layout) (afterAddress mode layout source state)
@[expose] def continuation (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (ReadScalarImage.endPosition mode .store (readLayout mode layout))

/-- Both setups refer to original memory; the actual reader setup is derived
from the guarded address result and its owned selected heap field. -/
structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  addressSetup : AddressImage.Ready mode layout.address state
  readSetup : ReadScalarImage.Ready mode .store (readLayout mode layout) (readView mode layout state)

structure Bounds (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) : Prop where
  offsetInside : match source.registers layout.address.offset.offset with | .address cell => cell < layout.address.offset.cells | .offset _ => True
  baseInside : match source.registers layout.address.base with | .address cell => cell < layout.address.offset.cells | .offset _ => True

private theorem address_tags (source : Dolan.Mov.State) (base offset : Dolan.Mov.Register) (position : Prod Nat Bool)
    (valid : Dolan.Mov.address source base offset = some position) :
    source.registers base = .address position.1 ∧ source.registers offset = .offset position.2 := by
  cases baseValue : source.registers base with
  | offset choice => simp [Dolan.Mov.address, baseValue] at valid
  | address cell =>
    cases offsetValue : source.registers offset with
    | address other => simp [Dolan.Mov.address, baseValue, offsetValue] at valid
    | offset choice =>
      have same : (cell, choice) = position := Option.some.inj (by simpa [Dolan.Mov.address, baseValue, offsetValue] using valid)
      subst position
      exact ⟨rfl, rfl⟩

theorem pointer_inside (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (bounds : Bounds mode layout source)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    position.1 < layout.address.offset.cells := by
  have tags := address_tags source layout.address.base layout.address.offset.offset position valid
  simpa [tags.1] using bounds.baseInside

theorem read_ready (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    ReadScalarImage.Ready mode .store (readLayout mode layout) (afterAddress mode layout source state) := by
  apply ReadScalarImage.transport_ready_pointer mode .store (readLayout mode layout) _ _ ready.readSetup
  · have location := AddressImage.pc mode layout.address source state ready.addressSetup rep bounds.offsetInside bounds.baseInside
    simpa [afterAddress, AddressImage.accepts, valid, readLayout, readStart, AddressImage.continuation,
      GuardInvocationImage.callerEnd, AddressImage.guardLayout, AddressImage.baseGuard] using location
  · exact AddressImage.finish_intact mode layout.address source state ready.addressSetup rep
  · exact (AddressImage.top_reusable mode layout.address source state ready.addressSetup rep).trans ready.readSetup.readReady.topValue.symm
  · change SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin
      layout.address.offset.guard.setup.gridBase (load mode (afterAddress mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee))
    rw [afterAddress, AddressImage.pointer mode layout.address source state ready.addressSetup rep position valid]
    exact SourceData.heap_owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin
      layout.address.offset.guard.setup.gridBase layout.address.offset.cells position ready.addressSetup.offsetSetup.capacity
      (pointer_inside mode layout source bounds position valid)

theorem read_value (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position)
    (inside : position.1 < layout.address.offset.cells) :
    ReadScalarImage.readValue mode (readLayout mode layout) (afterAddress mode layout source state) =
      SourceValues.encodeWord mode layout.address.offset.guard.setup.gridBase (source.memory position) := by
  have points : load mode (afterAddress mode layout source state).memory (ReaderImage.label mode (readLayout mode layout).reader.callee) =
      SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position :=
    AddressImage.pointer mode layout.address source state ready.addressSetup rep position valid
  have notSlot := SourceData.heap_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells
    layout.address.offset.guard.setup.slot position ready.addressSetup.offsetSetup.capacity inside ready.readSetup.readReady.slotFits
    (ready.addressSetup.offsetSetup.fieldsBefore .slot)
  rw [ReadScalarImage.read_value_from mode (readLayout mode layout) _ _ points notSlot]
  exact (AddressImage.represented mode layout.address source state ready.addressSetup rep).heap position inside

theorem source_step (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) :
    Dolan.Mov.execute (.load layout.destination layout.address.base layout.address.offset.offset) source =
      if AddressImage.accepts layout.address source then some (sourceResult layout source) else none := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset <;>
    simp [Dolan.Mov.execute, sourceResult, AddressImage.accepts, valid, SourceWriteImage.registerResult]

theorem represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells (sourceResult layout source) (finish mode layout source state).memory := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, sourceResult, valid, afterAddress] using AddressImage.represented mode layout.address source state ready.addressSetup rep
  | some position =>
    have result := SourceWriteImage.register_rep mode (readLayout mode layout) layout.address.offset.cells layout.destination (source.memory position) source _
      (read_ready mode layout source state ready bounds rep position valid) ready.addressSetup.offsetSetup.capacity
      (ready.addressSetup.offsetSetup.fieldsBefore .slot) rfl
      (read_value mode layout source state ready rep position valid (pointer_inside mode layout source bounds position valid))
      (AddressImage.represented mode layout.address source state ready.addressSetup rep)
    simpa [finish, sourceResult, valid, readLayout] using result

theorem trace (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    Fetch.Trace mode state (program mode layout source state) (finish mode layout source state) := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [program, finish, valid, afterAddress] using AddressImage.trace mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [program, finish, valid, afterAddress] using Fetch.trace_append mode (AddressImage.trace mode layout.address source state ready.addressSetup rep)
      (ReadScalarImage.trace mode .store (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid))

theorem owned_run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase)
      (program mode layout source state) state := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [program, valid] using AddressImage.owned_run mode layout.address source state ready.addressSetup rep
  | some position =>
    have firstRun : runForms mode (AddressImage.program mode layout.address source state) state = afterAddress mode layout source state :=
      AddressImage.run mode layout.address source state ready.addressSetup rep
    rw [program, valid, Writes.owned_run_append, firstRun]
    exact ⟨AddressImage.owned_run mode layout.address source state ready.addressSetup rep,
      ReadScalarImage.owned_run mode .store (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)⟩

theorem pc (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).pc = if AddressImage.accepts layout.address source then continuation mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, AddressImage.accepts, valid] using AddressImage.pc mode layout.address source state ready.addressSetup rep bounds.offsetInside bounds.baseInside
  | some position =>
    simpa [finish, continuation, AddressImage.accepts, valid] using ReadScalarImage.pc mode .store (readLayout mode layout) _
      (read_ready mode layout source state ready bounds rep position valid)

theorem finish_intact (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    SpacedCombinedImage.Intact mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase
      (finish mode layout source state).memory := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.finish_intact mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, valid, readLayout] using ReadScalarImage.finish_intact mode .store (readLayout mode layout) _
      (read_ready mode layout source state ready bounds rep position valid)

theorem top_reusable (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    load mode (finish mode layout source state).memory (Arithmetic.encodeNat mode layout.address.offset.guard.setup.top) =
      Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.top_reusable mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, valid, readLayout] using ReadScalarImage.top_reusable mode .store (readLayout mode layout) _
      (read_ready mode layout source state ready bounds rep position valid)

theorem stack (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).stack = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.stack mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, valid, readLayout] using ReadScalarImage.stack mode .store (readLayout mode layout) _
      (read_ready mode layout source state ready bounds rep position valid)

theorem carry (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).carry = false := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.carry mode layout.address source state ready.addressSetup rep
  | some position =>
    have frame := ReadScalarImage.carry mode .store (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)
    change (ReadScalarImage.finish mode .store (readLayout mode layout) (afterAddress mode layout source state)).carry =
      (afterAddress mode layout source state).carry at frame
    have result := frame.trans (AddressImage.carry mode layout.address source state ready.addressSetup rep)
    simpa [finish, valid] using result

/-- The final reader/update additionally writes the destination register.
Other owned metadata outside it and the seven address-stage fields is framed. -/
inductive Field where | address (field : AddressImage.Field) | destination deriving DecidableEq
@[expose] def fieldAddress {mode : Mode} (layout : Layout mode) : Field -> Nat
  | .address field => AddressImage.fieldAddress layout.address field
  | .destination => SourceData.registerAddress mode layout.address.offset.guard.setup.gridBase layout.destination

theorem load_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase observed)
    (different : forall field, Not (observed = Arithmetic.encodeNat mode (fieldAddress layout field))) :
    load mode (finish mode layout source state).memory observed = load mode state.memory observed := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.load_frame mode layout.address source state ready.addressSetup rep observed owned (fun field => different (.address field))
  | some position =>
    have readFrame := ReadScalarImage.load_frame mode .store (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid) observed owned
      (different .destination) (different (.address (.control .slot)))
    have addressFrame := AddressImage.load_frame mode layout.address source state ready.addressSetup rep observed owned (fun field => different (.address field))
    simpa [finish, valid] using readFrame.trans addressFrame

theorem run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    runForms mode (program mode layout source state) state = finish mode layout source state :=
  (Fetch.trace_run_eq mode (trace mode layout source state ready bounds rep)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) :
    (program mode layout source state).length = if AddressImage.accepts layout.address source then 233
      else if SourceValues.isOffset (source.registers layout.address.offset.offset) then 222 else 100 := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simp [program, valid, AddressImage.accepts, AddressImage.program_count]
  | some position =>
    have tags := address_tags source layout.address.base layout.address.offset.offset position valid
    simp [program, valid, AddressImage.accepts, AddressImage.program_count, ReadScalarImage.program_count, tags.2, SourceValues.isOffset]

structure Spec (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (start stop : State mode) : Prop where
  sourceStep : Dolan.Mov.execute (.load layout.destination layout.address.base layout.address.offset.offset) source =
    if AddressImage.accepts layout.address source then some (sourceResult layout source) else none
  represented : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells (sourceResult layout source) stop.memory
  trace : Fetch.Trace mode start (program mode layout source start) stop
  owned : Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase) (program mode layout source start) start
  pc : stop.pc = if AddressImage.accepts layout.address source then continuation mode layout else load mode start.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal)
  intact : SpacedCombinedImage.Intact mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase stop.memory
  top : load mode stop.memory (Arithmetic.encodeNat mode layout.address.offset.guard.setup.top) = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes
  stack : stop.stack = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot
  carry : stop.carry = false

theorem correct (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    Spec mode layout source state (finish mode layout source state) :=
  ⟨source_step mode layout source, represented mode layout source state ready bounds rep, trace mode layout source state ready bounds rep,
    owned_run mode layout source state ready bounds rep, pc mode layout source state ready bounds rep,
    finish_intact mode layout source state ready bounds rep, top_reusable mode layout source state ready bounds rep,
    stack mode layout source state ready bounds rep, carry mode layout source state ready bounds rep⟩

end SmcTuring.Native.LoadImage
