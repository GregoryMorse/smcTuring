module
public import SmcTuring.Native.AddressImage
public import SmcTuring.Native.SourceWriteImage

public section

namespace SmcTuring.Native.StoreImage

open Execution

structure Layout (mode : Mode) where
  address : AddressImage.Layout mode
  source : Dolan.Mov.Register
  readerCallee : Nat
  readerInitial : Word mode
  pointerInitial : Word mode

@[expose] def readStart (mode : Mode) (layout : Layout mode) : Nat :=
  (AddressImage.guardLayout mode layout.address).caller + CallsImage.totalSize mode (.relative layout.address.guardStart)
@[expose] def readLayout (mode : Mode) (layout : Layout mode) : ReadInvocationImage.Layout mode :=
  ⟨readStart mode layout, layout.readerCallee, layout.address.offset.guard.setup.top, layout.address.offset.guard.setup.slot,
    layout.address.offset.guard.setup.origin, layout.address.offset.guard.setup.gridBase, layout.readerInitial, layout.address.offset.guard.setup.whole⟩
@[expose] def storeLayout (mode : Mode) (layout : Layout mode) : StoreInvocationImage.Layout mode :=
  ⟨readStart mode layout + CallsImage.totalSize mode (.relative layout.readerCallee), layout.address.pointerCallee,
    layout.address.offset.guard.setup.top, layout.address.offset.guard.setup.slot, layout.address.offset.guard.setup.origin,
    layout.address.offset.guard.setup.gridBase, layout.pointerInitial, layout.address.offset.guard.setup.whole⟩
@[expose] def readView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (readStart mode layout) }
@[expose] def storeView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (storeLayout mode layout).caller }
@[expose] def afterAddress (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  AddressImage.finish mode layout.address source state
@[expose] def afterRead (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  ReadInvocationImage.finish mode (readLayout mode layout) (afterAddress mode layout source state)
@[expose] def acceptedFinish (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  StoreInvocationImage.finish mode (storeLayout mode layout) (afterRead mode layout source state)
@[expose] def acceptedProgram (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : List (Form mode) :=
  AddressImage.program mode layout.address source state ++ ReadInvocationImage.program mode (readLayout mode layout) (afterAddress mode layout source state) ++
    StoreInvocationImage.program mode (storeLayout mode layout) (afterRead mode layout source state)
@[expose] def sourceResult {mode : Mode} (layout : Layout mode) (source : Dolan.Mov.State) : Dolan.Mov.State :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => source
  | some position => SourceWriteImage.heapResult source position (source.registers layout.source)
@[expose] def finish (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => afterAddress mode layout source state
  | some _ => acceptedFinish mode layout source state
@[expose] def program (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) : List (Form mode) :=
  match Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => AddressImage.program mode layout.address source state
  | some _ => acceptedProgram mode layout source state
@[expose] def continuation (mode : Mode) (layout : Layout mode) : Word mode := StoreInvocationImage.callerEnd mode (storeLayout mode layout)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  addressSetup : AddressImage.Ready mode layout.address state
  readSetup : ReadInvocationImage.Ready mode (readLayout mode layout) (readView mode layout state)
  storeSetup : StoreInvocationImage.Ready mode (storeLayout mode layout) (storeView mode layout state)
  sourcePointer : load mode state.memory (ReaderImage.label mode layout.readerCallee) = SourceData.registerWord mode layout.address.offset.guard.setup.gridBase layout.source
  sourceLabelSeparate : forall field, Not (ReaderImage.label mode layout.readerCallee = Arithmetic.encodeNat mode (AddressImage.fieldAddress layout.address field))
  topBefore : layout.address.offset.guard.setup.top < layout.address.offset.guard.setup.gridBase

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

theorem source_label_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    load mode (afterAddress mode layout source state).memory (ReaderImage.label mode layout.readerCallee) =
      load mode state.memory (ReaderImage.label mode layout.readerCallee) :=
  AddressImage.load_frame mode layout.address source state ready.addressSetup rep _
    (ReadInvocationImage.label_owned mode (readLayout mode layout) _ ready.readSetup) ready.sourceLabelSeparate

theorem read_ready (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    ReadInvocationImage.Ready mode (readLayout mode layout) (afterAddress mode layout source state) := by
  apply ReadInvocationImage.transport_ready mode (readLayout mode layout) _ _ ready.readSetup
  · have location := AddressImage.pc mode layout.address source state ready.addressSetup rep bounds.offsetInside bounds.baseInside
    simpa [afterAddress, AddressImage.accepts, valid, readLayout, readStart, AddressImage.continuation,
      GuardInvocationImage.callerEnd, AddressImage.guardLayout, AddressImage.baseGuard] using location
  · exact AddressImage.finish_intact mode layout.address source state ready.addressSetup rep
  · exact (AddressImage.top_reusable mode layout.address source state ready.addressSetup rep).trans ready.readSetup.topValue.symm
  · exact source_label_frame mode layout source state ready rep

theorem read_value (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    (afterRead mode layout source state).accumulator = SourceValues.encodeWord mode layout.address.offset.guard.setup.gridBase (source.registers layout.source) := by
  have points := (source_label_frame mode layout source state ready rep).trans ready.sourcePointer
  have notSlot := SourceData.register_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells
    layout.address.offset.guard.setup.slot layout.source ready.addressSetup.offsetSetup.capacity ready.readSetup.slotFits
    (ready.addressSetup.offsetSetup.fieldsBefore .slot)
  rw [afterRead, ReadInvocationImage.accumulator mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)]
  change (if load mode (afterAddress mode layout source state).memory (ReaderImage.label mode layout.readerCallee) = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot
    then _ else load mode (afterAddress mode layout source state).memory (load mode (afterAddress mode layout source state).memory (ReaderImage.label mode layout.readerCallee))) = _
  rw [points, ite_eq_right notSlot]
  exact (AddressImage.represented mode layout.address source state ready.addressSetup rep).registers layout.source

theorem pointer_after_read (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    load mode (afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee) =
      SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position := by
  have owned : SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase
      (ReaderImage.label mode layout.address.pointerCallee) := StoreInvocationImage.label_owned mode (storeLayout mode layout) _ ready.storeSetup
  have frame := ReadInvocationImage.load_frame mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid) _ owned ready.storeSetup.labelDifferentSlot
  exact frame.trans (AddressImage.pointer mode layout.address source state ready.addressSetup rep position valid)

theorem store_ready (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    StoreInvocationImage.Ready mode (storeLayout mode layout) (afterRead mode layout source state) := by
  apply StoreInvocationImage.transport_ready_pointer mode (storeLayout mode layout) _ _ ready.storeSetup
  · exact ReadInvocationImage.return_pc mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)
  · exact ReadInvocationImage.finish_intact mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)
  · exact (ReadInvocationImage.top_reusable mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)).trans ready.storeSetup.topValue.symm
  · change SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase
      (load mode (afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee))
    rw [pointer_after_read mode layout source state ready bounds rep position valid]
    exact SourceData.heap_owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase
      layout.address.offset.cells position ready.addressSetup.offsetSetup.capacity (pointer_inside mode layout source bounds position valid)
  · change Not (load mode (afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee) = Arithmetic.encodeNat mode layout.address.offset.guard.setup.top)
    rw [pointer_after_read mode layout source state ready bounds rep position valid]
    exact SourceData.heap_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells layout.address.offset.guard.setup.top
      position ready.addressSetup.offsetSetup.capacity (pointer_inside mode layout source bounds position valid)
      (SourceData.metadata_fits mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells _ ready.addressSetup.offsetSetup.capacity ready.topBefore) ready.topBefore
  · change Not (load mode (afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee) = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot)
    rw [pointer_after_read mode layout source state ready bounds rep position valid]
    exact SourceData.heap_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells layout.address.offset.guard.setup.slot
      position ready.addressSetup.offsetSetup.capacity (pointer_inside mode layout source bounds position valid) ready.storeSetup.slotFits (ready.addressSetup.offsetSetup.fieldsBefore .slot)

theorem after_read_represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source (afterRead mode layout source state).memory := by
  have addressRep := AddressImage.represented mode layout.address source state ready.addressSetup rep
  constructor
  · intro register
    rw [afterRead, ReadInvocationImage.load_frame mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid) _
      (SourceData.register_owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase layout.address.offset.cells register ready.addressSetup.offsetSetup.capacity)
      (SourceData.register_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells layout.address.offset.guard.setup.slot register
        ready.addressSetup.offsetSetup.capacity ready.readSetup.slotFits (ready.addressSetup.offsetSetup.fieldsBefore .slot))]
    exact addressRep.registers register
  · intro observed inside
    rw [afterRead, ReadInvocationImage.load_frame mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid) _
      (SourceData.heap_owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase layout.address.offset.cells observed ready.addressSetup.offsetSetup.capacity inside)
      (SourceData.heap_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells layout.address.offset.guard.setup.slot observed
        ready.addressSetup.offsetSetup.capacity inside ready.readSetup.slotFits (ready.addressSetup.offsetSetup.fieldsBefore .slot))]
    exact addressRep.heap observed inside

theorem source_step (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) :
    Dolan.Mov.execute (.store layout.address.base layout.address.offset.offset layout.source) source =
      if AddressImage.accepts layout.address source then some (sourceResult layout source) else none := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset <;>
    simp [Dolan.Mov.execute, sourceResult, AddressImage.accepts, valid, SourceWriteImage.heapResult]

theorem represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells (sourceResult layout source) (finish mode layout source state).memory := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, sourceResult, valid, afterAddress] using AddressImage.represented mode layout.address source state ready.addressSetup rep
  | some position =>
    have result := SourceWriteImage.heap_rep mode (storeLayout mode layout) layout.address.offset.cells position (source.registers layout.source) source _
      (store_ready mode layout source state ready bounds rep position valid) ready.addressSetup.offsetSetup.capacity (pointer_inside mode layout source bounds position valid)
      (ready.addressSetup.offsetSetup.fieldsBefore .slot) (pointer_after_read mode layout source state ready bounds rep position valid)
      (read_value mode layout source state ready bounds rep position valid) (after_read_represented mode layout source state ready bounds rep position valid)
    simpa [finish, acceptedFinish, sourceResult, valid, storeLayout] using result

theorem accepted_trace (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    Fetch.Trace mode state (acceptedProgram mode layout source state) (acceptedFinish mode layout source state) :=
  Fetch.trace_append mode (Fetch.trace_append mode (AddressImage.trace mode layout.address source state ready.addressSetup rep)
    (ReadInvocationImage.trace mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)))
    (StoreInvocationImage.trace mode (storeLayout mode layout) _ (store_ready mode layout source state ready bounds rep position valid))

theorem trace (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    Fetch.Trace mode state (program mode layout source state) (finish mode layout source state) := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [program, finish, valid, afterAddress] using AddressImage.trace mode layout.address source state ready.addressSetup rep
  | some position => simpa [program, finish, valid] using accepted_trace mode layout source state ready bounds rep position valid

theorem accepted_owned_run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Prod Nat Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase)
      (acceptedProgram mode layout source state) state := by
  have firstRun : runForms mode (AddressImage.program mode layout.address source state) state = afterAddress mode layout source state :=
    AddressImage.run mode layout.address source state ready.addressSetup rep
  have prefixRun : runForms mode (AddressImage.program mode layout.address source state ++ ReadInvocationImage.program mode (readLayout mode layout) (afterAddress mode layout source state)) state =
      afterRead mode layout source state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (AddressImage.trace mode layout.address source state ready.addressSetup rep)
      (ReadInvocationImage.trace mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)))).symm
  rw [acceptedProgram, Writes.owned_run_append, prefixRun, Writes.owned_run_append, firstRun]
  exact ⟨⟨AddressImage.owned_run mode layout.address source state ready.addressSetup rep,
    ReadInvocationImage.owned_run mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)⟩,
    StoreInvocationImage.owned_run mode (storeLayout mode layout) _ (store_ready mode layout source state ready bounds rep position valid)⟩

theorem owned_run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase)
      (program mode layout source state) state := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [program, valid] using AddressImage.owned_run mode layout.address source state ready.addressSetup rep
  | some position => simpa [program, valid] using accepted_owned_run mode layout source state ready bounds rep position valid

theorem pc (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).pc = if AddressImage.accepts layout.address source then continuation mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, AddressImage.accepts, valid] using AddressImage.pc mode layout.address source state ready.addressSetup rep bounds.offsetInside bounds.baseInside
  | some position =>
    simpa [finish, acceptedFinish, continuation, AddressImage.accepts, valid] using StoreInvocationImage.return_pc mode (storeLayout mode layout) _
      (store_ready mode layout source state ready bounds rep position valid)

theorem finish_intact (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    SpacedCombinedImage.Intact mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase
      (finish mode layout source state).memory := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.finish_intact mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, acceptedFinish, valid, storeLayout] using StoreInvocationImage.finish_intact mode (storeLayout mode layout) _
      (store_ready mode layout source state ready bounds rep position valid)

theorem top_reusable (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    load mode (finish mode layout source state).memory (Arithmetic.encodeNat mode layout.address.offset.guard.setup.top) =
      Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.top_reusable mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, acceptedFinish, valid, storeLayout] using StoreInvocationImage.top_reusable mode (storeLayout mode layout) _
      (store_ready mode layout source state ready bounds rep position valid)

theorem stack (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).stack = Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.stack mode layout.address source state ready.addressSetup rep
  | some position =>
    simpa [finish, acceptedFinish, valid, storeLayout] using StoreInvocationImage.stack mode (storeLayout mode layout) _
      (store_ready mode layout source state ready bounds rep position valid)

theorem carry (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (_bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    (finish mode layout source state).carry = false := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.carry mode layout.address source state ready.addressSetup rep
  | some position =>
    have storeFrame := StoreInvocationImage.carry mode (storeLayout mode layout) (afterRead mode layout source state)
    have readFrame := ReadInvocationImage.carry mode (readLayout mode layout) (afterAddress mode layout source state)
    have result := storeFrame.trans (readFrame.trans (AddressImage.carry mode layout.address source state ready.addressSetup rep))
    simpa [finish, acceptedFinish, valid] using result

/-- Other owned words are framed across the complete store block. The
heap destination is derived from the source address; no second operand exists. -/
theorem load_frame (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase observed)
    (differentAddress : forall field, Not (observed = Arithmetic.encodeNat mode (AddressImage.fieldAddress layout.address field)))
    (differentDestination : forall position, Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position ->
      Not (observed = SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position)) :
    load mode (finish mode layout source state).memory observed = load mode state.memory observed := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simpa [finish, afterAddress, valid] using AddressImage.load_frame mode layout.address source state ready.addressSetup rep observed owned differentAddress
  | some position =>
    have notTarget : Not (observed = load mode (afterRead mode layout source state).memory (ReaderImage.label mode (storeLayout mode layout).body)) := by
      change Not (observed = load mode (afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee))
      rw [pointer_after_read mode layout source state ready bounds rep position valid]
      exact differentDestination position valid
    have storeFrame := StoreInvocationImage.load_frame mode (storeLayout mode layout) _ (store_ready mode layout source state ready bounds rep position valid)
      observed owned notTarget (differentAddress (.control .slot))
    have readFrame := ReadInvocationImage.load_frame mode (readLayout mode layout) _ (read_ready mode layout source state ready bounds rep position valid)
      observed owned (differentAddress (.control .slot))
    have addressFrame := AddressImage.load_frame mode layout.address source state ready.addressSetup rep observed owned differentAddress
    simpa [finish, acceptedFinish, afterRead, valid] using storeFrame.trans (readFrame.trans addressFrame)

theorem run (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (bounds : Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory) :
    runForms mode (program mode layout source state) state = finish mode layout source state :=
  (Fetch.trace_run_eq mode (trace mode layout source state ready bounds rep)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode) :
    (program mode layout source state).length = if AddressImage.accepts layout.address source then 239
      else if SourceValues.isOffset (source.registers layout.address.offset.offset) then 222 else 100 := by
  cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
  | none => simp [program, valid, AddressImage.accepts, AddressImage.program_count]
  | some position =>
    have tags := address_tags source layout.address.base layout.address.offset.offset position valid
    simp [program, acceptedProgram, valid, AddressImage.accepts, AddressImage.program_count, ReadInvocationImage.program_count,
      StoreInvocationImage.program_count, tags.2, SourceValues.isOffset]

structure Spec (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (start stop : State mode) : Prop where
  sourceStep : Dolan.Mov.execute (.store layout.address.base layout.address.offset.offset layout.source) source =
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

end SmcTuring.Native.StoreImage
