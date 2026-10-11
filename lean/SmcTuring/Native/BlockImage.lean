module
public import SmcTuring.Native.ImmediateImage
public import SmcTuring.Native.LoadImage
public import SmcTuring.Native.StoreImage

public section

namespace SmcTuring.Native.BlockImage

open Execution

/-- Finite static observations used by an address block. The computed active
operand and all temporary values are deliberately absent. -/
inductive AddressStatic (mode : Mode) (layout : AddressImage.Layout mode) : Word mode -> Prop where
  | top : AddressStatic mode layout (Arithmetic.encodeNat mode layout.offset.guard.setup.top)
  | offsetReader : AddressStatic mode layout (ReaderImage.label mode layout.offset.readerCallee)
  | offsetGuard (role : GuardInvocationImage.Metadata) :
      AddressStatic mode layout (GuardInvocationImage.metadataWord mode (OffsetGuardImage.guardLayout mode layout.offset) role)
  | pointer (role : PointerImage.Metadata) :
      AddressStatic mode layout (PointerImage.metadataWord mode (AddressImage.pointerLayout mode layout) role)
  | baseGuard (role : GuardInvocationImage.Metadata) :
      AddressStatic mode layout (GuardInvocationImage.metadataWord mode (AddressImage.guardLayout mode layout) role)

theorem address_ready_from_snapshot (mode : Mode) (layout : AddressImage.Layout mode)
    (original actual : State mode) (ready : AddressImage.Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.offset.start)
    (intact : SpacedCombinedImage.Intact mode layout.offset.guard.setup.whole
      layout.offset.guard.setup.origin layout.offset.guard.setup.gridBase actual.memory)
    (frames : forall word, AddressStatic mode layout word -> load mode actual.memory word = load mode original.memory word) :
    AddressImage.Ready mode layout actual := by
  have offsetReady : OffsetGuardImage.Ready mode layout.offset actual := {
    readSetup := ReadScalarImage.transport_ready mode .store (OffsetGuardImage.readLayout mode layout.offset)
      _ _ ready.offsetSetup.readSetup location intact (frames _ .top) (frames _ .offsetReader)
    guardSetup := GuardInvocationImage.transport_ready mode (OffsetGuardImage.guardLayout mode layout.offset)
      _ _ ready.offsetSetup.guardSetup rfl intact (fun role => frames _ (.offsetGuard role))
    capacity := ready.offsetSetup.capacity
    positive := ready.offsetSetup.positive
    fieldsBefore := ready.offsetSetup.fieldsBefore
    metadataDifferent := ready.offsetSetup.metadataDifferent
    sourcePointer := (frames _ .offsetReader).trans ready.offsetSetup.sourcePointer
    boundary := (frames _ (.offsetGuard .boundary)).trans ready.offsetSetup.boundary
    sense := ready.offsetSetup.sense }
  exact {
    offsetSetup := offsetReady
    pointerSetup := PointerImage.transport_ready mode (AddressImage.pointerLayout mode layout) _ _
      ready.pointerSetup rfl intact (fun role => frames _ (.pointer role))
    guardSetup := GuardInvocationImage.transport_ready mode (AddressImage.guardLayout mode layout) _ _
      ready.guardSetup rfl intact (fun role => frames _ (.baseGuard role))
    pointerMetadataSeparate := ready.pointerMetadataSeparate
    guardOffsetSeparate := ready.guardOffsetSeparate
    guardPointerSeparate := ready.guardPointerSeparate
    pointerSeparate := ready.pointerSeparate }

/-- An emitted source block, including all static addresses chosen by the
layout pass. Address immediates are initialized data in the fixed Dolan kernel. -/
inductive Block (mode : Mode) where
  | immediate (layout : ImmediateImage.Layout mode)
  | load (layout : LoadImage.Layout mode)
  | store (layout : StoreImage.Layout mode)

structure Context (mode : Mode) where
  whole : List (SpacedPacking.Piece mode)
  origin : Nat
  gridBase : Nat
  cells : Nat
  top : Nat
  slot : Nat
  deriving DecidableEq

@[expose] def context (mode : Mode) : Block mode -> Context mode
  | .immediate layout => ⟨layout.unit.reader.whole, layout.unit.reader.origin, layout.unit.reader.gridBase,
      layout.cells, layout.unit.reader.top, layout.unit.reader.slot⟩
  | .load layout => ⟨layout.address.offset.guard.setup.whole, layout.address.offset.guard.setup.origin,
      layout.address.offset.guard.setup.gridBase, layout.address.offset.cells, layout.address.offset.guard.setup.top,
      layout.address.offset.guard.setup.slot⟩
  | .store layout => ⟨layout.address.offset.guard.setup.whole, layout.address.offset.guard.setup.origin,
      layout.address.offset.guard.setup.gridBase, layout.address.offset.cells, layout.address.offset.guard.setup.top,
      layout.address.offset.guard.setup.slot⟩

@[expose] def instruction {mode : Mode} : Block mode -> Dolan.Mov.Instruction
  | .immediate layout => .immediate layout.destination (.offset layout.choice)
  | .load layout => .load layout.destination layout.address.base layout.address.offset.offset
  | .store layout => .store layout.address.base layout.address.offset.offset layout.source
@[expose] def start (mode : Mode) : Block mode -> Nat
  | .immediate layout => layout.unit.reader.caller
  | .load layout => layout.address.offset.start
  | .store layout => layout.address.offset.start
@[expose] def continuation (mode : Mode) : Block mode -> Word mode
  | .immediate layout => Arithmetic.encodeNat mode (ReadScalarImage.endPosition mode .store layout.unit)
  | .load layout => LoadImage.continuation mode layout
  | .store layout => StoreImage.continuation mode layout
@[expose] def accepts {mode : Mode} (block : Block mode) (source : Dolan.Mov.State) : Bool :=
  (Dolan.Mov.execute (instruction block) source).isSome
@[expose] def result {mode : Mode} (block : Block mode) (source : Dolan.Mov.State) : Dolan.Mov.State :=
  match block with
  | .immediate layout => ImmediateImage.sourceResult layout source
  | .load layout => LoadImage.sourceResult layout source
  | .store layout => StoreImage.sourceResult layout source
@[expose] def finish (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state : State mode) : State mode :=
  match block with
  | .immediate layout => ImmediateImage.finish mode layout state
  | .load layout => LoadImage.finish mode layout source state
  | .store layout => StoreImage.finish mode layout source state
@[expose] def program (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state : State mode) : List (Form mode) :=
  match block with
  | .immediate layout => ImmediateImage.program mode layout state
  | .load layout => LoadImage.program mode layout source state
  | .store layout => StoreImage.program mode layout source state
@[expose] def Ready (mode : Mode) (block : Block mode) (state : State mode) : Prop :=
  match block with
  | .immediate layout => ImmediateImage.Ready mode layout state
  | .load layout => LoadImage.Ready mode layout state
  | .store layout => StoreImage.Ready mode layout state
@[expose] def Bounds (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) : Prop :=
  match block with
  | .immediate _ => True
  | .load layout => LoadImage.Bounds mode layout source
  | .store layout => StoreImage.Bounds mode layout source
@[expose] def Owned (mode : Mode) (block : Block mode) : Word mode -> Prop :=
  SpacedCombinedImage.Owned mode (context mode block).whole (context mode block).origin (context mode block).gridBase
@[expose] def Intact (mode : Mode) (block : Block mode) (state : State mode) : Prop :=
  SpacedCombinedImage.Intact mode (context mode block).whole (context mode block).origin (context mode block).gridBase state.memory
@[expose] def Rep (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state : State mode) : Prop :=
  SourceData.Rep mode (context mode block).gridBase (context mode block).cells source state.memory

inductive Static (mode : Mode) : Block mode -> Word mode -> Prop where
  | immediateTop (layout) : Static mode (.immediate layout) (Arithmetic.encodeNat mode layout.unit.reader.top)
  | immediateReader (layout) : Static mode (.immediate layout) (ReaderImage.label mode layout.unit.reader.callee)
  | immediateConstant (layout) : Static mode (.immediate layout) (Arithmetic.encodeNat mode layout.constant)
  | loadAddress (layout) {word} : AddressStatic mode layout.address word -> Static mode (.load layout) word
  | storeAddress (layout) {word} : AddressStatic mode layout.address word -> Static mode (.store layout) word
  | storeReader (layout) : Static mode (.store layout) (ReaderImage.label mode layout.readerCallee)

/-- The shared active operand can hold a different pointer after each source
block. Only its actual ownership and separation matter for the static setup. -/
@[expose] def PointerSafe (mode : Mode) (block : Block mode) (state : State mode) : Prop :=
  match block with
  | .immediate _ => True
  | .load layout => Owned mode block (load mode state.memory (ReaderImage.label mode layout.address.pointerCallee))
  | .store layout =>
      Owned mode block (load mode state.memory (ReaderImage.label mode layout.address.pointerCallee)) ∧
      load mode state.memory (ReaderImage.label mode layout.address.pointerCallee) ≠ Arithmetic.encodeNat mode layout.address.offset.guard.setup.top ∧
      load mode state.memory (ReaderImage.label mode layout.address.pointerCallee) ≠ Arithmetic.encodeNat mode layout.address.offset.guard.setup.slot

theorem ready_from_snapshot (mode : Mode) (block : Block mode) (original actual : State mode)
    (ready : Ready mode block original) (location : actual.pc = Arithmetic.encodeNat mode (start mode block))
    (intact : Intact mode block actual)
    (frames : forall word, Static mode block word -> load mode actual.memory word = load mode original.memory word)
    (pointer : PointerSafe mode block actual) : Ready mode block actual := by
  cases block with
  | immediate layout =>
    exact {
      unit := ReadScalarImage.transport_ready mode .store layout.unit _ _ ready.unit location intact
        (frames _ (.immediateTop layout)) (frames _ (.immediateReader layout))
      target := ready.target
      capacity := ready.capacity
      slotBefore := ready.slotBefore
      points := (frames _ (.immediateReader layout)).trans ready.points
      constantValue := (frames _ (.immediateConstant layout)).trans ready.constantValue
      constantNotSlot := ready.constantNotSlot }
  | load layout =>
    exact ⟨address_ready_from_snapshot mode layout.address _ _ ready.addressSetup location intact
        (fun word observed => frames word (.loadAddress layout observed)),
      ReadScalarImage.transport_ready_pointer mode .store (LoadImage.readLayout mode layout) _ _ ready.readSetup
        rfl intact (frames _ (.loadAddress layout .top)) pointer⟩
  | store layout =>
    exact {
      addressSetup := address_ready_from_snapshot mode layout.address _ _ ready.addressSetup location intact
        (fun word observed => frames word (.storeAddress layout observed))
      readSetup := ReadInvocationImage.transport_ready mode (StoreImage.readLayout mode layout) _ _ ready.readSetup
        rfl intact (frames _ (.storeAddress layout .top)) (frames _ (.storeReader layout))
      storeSetup := StoreInvocationImage.transport_ready_pointer mode (StoreImage.storeLayout mode layout) _ _ ready.storeSetup
        rfl intact (frames _ (.storeAddress layout .top)) pointer.1 pointer.2.1 pointer.2.2
      sourcePointer := (frames _ (.storeReader layout)).trans ready.sourcePointer
      sourceLabelSeparate := ready.sourceLabelSeparate
      topBefore := ready.topBefore }

@[expose] def failureTarget (mode : Mode) (block : Block mode) (state : State mode) : Word mode :=
  match block with
  | .immediate _ => 0
  | .load layout => load mode state.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal)
  | .store layout => load mode state.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal)

private theorem accepts_load (mode : Mode) (layout : LoadImage.Layout mode) (source : Dolan.Mov.State) :
    accepts (.load layout) source = AddressImage.accepts layout.address source := by
  simp only [accepts, instruction, LoadImage.source_step]
  split <;> simp_all
private theorem accepts_store (mode : Mode) (layout : StoreImage.Layout mode) (source : Dolan.Mov.State) :
    accepts (.store layout) source = AddressImage.accepts layout.address source := by
  simp only [accepts, instruction, StoreImage.source_step]
  split <;> simp_all

structure Spec (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state stop : State mode) : Prop where
  sourceStep : Dolan.Mov.execute (instruction block) source = if accepts block source then some (result block source) else none
  represented : Rep mode block (result block source) stop
  trace : Fetch.Trace mode state (program mode block source state) stop
  owned : Writes.OwnedRun mode (Owned mode block) (program mode block source state) state
  pc : stop.pc = if accepts block source then continuation mode block else failureTarget mode block state
  intact : Intact mode block stop
  top : load mode stop.memory (Arithmetic.encodeNat mode (context mode block).top) =
    Arithmetic.encodeNat mode (context mode block).slot + Arithmetic.encodeNat mode mode.wordBytes
  stack : stop.stack = Arithmetic.encodeNat mode (context mode block).slot

/-- The dispatch theorem connects each literal source instruction to its
complete fetched byte block, including the exact rejected path. -/
theorem correct (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode block state) (bounds : Bounds mode block source) (rep : Rep mode block source state) :
    Spec mode block source state (finish mode block source state) := by
  cases block with
  | immediate layout =>
    have checked := ImmediateImage.correct mode layout source state ready rep
    simpa only [instruction, accepts, ImmediateImage.source_step, Option.isSome_some, Bool.true_eq,
      ite_true, result, program, finish, continuation, Rep, Intact, Owned, context] using
      (show Spec mode (.immediate layout) source state (finish mode (.immediate layout) source state) from
        ⟨checked.sourceStep, checked.represented, checked.trace, checked.owned,
          by simpa [accepts, instruction, ImmediateImage.source_step, continuation, finish] using checked.pc,
          checked.intact, checked.top, checked.stack⟩)
  | load layout =>
    have checked := LoadImage.correct mode layout source state ready bounds rep
    exact ⟨by simpa only [instruction, accepts_load, result] using checked.sourceStep,
      checked.represented, checked.trace, checked.owned,
      by simpa only [accepts_load, continuation, failureTarget, finish] using checked.pc,
      checked.intact, checked.top, checked.stack⟩
  | store layout =>
    have checked := StoreImage.correct mode layout source state ready bounds rep
    exact ⟨by simpa only [instruction, accepts_store, result] using checked.sourceStep,
      checked.represented, checked.trace, checked.owned,
      by simpa only [accepts_store, continuation, failureTarget, finish] using checked.pc,
      checked.intact, checked.top, checked.stack⟩

/-- The final write set is stated as physical code fields. Temporary exchanges
restore their operands and therefore do not enlarge this boundary write set. -/
@[expose] def MayWrite (mode : Mode) (block : Block mode) (word : Word mode) : Prop :=
  match block with
  | .immediate layout => word = Arithmetic.encodeNat mode layout.unit.reader.slot ∨
      word = SourceData.registerWord mode layout.unit.reader.gridBase layout.destination
  | .load layout => exists field, word = Arithmetic.encodeNat mode (LoadImage.fieldAddress layout field)
  | .store layout => (exists field, word = Arithmetic.encodeNat mode (AddressImage.fieldAddress layout.address field)) ∨
      exists position : Nat × Bool, position.1 < layout.address.offset.cells ∧
        word = SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position

theorem load_frame (mode : Mode) (block : Block mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode block state) (bounds : Bounds mode block source) (rep : Rep mode block source state)
    (word : Word mode) (owned : Owned mode block word) (outside : Not (MayWrite mode block word)) :
    load mode (finish mode block source state).memory word = load mode state.memory word := by
  cases block with
  | immediate layout =>
    apply ReadScalarImage.load_frame mode .store layout.unit state ready.unit word owned
    · rw [ready.target]
      exact fun same => outside (Or.inr same)
    · exact fun same => outside (Or.inl same)
  | load layout =>
    exact LoadImage.load_frame mode layout source state ready bounds rep word owned
      (fun field same => outside ⟨field, same⟩)
  | store layout =>
    exact StoreImage.load_frame mode layout source state ready bounds rep word owned
      (fun field same => outside (Or.inl ⟨field, same⟩))
      (fun position valid same => outside (Or.inr ⟨position,
        StoreImage.pointer_inside mode layout source bounds position valid, same⟩))

theorem load_pointer (mode : Mode) (layout : LoadImage.Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : LoadImage.Ready mode layout state) (bounds : LoadImage.Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Nat × Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    load mode (LoadImage.finish mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee) =
      SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position := by
  have actualReady := LoadImage.read_ready mode layout source state ready bounds rep position valid
  have pointerOwned : SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole
      layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase (ReaderImage.label mode layout.address.pointerCallee) :=
    ready.addressSetup.pointerSetup.baseSetup.scalarSetup.owned
  have pointerFits := SourceData.metadata_fits mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells _
    ready.addressSetup.offsetSetup.capacity (ready.addressSetup.pointerSetup.fieldsBefore .pointer)
  have notDestination := SourceData.register_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells
    (AddressImage.pointerPosition mode layout.address) layout.destination ready.addressSetup.offsetSetup.capacity pointerFits
    (ready.addressSetup.pointerSetup.fieldsBefore .pointer)
  have frame := ReadScalarImage.load_frame mode .store (LoadImage.readLayout mode layout) _ actualReady _ pointerOwned
    (by simpa only [LoadImage.readLayout, SourceData.registerWord, ReaderImage.label, AddressImage.pointerPosition] using Ne.symm notDestination)
    actualReady.readReady.labelDifferent
  rw [LoadImage.finish, valid]
  exact frame.trans (AddressImage.pointer mode layout.address source state ready.addressSetup rep position valid)

theorem store_pointer (mode : Mode) (layout : StoreImage.Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : StoreImage.Ready mode layout state) (bounds : StoreImage.Bounds mode layout source)
    (rep : SourceData.Rep mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells source state.memory)
    (position : Nat × Bool) (valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset = some position) :
    load mode (StoreImage.finish mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee) =
      SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position := by
  have actualReady := StoreImage.store_ready mode layout source state ready bounds rep position valid
  have pointerOwned : SpacedCombinedImage.Owned mode layout.address.offset.guard.setup.whole
      layout.address.offset.guard.setup.origin layout.address.offset.guard.setup.gridBase (ReaderImage.label mode layout.address.pointerCallee) :=
    ready.addressSetup.pointerSetup.baseSetup.scalarSetup.owned
  have pointerFits := SourceData.metadata_fits mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells _
    ready.addressSetup.offsetSetup.capacity (ready.addressSetup.pointerSetup.fieldsBefore .pointer)
  have notDestination := SourceData.heap_not_before mode layout.address.offset.guard.setup.gridBase layout.address.offset.cells
    (AddressImage.pointerPosition mode layout.address) position ready.addressSetup.offsetSetup.capacity
    (StoreImage.pointer_inside mode layout source bounds position valid) pointerFits
    (ready.addressSetup.pointerSetup.fieldsBefore .pointer)
  have frame := StoreInvocationImage.load_frame mode (StoreImage.storeLayout mode layout) _ actualReady _ pointerOwned
    (by
      change Not (ReaderImage.label mode layout.address.pointerCallee = load mode (StoreImage.afterRead mode layout source state).memory (ReaderImage.label mode layout.address.pointerCallee))
      rw [StoreImage.pointer_after_read mode layout source state ready bounds rep position valid]
      simpa only [ReaderImage.label, AddressImage.pointerPosition] using Ne.symm notDestination)
    actualReady.labelDifferentSlot
  rw [StoreImage.finish, valid, StoreImage.acceptedFinish]
  exact frame.trans (StoreImage.pointer_after_read mode layout source state ready bounds rep position valid)

end SmcTuring.Native.BlockImage
