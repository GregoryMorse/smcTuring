module
public import SmcTuring.Native.ReadScalarImage

public section

namespace SmcTuring.Native.GuardSelectionImage

open Execution ControlImage

structure Layout (mode : Mode) where
  start : Nat
  continuationCallee : Nat
  terminalCallee : Nat
  maskCallee : Nat
  continuation : Nat
  terminal : Nat
  mask : Nat
  selected : Nat
  top : Nat
  slot : Nat
  origin : Nat
  gridBase : Nat
  whole : List (SpacedPacking.Piece mode)
  continuationInitial : Word mode
  terminalInitial : Word mode
  maskInitial : Word mode

@[expose] def updateLayout (mode : Mode) (layout : Layout mode) (caller callee : Nat) (initial : Word mode) : ReadScalarImage.Layout mode :=
  ⟨⟨caller, callee, layout.top, layout.slot, layout.origin, layout.gridBase, initial, layout.whole⟩, layout.selected⟩
@[expose] def firstLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  updateLayout mode layout layout.start layout.continuationCallee layout.continuationInitial
@[expose] def secondLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  updateLayout mode layout (ReadScalarImage.endPosition mode .store (firstLayout mode layout)) layout.terminalCallee layout.terminalInitial
@[expose] def thirdLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  updateLayout mode layout (ReadScalarImage.endPosition mode .bitXor (secondLayout mode layout)) layout.maskCallee layout.maskInitial
@[expose] def fourthLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  updateLayout mode layout (ReadScalarImage.endPosition mode .bitAnd (thirdLayout mode layout)) layout.continuationCallee layout.continuationInitial
@[expose] def callStart (mode : Mode) (layout : Layout mode) : Nat := ReadScalarImage.endPosition mode .bitXor (fourthLayout mode layout)
@[expose] def callTarget (mode : Mode) (layout : Layout mode) : Calls.Target := CallsImage.callTarget mode (callStart mode layout) (.indirect layout.selected)
@[expose] def callerEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (callStart mode layout + CallsImage.totalSize mode (.indirect layout.selected))
@[expose] def viewAt (mode : Mode) (state : State mode) (position : Nat) : State mode := { state with pc := Arithmetic.encodeNat mode position }
@[expose] def first (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := ReadScalarImage.finish mode .store (firstLayout mode layout) state
@[expose] def second (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := ReadScalarImage.finish mode .bitXor (secondLayout mode layout) (first mode layout state)
@[expose] def third (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := ReadScalarImage.finish mode .bitAnd (thirdLayout mode layout) (second mode layout state)
@[expose] def fourth (mode : Mode) (layout : Layout mode) (state : State mode) : State mode := ReadScalarImage.finish mode .bitXor (fourthLayout mode layout) (third mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Calls.called mode (fourth mode layout state) (CallsImage.firstDisp mode (callStart mode layout) layout.top)
    (CallsImage.secondDisp mode (callStart mode layout) layout.top) (callTarget mode layout)
@[expose] def callProgram (mode : Mode) (layout : Layout mode) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode (callStart mode layout) layout.top)
    (CallsImage.secondDisp mode (callStart mode layout) layout.top) (callTarget mode layout)
@[expose] def beforeProgram (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  ReadScalarImage.program mode .store (firstLayout mode layout) state ++
    ReadScalarImage.program mode .bitXor (secondLayout mode layout) (first mode layout state) ++
    ReadScalarImage.program mode .bitAnd (thirdLayout mode layout) (second mode layout state) ++
    ReadScalarImage.program mode .bitXor (fourthLayout mode layout) (third mode layout state)
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) := beforeProgram mode layout state ++ callProgram mode layout
@[expose] def selectedValue (mode : Mode) (layout : Layout mode) (state : State mode) : Word mode :=
  Arithmetic.maskSelect (load mode state.memory (Arithmetic.encodeNat mode layout.continuation))
    (load mode state.memory (Arithmetic.encodeNat mode layout.terminal)) (load mode state.memory (Arithmetic.encodeNat mode layout.mask))

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  firstReady : ReadScalarImage.Ready mode .store (firstLayout mode layout) state
  secondSetup : ReadScalarImage.Ready mode .bitXor (secondLayout mode layout) (viewAt mode state (secondLayout mode layout).reader.caller)
  thirdSetup : ReadScalarImage.Ready mode .bitAnd (thirdLayout mode layout) (viewAt mode state (thirdLayout mode layout).reader.caller)
  fourthSetup : ReadScalarImage.Ready mode .bitXor (fourthLayout mode layout) (viewAt mode state (fourthLayout mode layout).reader.caller)
  continuationPointer : load mode state.memory (ReaderImage.label mode layout.continuationCallee) = Arithmetic.encodeNat mode layout.continuation
  terminalPointer : load mode state.memory (ReaderImage.label mode layout.terminalCallee) = Arithmetic.encodeNat mode layout.terminal
  maskPointer : load mode state.memory (ReaderImage.label mode layout.maskCallee) = Arithmetic.encodeNat mode layout.mask
  continuationNotSelected : Not (Arithmetic.encodeNat mode layout.continuation = Arithmetic.encodeNat mode layout.selected)
  terminalNotSelected : Not (Arithmetic.encodeNat mode layout.terminal = Arithmetic.encodeNat mode layout.selected)
  maskNotSelected : Not (Arithmetic.encodeNat mode layout.mask = Arithmetic.encodeNat mode layout.selected)
  continuationNotSlot : Not (Arithmetic.encodeNat mode layout.continuation = Arithmetic.encodeNat mode layout.slot)
  terminalNotSlot : Not (Arithmetic.encodeNat mode layout.terminal = Arithmetic.encodeNat mode layout.slot)
  maskNotSlot : Not (Arithmetic.encodeNat mode layout.mask = Arithmetic.encodeNat mode layout.slot)
  continuationLabelNotSelected : Not (ReaderImage.label mode layout.continuationCallee = Arithmetic.encodeNat mode layout.selected)
  terminalLabelNotSelected : Not (ReaderImage.label mode layout.terminalCallee = Arithmetic.encodeNat mode layout.selected)
  maskLabelNotSelected : Not (ReaderImage.label mode layout.maskCallee = Arithmetic.encodeNat mode layout.selected)
  callRanges : CallsImage.Ranges mode (callStart mode layout) layout.top (.indirect layout.selected)
  callFits : callStart mode layout + CallsImage.totalSize mode (.indirect layout.selected) < 2 ^ (8 * mode.wordBytes)
  callWithin : Fragment.Within mode (ControlPacking.place mode (callStart mode layout) (CallsImage.packets mode (callStart mode layout) layout.top (.indirect layout.selected)))
    (SpacedPacking.place mode layout.origin layout.whole)

/-- The complete selector setup transfers through the maintained image and
its stack-top/three reader-label frames. Data values are read from the new
executed state; neither the selector trace nor its chosen target is assumed. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode) (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.start)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.top) = load mode original.memory (Arithmetic.encodeNat mode layout.top))
    (continuationFrame : load mode actual.memory (ReaderImage.label mode layout.continuationCallee) = load mode original.memory (ReaderImage.label mode layout.continuationCallee))
    (terminalFrame : load mode actual.memory (ReaderImage.label mode layout.terminalCallee) = load mode original.memory (ReaderImage.label mode layout.terminalCallee))
    (maskFrame : load mode actual.memory (ReaderImage.label mode layout.maskCallee) = load mode original.memory (ReaderImage.label mode layout.maskCallee)) : Ready mode layout actual := by
  refine ⟨?_, ?_, ?_, ?_, continuationFrame.trans ready.continuationPointer, terminalFrame.trans ready.terminalPointer,
    maskFrame.trans ready.maskPointer, ready.continuationNotSelected, ready.terminalNotSelected, ready.maskNotSelected,
    ready.continuationNotSlot, ready.terminalNotSlot, ready.maskNotSlot, ready.continuationLabelNotSelected,
    ready.terminalLabelNotSelected, ready.maskLabelNotSelected, ready.callRanges, ready.callFits, ready.callWithin⟩
  · exact ReadScalarImage.transport_ready mode .store (firstLayout mode layout) _ _ ready.firstReady location intact topFrame continuationFrame
  · exact ReadScalarImage.transport_ready mode .bitXor (secondLayout mode layout) _ _ ready.secondSetup rfl intact topFrame terminalFrame
  · exact ReadScalarImage.transport_ready mode .bitAnd (thirdLayout mode layout) _ _ ready.thirdSetup rfl intact topFrame maskFrame
  · exact ReadScalarImage.transport_ready mode .bitXor (fourthLayout mode layout) _ _ ready.fourthSetup rfl intact topFrame continuationFrame

theorem first_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (first mode layout state).memory observed = load mode state.memory observed := by
  rw [first, ReadScalarImage.load_frame mode .store (firstLayout mode layout) state ready.firstReady observed owned notSelected notSlot]

theorem second_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.Ready mode .bitXor (secondLayout mode layout) (first mode layout state) := by
  apply ReadScalarImage.transport_ready mode .bitXor (secondLayout mode layout) _ _ ready.secondSetup
  · exact ReadScalarImage.pc mode .store (firstLayout mode layout) state ready.firstReady
  · exact ReadScalarImage.finish_intact mode .store (firstLayout mode layout) state ready.firstReady
  · exact first_load_frame mode layout state ready _ ready.secondSetup.readReady.topOwned ready.firstReady.targetNotTop ready.secondSetup.readReady.topDifferent
  · exact first_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (secondLayout mode layout).reader _ ready.secondSetup.readReady)
      ready.terminalLabelNotSelected ready.secondSetup.readReady.labelDifferent

theorem second_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (second mode layout state).memory observed = load mode state.memory observed := by
  rw [second, ReadScalarImage.load_frame mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready) observed owned notSelected notSlot]
  exact first_load_frame mode layout state ready observed owned notSelected notSlot

theorem third_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.Ready mode .bitAnd (thirdLayout mode layout) (second mode layout state) := by
  apply ReadScalarImage.transport_ready mode .bitAnd (thirdLayout mode layout) _ _ ready.thirdSetup
  · exact ReadScalarImage.pc mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready)
  · exact ReadScalarImage.finish_intact mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready)
  · exact second_load_frame mode layout state ready _ ready.thirdSetup.readReady.topOwned ready.firstReady.targetNotTop ready.thirdSetup.readReady.topDifferent
  · exact second_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (thirdLayout mode layout).reader _ ready.thirdSetup.readReady)
      ready.maskLabelNotSelected ready.thirdSetup.readReady.labelDifferent

theorem third_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (third mode layout state).memory observed = load mode state.memory observed := by
  rw [third, ReadScalarImage.load_frame mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready) observed owned notSelected notSlot]
  exact second_load_frame mode layout state ready observed owned notSelected notSlot

theorem fourth_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.Ready mode .bitXor (fourthLayout mode layout) (third mode layout state) := by
  apply ReadScalarImage.transport_ready mode .bitXor (fourthLayout mode layout) _ _ ready.fourthSetup
  · exact ReadScalarImage.pc mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready)
  · exact ReadScalarImage.finish_intact mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready)
  · exact third_load_frame mode layout state ready _ ready.fourthSetup.readReady.topOwned ready.firstReady.targetNotTop ready.fourthSetup.readReady.topDifferent
  · exact third_load_frame mode layout state ready _
      (ReadInvocationImage.label_owned mode (fourthLayout mode layout).reader _ ready.fourthSetup.readReady)
      ready.continuationLabelNotSelected ready.fourthSetup.readReady.labelDifferent

theorem fourth_load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (fourth mode layout state).memory observed = load mode state.memory observed := by
  rw [fourth, ReadScalarImage.load_frame mode .bitXor (fourthLayout mode layout) (third mode layout state) (fourth_ready mode layout state ready) observed owned notSelected notSlot]
  exact third_load_frame mode layout state ready observed owned notSelected notSlot

theorem continuation_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.continuation) := by
  have owns := ready.firstReady.readReady.pointerOwned
  change SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.continuationCallee)) at owns
  rw [ready.continuationPointer] at owns
  exact owns

theorem terminal_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.terminal) := by
  have owns := ready.secondSetup.readReady.pointerOwned
  change SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.terminalCallee)) at owns
  rw [ready.terminalPointer] at owns
  exact owns

theorem mask_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.mask) := by
  have owns := ready.thirdSetup.readReady.pointerOwned
  change SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.maskCallee)) at owns
  rw [ready.maskPointer] at owns
  exact owns

theorem first_read_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.readValue mode (firstLayout mode layout) state = load mode state.memory (Arithmetic.encodeNat mode layout.continuation) := by
  have pointed : load mode state.memory (ReaderImage.label mode layout.continuationCallee) = Arithmetic.encodeNat mode layout.continuation := by
    exact ready.continuationPointer
  rw [ReadScalarImage.read_value_from mode (firstLayout mode layout) state _ pointed ready.continuationNotSlot]

theorem second_read_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.readValue mode (secondLayout mode layout) (first mode layout state) = load mode state.memory (Arithmetic.encodeNat mode layout.terminal) := by
  have pointed : load mode (first mode layout state).memory (ReaderImage.label mode layout.terminalCallee) = Arithmetic.encodeNat mode layout.terminal := by
    have labelOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.terminalCallee) :=
      ReadInvocationImage.label_owned mode (secondLayout mode layout).reader _ ready.secondSetup.readReady
    rw [first_load_frame mode layout state ready _ labelOwned ready.terminalLabelNotSelected ready.secondSetup.readReady.labelDifferent]
    exact ready.terminalPointer
  rw [ReadScalarImage.read_value_from mode (secondLayout mode layout) (first mode layout state) _ pointed ready.terminalNotSlot]
  exact first_load_frame mode layout state ready _ (terminal_owned mode layout state ready) ready.terminalNotSelected ready.terminalNotSlot

theorem third_read_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.readValue mode (thirdLayout mode layout) (second mode layout state) = load mode state.memory (Arithmetic.encodeNat mode layout.mask) := by
  have pointed : load mode (second mode layout state).memory (ReaderImage.label mode layout.maskCallee) = Arithmetic.encodeNat mode layout.mask := by
    have labelOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.maskCallee) :=
      ReadInvocationImage.label_owned mode (thirdLayout mode layout).reader _ ready.thirdSetup.readReady
    rw [second_load_frame mode layout state ready _ labelOwned ready.maskLabelNotSelected ready.thirdSetup.readReady.labelDifferent]
    exact ready.maskPointer
  rw [ReadScalarImage.read_value_from mode (thirdLayout mode layout) (second mode layout state) _ pointed ready.maskNotSlot]
  exact second_load_frame mode layout state ready _ (mask_owned mode layout state ready) ready.maskNotSelected ready.maskNotSlot

theorem fourth_read_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.readValue mode (fourthLayout mode layout) (third mode layout state) = load mode state.memory (Arithmetic.encodeNat mode layout.continuation) := by
  have pointed : load mode (third mode layout state).memory (ReaderImage.label mode layout.continuationCallee) = Arithmetic.encodeNat mode layout.continuation := by
    have labelOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.continuationCallee) :=
      ReadInvocationImage.label_owned mode (fourthLayout mode layout).reader _ ready.fourthSetup.readReady
    rw [third_load_frame mode layout state ready _ labelOwned ready.continuationLabelNotSelected ready.fourthSetup.readReady.labelDifferent]
    exact ready.continuationPointer
  rw [ReadScalarImage.read_value_from mode (fourthLayout mode layout) (third mode layout state) _ pointed ready.continuationNotSlot]
  exact third_load_frame mode layout state ready _ (continuation_owned mode layout state ready) ready.continuationNotSelected ready.continuationNotSlot

theorem first_selected (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (first mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = load mode state.memory (Arithmetic.encodeNat mode layout.continuation) := by
  change load mode (ReadScalarImage.finish mode .store (firstLayout mode layout) state).memory
    (Arithmetic.encodeNat mode (firstLayout mode layout).target) = _
  rw [ReadScalarImage.written_value mode .store (firstLayout mode layout) state ready.firstReady]
  change ReadScalarImage.readValue mode (firstLayout mode layout) state = _
  exact first_read_value mode layout state ready

theorem second_selected (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (second mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = (load mode state.memory (Arithmetic.encodeNat mode layout.continuation)) ^^^ (load mode state.memory (Arithmetic.encodeNat mode layout.terminal)) := by
  change load mode (ReadScalarImage.finish mode .bitXor (secondLayout mode layout) (first mode layout state)).memory
    (Arithmetic.encodeNat mode (secondLayout mode layout).target) = _
  rw [ReadScalarImage.written_value mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready)]
  change (load mode (first mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) ^^^
    (ReadScalarImage.readValue mode (secondLayout mode layout) (first mode layout state)) = _
  rw [first_selected mode layout state ready, second_read_value mode layout state ready]

theorem third_selected (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (third mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = ((load mode state.memory (Arithmetic.encodeNat mode layout.continuation)) ^^^ (load mode state.memory (Arithmetic.encodeNat mode layout.terminal))) &&& (load mode state.memory (Arithmetic.encodeNat mode layout.mask)) := by
  change load mode (ReadScalarImage.finish mode .bitAnd (thirdLayout mode layout) (second mode layout state)).memory
    (Arithmetic.encodeNat mode (thirdLayout mode layout).target) = _
  rw [ReadScalarImage.written_value mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready)]
  change (load mode (second mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) &&&
    (ReadScalarImage.readValue mode (thirdLayout mode layout) (second mode layout state)) = _
  rw [second_selected mode layout state ready, third_read_value mode layout state ready]

theorem fourth_selected (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (fourth mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = selectedValue mode layout state := by
  change load mode (ReadScalarImage.finish mode .bitXor (fourthLayout mode layout) (third mode layout state)).memory
    (Arithmetic.encodeNat mode (fourthLayout mode layout).target) = _
  rw [ReadScalarImage.written_value mode .bitXor (fourthLayout mode layout) (third mode layout state) (fourth_ready mode layout state ready)]
  change (load mode (third mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) ^^^
    (ReadScalarImage.readValue mode (fourthLayout mode layout) (third mode layout state)) = _
  rw [third_selected mode layout state ready, fourth_read_value mode layout state ready]
  rfl

theorem selected_slot_separate (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    forall index : Fin mode.wordBytes, Not (ByteMemory.Inside layout.slot mode.wordBytes (layout.selected + index.val)) := by
  have selectedOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.selected) := ready.firstReady.scalarSetup.owned
  have slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot) := ready.firstReady.readReady.slotOwned
  have separate := Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.firstReady.readReady.gap
    selectedOwned slotOwned ready.firstReady.targetNotSlot
  rw [Arithmetic.encode_nat_toNat mode layout.selected ready.firstReady.scalarSetup.targetFits,
    Arithmetic.encode_nat_toNat mode layout.slot ready.firstReady.readReady.slotFits] at separate
  exact separate

/-- A later read/update pair supersedes both previous field values. The
commutation is justified by the actual distinct owned operand byte spans. -/
theorem collapse_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (memory : ByteMemory.Memory) (earlierSlot earlierSelected laterSlot laterSelected : Word mode) :
    ByteMemory.putWord mode (ByteMemory.putWord mode
      (ByteMemory.putWord mode (ByteMemory.putWord mode memory layout.slot earlierSlot) layout.selected earlierSelected)
      layout.slot laterSlot) layout.selected laterSelected =
    ByteMemory.putWord mode (ByteMemory.putWord mode memory layout.slot laterSlot) layout.selected laterSelected := by
  rw [Writes.put_words_commute mode (ByteMemory.putWord mode memory layout.slot earlierSlot) layout.selected layout.slot
    earlierSelected laterSlot (selected_slot_separate mode layout state ready), Writes.put_word_overwrite, Writes.put_word_overwrite]

theorem first_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (first mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.slot (ReadInvocationImage.calleeEnd mode (firstLayout mode layout).reader))
      layout.selected (load mode state.memory (Arithmetic.encodeNat mode layout.continuation)) := by
  rw [first, ReadScalarImage.memory_effect mode .store (firstLayout mode layout) state ready.firstReady]
  change ByteMemory.putWord mode (ByteMemory.putWord mode state.memory layout.slot _) layout.selected
    (ReadScalarImage.readValue mode (firstLayout mode layout) state) = _
  rw [first_read_value mode layout state ready]

theorem second_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (second mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.slot (ReadInvocationImage.calleeEnd mode (secondLayout mode layout).reader))
      layout.selected ((load mode state.memory (Arithmetic.encodeNat mode layout.continuation)) ^^^ (load mode state.memory (Arithmetic.encodeNat mode layout.terminal))) := by
  rw [second, ReadScalarImage.memory_effect mode .bitXor (secondLayout mode layout) (first mode layout state) (second_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (first mode layout state).memory layout.slot _) layout.selected
    ((load mode (first mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) ^^^
      (ReadScalarImage.readValue mode (secondLayout mode layout) (first mode layout state))) = _
  rw [first_selected mode layout state ready, second_read_value mode layout state ready,
    first_memory mode layout state ready]
  exact collapse_memory mode layout state ready _ _ _ _ _

theorem third_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (third mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.slot (ReadInvocationImage.calleeEnd mode (thirdLayout mode layout).reader))
      layout.selected (((load mode state.memory (Arithmetic.encodeNat mode layout.continuation)) ^^^ (load mode state.memory (Arithmetic.encodeNat mode layout.terminal))) &&& (load mode state.memory (Arithmetic.encodeNat mode layout.mask))) := by
  rw [third, ReadScalarImage.memory_effect mode .bitAnd (thirdLayout mode layout) (second mode layout state) (third_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (second mode layout state).memory layout.slot _) layout.selected
    ((load mode (second mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) &&&
      (ReadScalarImage.readValue mode (thirdLayout mode layout) (second mode layout state))) = _
  rw [second_selected mode layout state ready, third_read_value mode layout state ready,
    second_memory mode layout state ready]
  exact collapse_memory mode layout state ready _ _ _ _ _

theorem fourth_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (fourth mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.slot (ReadInvocationImage.calleeEnd mode (fourthLayout mode layout).reader))
      layout.selected (selectedValue mode layout state) := by
  rw [fourth, ReadScalarImage.memory_effect mode .bitXor (fourthLayout mode layout) (third mode layout state) (fourth_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (third mode layout state).memory layout.slot _) layout.selected
    ((load mode (third mode layout state).memory (Arithmetic.encodeNat mode layout.selected)) ^^^
      (ReadScalarImage.readValue mode (fourthLayout mode layout) (third mode layout state))) = _
  rw [third_selected mode layout state ready, fourth_read_value mode layout state ready,
    third_memory mode layout state ready]
  exact collapse_memory mode layout state ready _ _ _ _ _

theorem call_location (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (fourth mode layout state).pc = Arithmetic.encodeNat mode (callStart mode layout) :=
  ReadScalarImage.pc mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready)

theorem call_top (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (fourth mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  ReadScalarImage.top_reusable mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready)

theorem call_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (fourth mode layout state).memory :=
  ReadScalarImage.finish_intact mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready)

theorem call_stack_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Calls.StackReady mode (fourth mode layout state) (Arithmetic.encodeNat mode layout.top) (Arithmetic.encodeNat mode layout.slot)
      (CallsImage.firstDisp mode (callStart mode layout) layout.top) (CallsImage.secondDisp mode (callStart mode layout) layout.top) :=
  CallsImage.stack_ready mode (callStart mode layout) layout.top layout.slot (.indirect layout.selected) _
    (call_location mode layout state ready) ready.callRanges (call_top mode layout state ready)

theorem call_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode (fourth mode layout state) (callProgram mode layout) (finish mode layout state) :=
  CallsImage.trace mode (callStart mode layout) layout.top layout.origin layout.gridBase (.indirect layout.selected) layout.whole _
    (call_location mode layout state ready) ready.callRanges ready.callFits ready.firstReady.readReady.enough ready.firstReady.readReady.gap
    ready.callWithin (call_intact mode layout state ready) ready.firstReady.readReady.topOwned

theorem call_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (callProgram mode layout) (fourth mode layout state) :=
  CallsImage.owned_run mode (callStart mode layout) layout.top layout.slot layout.origin layout.gridBase (.indirect layout.selected) layout.whole _
    (call_location mode layout state ready) ready.callRanges (call_top mode layout state ready)
    ready.firstReady.readReady.topOwned ready.firstReady.readReady.slotOwned

theorem before_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (beforeProgram mode layout state) (fourth mode layout state) :=
  Fetch.trace_append mode (Fetch.trace_append mode (Fetch.trace_append mode
    (ReadScalarImage.trace mode .store (firstLayout mode layout) state ready.firstReady)
    (ReadScalarImage.trace mode .bitXor (secondLayout mode layout) _ (second_ready mode layout state ready)))
    (ReadScalarImage.trace mode .bitAnd (thirdLayout mode layout) _ (third_ready mode layout state ready)))
    (ReadScalarImage.trace mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready))

theorem before_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (beforeProgram mode layout state) state := by
  have firstRun : runForms mode (ReadScalarImage.program mode .store (firstLayout mode layout) state) state = first mode layout state :=
    ReadScalarImage.run mode .store (firstLayout mode layout) state ready.firstReady
  have secondRun : runForms mode (ReadScalarImage.program mode .store (firstLayout mode layout) state ++
      ReadScalarImage.program mode .bitXor (secondLayout mode layout) (first mode layout state)) state = second mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (ReadScalarImage.trace mode .store (firstLayout mode layout) state ready.firstReady)
      (ReadScalarImage.trace mode .bitXor (secondLayout mode layout) _ (second_ready mode layout state ready)))).symm
  have thirdRun : runForms mode (ReadScalarImage.program mode .store (firstLayout mode layout) state ++
      ReadScalarImage.program mode .bitXor (secondLayout mode layout) (first mode layout state) ++
      ReadScalarImage.program mode .bitAnd (thirdLayout mode layout) (second mode layout state)) state = third mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (Fetch.trace_append mode
      (ReadScalarImage.trace mode .store (firstLayout mode layout) state ready.firstReady)
      (ReadScalarImage.trace mode .bitXor (secondLayout mode layout) _ (second_ready mode layout state ready)))
      (ReadScalarImage.trace mode .bitAnd (thirdLayout mode layout) _ (third_ready mode layout state ready)))).symm
  rw [beforeProgram, Writes.owned_run_append, thirdRun, Writes.owned_run_append, secondRun, Writes.owned_run_append, firstRun]
  exact ⟨⟨⟨ReadScalarImage.owned_run mode .store (firstLayout mode layout) state ready.firstReady,
    ReadScalarImage.owned_run mode .bitXor (secondLayout mode layout) _ (second_ready mode layout state ready)⟩,
    ReadScalarImage.owned_run mode .bitAnd (thirdLayout mode layout) _ (third_ready mode layout state ready)⟩,
    ReadScalarImage.owned_run mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready)⟩

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (before_trace mode layout state ready) (call_trace mode layout state ready)

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode layout state) state := by
  have beforeRun : runForms mode (beforeProgram mode layout state) state = fourth mode layout state := (Fetch.trace_run_eq mode (before_trace mode layout state ready)).symm
  rw [program, Writes.owned_run_append, beforeRun]
  exact ⟨before_owned_run mode layout state ready, call_owned_run mode layout state ready⟩

theorem pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = selectedValue mode layout state := by
  rw [finish]
  have target := CallsImage.target_pc mode (callStart mode layout) layout.top (.indirect layout.selected) (fourth mode layout state)
    (call_location mode layout state ready) ready.callRanges
  change (Calls.called mode (fourth mode layout state) _ _ (callTarget mode layout)).pc = load mode (fourth mode layout state).memory (Arithmetic.encodeNat mode layout.selected) at target
  rw [target, fourth_selected mode layout state ready]

theorem selects (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) (borrow : Bool)
    (maskValue : load mode state.memory (Arithmetic.encodeNat mode layout.mask) = Arithmetic.sbbZero mode borrow) :
    (finish mode layout state).pc = if borrow then load mode state.memory (Arithmetic.encodeNat mode layout.terminal)
      else load mode state.memory (Arithmetic.encodeNat mode layout.continuation) := by
  rw [pc mode layout state ready, selectedValue, maskValue, Arithmetic.xor_mask_select]

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.slot :=
  Calls.called_stack mode _ _ _ _ _ _ (call_stack_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).carry = false := by
  rw [finish, Calls.called_carry]
  exact ReadScalarImage.xor_carry mode (fourthLayout mode layout) _ (fourth_ready mode layout state ready)

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.continuation) := by
  rw [finish, Calls.called_accumulator, fourth, ReadScalarImage.accumulator mode .bitXor (fourthLayout mode layout) _ (fourth_ready mode layout state ready)]
  exact fourth_read_value mode layout state ready

theorem call_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode (fourth mode layout state).memory layout.slot (callerEnd mode layout) := by
  rw [finish, Calls.called_memory mode _ _ _ _ _ _ (call_stack_ready mode layout state ready)]
  rw [callTarget, CallsImage.return_next mode (callStart mode layout) layout.top (.indirect layout.selected) _ (call_location mode layout state ready),
    Arithmetic.encode_nat_toNat mode layout.slot ready.firstReady.readReady.slotFits]
  rfl

/-- All intermediate return words and selector writes are overwritten. The
complete final byte memory contains exactly the chosen word and caller-end IP. -/
theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.slot (callerEnd mode layout)) layout.selected (selectedValue mode layout state) := by
  rw [call_memory mode layout state ready, fourth_memory mode layout state ready,
    Writes.put_words_commute mode _ layout.selected layout.slot _ _ (selected_slot_separate mode layout state ready),
    Writes.put_word_overwrite]

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideSelected : Not (ByteMemory.Inside layout.selected mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.slot mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [memory_effect mode layout state ready]
  unfold ByteMemory.putWord
  rw [ByteMemory.put_frame _ _ _ position (by simpa using outsideSelected),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot)]

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.firstReady.readReady.enough ready.firstReady.readReady.gap
    ready.firstReady.readReady.intact (owned_run mode layout state ready) (trace mode layout state ready)

theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notSelected : Not (observed = Arithmetic.encodeNat mode layout.selected)) (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  have slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot) := ready.firstReady.readReady.slotOwned
  rw [call_memory mode layout state ready, ← Arithmetic.encode_nat_toNat mode layout.slot ready.firstReady.readReady.slotFits]
  rw [Writes.load_frame mode _ _ observed _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.firstReady.readReady.gap owned slotOwned notSlot)]
  exact fourth_load_frame mode layout state ready observed owned notSelected notSlot

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  have topOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.top) := ready.firstReady.readReady.topOwned
  rw [load_frame mode layout state ready _ topOwned ready.firstReady.targetNotTop ready.firstReady.readReady.topDifferent]
  exact ready.firstReady.readReady.topValue

theorem selected_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.selected) = selectedValue mode layout state := by
  have selectedOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.selected) := ready.firstReady.scalarSetup.owned
  have slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot) := ready.firstReady.readReady.slotOwned
  rw [call_memory mode layout state ready, ← Arithmetic.encode_nat_toNat mode layout.slot ready.firstReady.readReady.slotFits,
    Writes.load_frame mode _ _ _ _
      (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.firstReady.readReady.gap selectedOwned slotOwned ready.firstReady.targetNotSlot)]
  exact fourth_selected mode layout state ready

theorem slot_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.slot) = callerEnd mode layout := by
  have effect : (finish mode layout state).memory = ByteMemory.putWord mode (fourth mode layout state).memory
      (Arithmetic.encodeNat mode layout.slot).toNat (callerEnd mode layout) := by
    rw [Arithmetic.encode_nat_toNat mode layout.slot ready.firstReady.readReady.slotFits]
    exact call_memory mode layout state ready
  rw [effect, load_put_word]

theorem run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    runForms mode (program mode layout state) state = finish mode layout state := (Fetch.trace_run_eq mode (trace mode layout state ready)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 47 := by
  simp only [program, beforeProgram, List.length_append, ReadScalarImage.program_count, callProgram, Calls.program,
    List.length_cons, List.length_nil]

end SmcTuring.Native.GuardSelectionImage
