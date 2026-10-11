module
public import SmcTuring.Native.ScalarImage

public section

namespace SmcTuring.Native.BorrowMaskImage

open Execution ControlImage

structure Layout (mode : Mode) where
  start : Nat
  scratch : Nat
  mask : Nat
  zero : Nat
  reader : ReadInvocationImage.Layout mode

@[expose] def subLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨layout.start, layout.scratch, layout.reader.origin, layout.reader.gridBase, layout.reader.whole⟩

@[expose] def storeStart (mode : Mode) (layout : Layout mode) : Nat :=
  layout.reader.caller + CallsImage.totalSize mode (.relative layout.reader.callee)

@[expose] def storeLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨storeStart mode layout, layout.mask, layout.reader.origin, layout.reader.gridBase, layout.reader.whole⟩

@[expose] def sbbLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨storeStart mode layout + ScalarImage.size mode .store, layout.mask,
    layout.reader.origin, layout.reader.gridBase, layout.reader.whole⟩

/-- Proof-only view of the initial memory at the computed reader-call position.
This does not assume an executed intermediate state or an instruction trace. -/
@[expose] def readerView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode layout.reader.caller }

@[expose] def subtracted (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode .subtract (subLayout mode layout) state
@[expose] def afterRead (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadInvocationImage.finish mode layout.reader (subtracted mode layout state)
@[expose] def maskStored (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode .store (storeLayout mode layout) (afterRead mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode .subtractBorrowZero (sbbLayout mode layout) (maskStored mode layout state)

@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  ScalarImage.program mode .subtract (subLayout mode layout) ++
    ReadInvocationImage.program mode layout.reader (subtracted mode layout state) ++
    ScalarImage.program mode .store (storeLayout mode layout) ++ ScalarImage.program mode .subtractBorrowZero (sbbLayout mode layout)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  subReady : ScalarImage.Ready mode .subtract (subLayout mode layout) state
  readSetup : ReadInvocationImage.Ready mode layout.reader (readerView mode layout state)
  nextReader : layout.reader.caller = layout.start + ScalarImage.size mode .subtract
  pointer : load mode state.memory (ReaderImage.label mode layout.reader.callee) = Arithmetic.encodeNat mode layout.zero
  zeroValue : load mode state.memory (Arithmetic.encodeNat mode layout.zero) = 0
  zeroNotSlot : Not (Arithmetic.encodeNat mode layout.zero = Arithmetic.encodeNat mode layout.reader.slot)
  scratchNotTop : Not (Arithmetic.encodeNat mode layout.reader.top = Arithmetic.encodeNat mode layout.scratch)
  scratchNotLabel : Not (ReaderImage.label mode layout.reader.callee = Arithmetic.encodeNat mode layout.scratch)
  scratchNotZero : Not (Arithmetic.encodeNat mode layout.zero = Arithmetic.encodeNat mode layout.scratch)
  maskNotTop : Not (Arithmetic.encodeNat mode layout.reader.top = Arithmetic.encodeNat mode layout.mask)
  maskFits : layout.mask < 2 ^ (8 * mode.wordBytes)
  maskOwned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase (Arithmetic.encodeNat mode layout.mask)
  storeRange : mode = .x64 -> Relocation.SignedDelta (storeStart mode layout + ScalarImage.size mode .store) layout.mask
  sbbRange : mode = .x64 -> Relocation.SignedDelta
    (storeStart mode layout + ScalarImage.size mode .store + ScalarImage.size mode .subtractBorrowZero) layout.mask
  codeFits : storeStart mode layout + ScalarImage.size mode .store + ScalarImage.size mode .subtractBorrowZero < 2 ^ (8 * mode.wordBytes)
  storeMember : List.Mem (ScalarImage.entry mode .store (storeLayout mode layout)) (SpacedPacking.place mode layout.reader.origin layout.reader.whole)
  sbbMember : List.Mem (ScalarImage.entry mode .subtractBorrowZero (sbbLayout mode layout)) (SpacedPacking.place mode layout.reader.origin layout.reader.whole)

/-- Transfer original-memory setup through a computed entry PC, preserved
image and the top/reader-label/zero frames. No executed state is assumed. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode) (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.start)
    (intact : SpacedCombinedImage.Intact mode layout.reader.whole layout.reader.origin layout.reader.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.reader.top) = load mode original.memory (Arithmetic.encodeNat mode layout.reader.top))
    (labelFrame : load mode actual.memory (ReaderImage.label mode layout.reader.callee) = load mode original.memory (ReaderImage.label mode layout.reader.callee))
    (zeroFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.zero) = load mode original.memory (Arithmetic.encodeNat mode layout.zero)) : Ready mode layout actual := by
  refine ⟨?_, ?_, ready.nextReader, labelFrame.trans ready.pointer, zeroFrame.trans ready.zeroValue,
    ready.zeroNotSlot, ready.scratchNotTop, ready.scratchNotLabel, ready.scratchNotZero, ready.maskNotTop,
    ready.maskFits, ready.maskOwned, ready.storeRange, ready.sbbRange, ready.codeFits, ready.storeMember, ready.sbbMember⟩
  · exact ScalarImage.transport_ready mode .subtract (subLayout mode layout) original actual ready.subReady location intact
  · exact ReadInvocationImage.transport_ready mode layout.reader _ _ ready.readSetup rfl intact topFrame labelFrame

theorem zero_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase (Arithmetic.encodeNat mode layout.zero) := by
  have owns := ready.readSetup.pointerOwned
  change SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase
    (load mode state.memory (ReaderImage.label mode layout.reader.callee)) at owns
  rw [ready.pointer] at owns
  exact owns

theorem sub_label (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (subtracted mode layout state).memory (ReaderImage.label mode layout.reader.callee) =
      load mode state.memory (ReaderImage.label mode layout.reader.callee) :=
  ScalarImage.load_frame mode .subtract (subLayout mode layout) state ready.subReady _
    (ReadInvocationImage.label_owned mode layout.reader (readerView mode layout state) ready.readSetup) ready.scratchNotLabel

theorem sub_top (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (subtracted mode layout state).memory (Arithmetic.encodeNat mode layout.reader.top) =
      Arithmetic.encodeNat mode layout.reader.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [subtracted, ScalarImage.load_frame mode .subtract (subLayout mode layout) state ready.subReady _ ready.readSetup.topOwned ready.scratchNotTop]
  exact ready.readSetup.topValue

theorem read_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadInvocationImage.Ready mode layout.reader (subtracted mode layout state) := by
  refine ⟨?_, ready.readSetup.callerRanges, ready.readSetup.calleeRanges, ready.readSetup.callerFits,
    ready.readSetup.calleeFits, ready.readSetup.slotFits, ready.readSetup.enough, ready.readSetup.gap,
    ready.readSetup.callerWithin, ready.readSetup.calleeWithin, ?_, sub_top mode layout state ready,
    ready.readSetup.topOwned, ready.readSetup.slotOwned, ?_, ready.readSetup.topDifferent, ready.readSetup.labelDifferent⟩
  · rw [subtracted, ScalarImage.pc mode .subtract (subLayout mode layout) state ready.subReady, ready.nextReader]
    rfl
  · exact ScalarImage.finish_intact mode .subtract (subLayout mode layout) state ready.subReady
  · rw [sub_label mode layout state ready]
    exact ready.readSetup.pointerOwned

theorem read_zero (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterRead mode layout state).accumulator = 0 := by
  rw [afterRead, ReadInvocationImage.accumulator mode layout.reader _ (read_ready mode layout state ready),
    sub_label mode layout state ready, ready.pointer, ite_eq_right ready.zeroNotSlot, subtracted,
    ScalarImage.load_frame mode .subtract (subLayout mode layout) state ready.subReady _
      (zero_owned mode layout state ready) ready.scratchNotZero]
  exact ready.zeroValue

theorem store_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ScalarImage.Ready mode .store (storeLayout mode layout) (afterRead mode layout state) := by
  refine ⟨?_, ready.storeRange, ?_, ready.maskFits, ready.readSetup.enough, ready.readSetup.gap,
    ready.storeMember, ?_, ready.maskOwned⟩
  · exact ReadInvocationImage.return_pc mode layout.reader _ (read_ready mode layout state ready)
  · have bound := ready.codeFits
    change storeStart mode layout + ScalarImage.size mode .store < _
    omega
  · exact ReadInvocationImage.finish_intact mode layout.reader _ (read_ready mode layout state ready)

theorem sbb_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ScalarImage.Ready mode .subtractBorrowZero (sbbLayout mode layout) (maskStored mode layout state) := by
  refine ⟨?_, ready.sbbRange, ready.codeFits, ready.maskFits, ready.readSetup.enough, ready.readSetup.gap,
    ready.sbbMember, ?_, ready.maskOwned⟩
  · exact ScalarImage.pc mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)
  · exact ScalarImage.finish_intact mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)

theorem stored_zero (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (maskStored mode layout state).memory (Arithmetic.encodeNat mode layout.mask) = 0 := by
  change load mode (ScalarImage.finish mode .store (storeLayout mode layout) (afterRead mode layout state)).memory
    (Arithmetic.encodeNat mode (storeLayout mode layout).target) = 0
  rw [ScalarImage.written_value mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)]
  exact read_zero mode layout state ready

theorem borrow_reaches_sbb (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (maskStored mode layout state).carry = Arithmetic.unsignedBorrow
      (load mode state.memory (Arithmetic.encodeNat mode layout.scratch)) state.accumulator := by
  rw [maskStored, ScalarImage.store_carry, afterRead, ReadInvocationImage.carry,
    subtracted, ScalarImage.carry mode .subtract (subLayout mode layout) state ready.subReady]
  rfl

theorem mask (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.mask) = Arithmetic.sbbZero mode
      (Arithmetic.unsignedBorrow (load mode state.memory (Arithmetic.encodeNat mode layout.scratch)) state.accumulator) := by
  change load mode (ScalarImage.finish mode .subtractBorrowZero (sbbLayout mode layout) (maskStored mode layout state)).memory
    (Arithmetic.encodeNat mode (sbbLayout mode layout).target) = _
  rw [ScalarImage.zero_mask mode (sbbLayout mode layout) _ (sbb_ready mode layout state ready) (stored_zero mode layout state ready),
    borrow_reaches_sbb mode layout state ready]

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (Fetch.trace_append mode (Fetch.trace_append mode
    (ScalarImage.trace mode .subtract (subLayout mode layout) state ready.subReady)
    (ReadInvocationImage.trace mode layout.reader _ (read_ready mode layout state ready)))
    (ScalarImage.trace mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)))
    (ScalarImage.trace mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready))

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase) (program mode layout state) state := by
  have firstRun : runForms mode (ScalarImage.program mode .subtract (subLayout mode layout) ++
      ReadInvocationImage.program mode layout.reader (subtracted mode layout state)) state = afterRead mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (ScalarImage.trace mode .subtract (subLayout mode layout) state ready.subReady)
      (ReadInvocationImage.trace mode layout.reader _ (read_ready mode layout state ready)))).symm
  have secondRun : runForms mode (ScalarImage.program mode .subtract (subLayout mode layout) ++
      ReadInvocationImage.program mode layout.reader (subtracted mode layout state) ++ ScalarImage.program mode .store (storeLayout mode layout)) state =
      maskStored mode layout state :=
    (Fetch.trace_run_eq mode (Fetch.trace_append mode (Fetch.trace_append mode
      (ScalarImage.trace mode .subtract (subLayout mode layout) state ready.subReady)
      (ReadInvocationImage.trace mode layout.reader _ (read_ready mode layout state ready)))
      (ScalarImage.trace mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)))).symm
  rw [program, Writes.owned_run_append, secondRun, Writes.owned_run_append, firstRun,
    Writes.owned_run_append, ScalarImage.run]
  exact ⟨⟨⟨ScalarImage.owned_run mode .subtract (subLayout mode layout) state ready.subReady,
    ReadInvocationImage.owned_run mode layout.reader _ (read_ready mode layout state ready)⟩,
    ScalarImage.owned_run mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)⟩,
    ScalarImage.owned_run mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready)⟩

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = 0 := by
  rw [finish, ScalarImage.accumulator, maskStored, ScalarImage.accumulator]
  exact read_zero mode layout state ready

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.reader.slot := by
  rw [finish, ScalarImage.stack, maskStored, ScalarImage.stack]
  exact ReadInvocationImage.stack mode layout.reader _ (read_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).carry = Arithmetic.unsignedBorrow
      (load mode state.memory (Arithmetic.encodeNat mode layout.scratch)) state.accumulator := by
  rw [finish, ScalarImage.zero_carry mode (sbbLayout mode layout) _ (sbb_ready mode layout state ready) (stored_zero mode layout state ready)]
  exact borrow_reaches_sbb mode layout state ready

theorem position (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc.toNat = storeStart mode layout + ScalarImage.size mode .store + ScalarImage.size mode .subtractBorrowZero :=
  ScalarImage.position mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready)

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.reader.whole layout.reader.origin layout.reader.gridBase (finish mode layout state).memory :=
  ScalarImage.finish_intact mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready)

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.reader.top) =
      Arithmetic.encodeNat mode layout.reader.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [finish, ScalarImage.load_frame mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready) _ ready.readSetup.topOwned ready.maskNotTop, maskStored,
    ScalarImage.load_frame mode .store (storeLayout mode layout) _ (store_ready mode layout state ready) _ ready.readSetup.topOwned ready.maskNotTop]
  exact ReadInvocationImage.top_reusable mode layout.reader _ (read_ready mode layout state ready)

/-- The intermediate zero store is overwritten by SBB. All final byte changes
are the SUB scratch word, the reader return word and the computed mask word. -/
theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode
        (ByteMemory.putWord mode state.memory layout.scratch
          (load mode state.memory (Arithmetic.encodeNat mode layout.scratch) - state.accumulator))
        layout.reader.slot (ReadInvocationImage.calleeEnd mode layout.reader)) layout.mask
      (Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow
        (load mode state.memory (Arithmetic.encodeNat mode layout.scratch)) state.accumulator)) := by
  rw [finish, ScalarImage.memory_effect mode .subtractBorrowZero (sbbLayout mode layout) _ (sbb_ready mode layout state ready)]
  change ByteMemory.putWord mode (maskStored mode layout state).memory layout.mask
    (ScalarImage.value mode .subtractBorrowZero (load mode (maskStored mode layout state).memory (Arithmetic.encodeNat mode layout.mask))
      (maskStored mode layout state).accumulator (maskStored mode layout state).carry) = _
  rw [stored_zero mode layout state ready, borrow_reaches_sbb mode layout state ready]
  have maskValue (acc : Word mode) (carry : Bool) : ScalarImage.value mode .subtractBorrowZero 0 acc carry = Arithmetic.sbbZero mode carry := by
    simp [ScalarImage.value, Arithmetic.sbbZero]
  rw [maskValue, maskStored, ScalarImage.memory_effect mode .store (storeLayout mode layout) _ (store_ready mode layout state ready)]
  change ByteMemory.putWord mode (ByteMemory.putWord mode (afterRead mode layout state).memory layout.mask
    (afterRead mode layout state).accumulator) layout.mask _ = _
  rw [read_zero mode layout state ready, Writes.put_word_overwrite, afterRead,
    ReadInvocationImage.memory_effect mode layout.reader _ (read_ready mode layout state ready), subtracted,
    ScalarImage.memory_effect mode .subtract (subLayout mode layout) state ready.subReady]
  rfl

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideScratch : Not (ByteMemory.Inside layout.scratch mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.reader.slot mode.wordBytes position))
    (outsideMask : Not (ByteMemory.Inside layout.mask mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [memory_effect mode layout state ready]
  unfold ByteMemory.putWord
  rw [ByteMemory.put_frame _ _ _ position (by simpa using outsideMask),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot)]
  exact ByteMemory.put_frame _ _ _ position (by simpa using outsideScratch)

theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode)
    (observedOwned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase observed)
    (differentScratch : Not (observed = Arithmetic.encodeNat mode layout.scratch))
    (differentSlot : Not (observed = Arithmetic.encodeNat mode layout.reader.slot))
    (differentMask : Not (observed = Arithmetic.encodeNat mode layout.mask)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  have scratchFits : layout.scratch < 2 ^ (8 * mode.wordBytes) := ready.subReady.targetFits
  have scratchOwned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase
      (Arithmetic.encodeNat mode layout.scratch) := ready.subReady.owned
  have effect : (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode
        (ByteMemory.putWord mode state.memory (Arithmetic.encodeNat mode layout.scratch).toNat
          (load mode state.memory (Arithmetic.encodeNat mode layout.scratch) - state.accumulator))
        (Arithmetic.encodeNat mode layout.reader.slot).toNat (ReadInvocationImage.calleeEnd mode layout.reader))
        (Arithmetic.encodeNat mode layout.mask).toNat
      (Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow (load mode state.memory (Arithmetic.encodeNat mode layout.scratch)) state.accumulator)) := by
    rw [Arithmetic.encode_nat_toNat mode _ scratchFits, Arithmetic.encode_nat_toNat mode _ ready.readSetup.slotFits,
      Arithmetic.encode_nat_toNat mode _ ready.maskFits]
    exact memory_effect mode layout state ready
  rw [effect, Writes.load_frame mode _ _ observed _
    (Fragment.owned_fields_separate mode layout.reader.whole layout.reader.origin layout.reader.gridBase _ _ ready.readSetup.gap observedOwned ready.maskOwned differentMask),
    Writes.load_frame mode _ _ observed _
    (Fragment.owned_fields_separate mode layout.reader.whole layout.reader.origin layout.reader.gridBase _ _ ready.readSetup.gap observedOwned ready.readSetup.slotOwned differentSlot),
    Writes.load_frame mode _ _ observed _
    (Fragment.owned_fields_separate mode layout.reader.whole layout.reader.origin layout.reader.gridBase _ _ ready.readSetup.gap observedOwned scratchOwned differentScratch)]

theorem zero_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (differentMask : Not (Arithmetic.encodeNat mode layout.zero = Arithmetic.encodeNat mode layout.mask)) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.zero) = 0 := by
  rw [load_frame mode layout state ready _ (zero_owned mode layout state ready) ready.scratchNotZero ready.zeroNotSlot differentMask]
  exact ready.zeroValue

theorem pointer_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (differentMask : Not (ReaderImage.label mode layout.reader.callee = Arithmetic.encodeNat mode layout.mask)) :
    load mode (finish mode layout state).memory (ReaderImage.label mode layout.reader.callee) = Arithmetic.encodeNat mode layout.zero := by
  rw [load_frame mode layout state ready _ (ReadInvocationImage.label_owned mode layout.reader (readerView mode layout state) ready.readSetup)
    ready.scratchNotLabel ready.readSetup.labelDifferent differentMask]
  exact ready.pointer

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 13 := rfl

end SmcTuring.Native.BorrowMaskImage
