module
public import SmcTuring.Native.StoreCalleeImage

public section

namespace SmcTuring.Native.StoreInvocationImage

open Execution ControlImage

structure Layout (mode : Mode) where
  caller : Nat
  body : Nat
  top : Nat
  slot : Nat
  origin : Nat
  gridBase : Nat
  initial : Word mode
  whole : List (SpacedPacking.Piece mode)

@[expose] def calleeLayout (mode : Mode) (layout : Layout mode) : StoreCalleeImage.Layout mode :=
  ⟨layout.body, layout.top, layout.slot, layout.origin, layout.gridBase, layout.initial, layout.whole⟩

@[expose] def entryPC (mode : Mode) (layout : Layout mode) : Nat :=
  StoreCalleeImage.entryPC mode (calleeLayout mode layout)

@[expose] def callerTarget (mode : Mode) (layout : Layout mode) : Calls.Target :=
  CallsImage.callTarget mode layout.caller (.relative (entryPC mode layout))

@[expose] def afterCaller (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Calls.called mode state (CallsImage.firstDisp mode layout.caller layout.top)
    (CallsImage.secondDisp mode layout.caller layout.top) (callerTarget mode layout)

@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  StoreCalleeImage.finish mode (calleeLayout mode layout) (afterCaller mode layout state)

@[expose] def callerProgram (mode : Mode) (layout : Layout mode) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode layout.caller layout.top)
    (CallsImage.secondDisp mode layout.caller layout.top) (callerTarget mode layout)

@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  callerProgram mode layout ++ StoreCalleeImage.program mode (calleeLayout mode layout) (afterCaller mode layout state)

@[expose] def callerEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (layout.caller + CallsImage.totalSize mode (.relative (entryPC mode layout)))

@[expose] def calleeEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  StoreCalleeImage.calleeEnd mode (calleeLayout mode layout)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode layout.caller
  callerRanges : CallsImage.Ranges mode layout.caller layout.top (.relative (entryPC mode layout))
  calleeRanges : ReadCalleeImage.Ranges mode layout.body layout.top layout.slot
  callerFits : layout.caller + CallsImage.totalSize mode (.relative (entryPC mode layout)) < 2 ^ (8 * mode.wordBytes)
  bodyFits : layout.body + ReadCalleeImage.totalSize mode < 2 ^ (8 * mode.wordBytes)
  slotFits : layout.slot < 2 ^ (8 * mode.wordBytes)
  enough : moffsOperandOffset mode <= layout.gridBase
  gap : layout.origin + SpacedPacking.size mode layout.whole <= layout.gridBase - moffsOperandOffset mode
  callerWithin : Fragment.Within mode
    (ControlPacking.place mode layout.caller (CallsImage.packets mode layout.caller layout.top (.relative (entryPC mode layout))))
    (SpacedPacking.place mode layout.origin layout.whole)
  calleeWithin : Fragment.Within mode
    (ControlPacking.place mode layout.body (ReadCalleeImage.packets mode layout.body layout.top layout.slot layout.initial))
    (SpacedPacking.place mode layout.origin layout.whole)
  intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase state.memory
  topValue : load mode state.memory (Arithmetic.encodeNat mode layout.top) =
    Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes
  topOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.top)
  slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot)
  pointerOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.body))
  targetDifferentTop : Not (load mode state.memory (ReaderImage.label mode layout.body) = Arithmetic.encodeNat mode layout.top)
  targetDifferentSlot : Not (load mode state.memory (ReaderImage.label mode layout.body) = Arithmetic.encodeNat mode layout.slot)
  topDifferentSlot : Not (Arithmetic.encodeNat mode layout.top = Arithmetic.encodeNat mode layout.slot)
  labelDifferentSlot : Not (ReaderImage.label mode layout.body = Arithmetic.encodeNat mode layout.slot)

/-- A computed shared operand may replace the original pointer. Placement
and reusable stack metadata are retained; destination ownership and separation
are checked in the actual input rather than assumed from an earlier pointer. -/
theorem transport_ready_pointer (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.caller)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.top) = load mode original.memory (Arithmetic.encodeNat mode layout.top))
    (pointerOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (load mode actual.memory (ReaderImage.label mode layout.body)))
    (notTop : Not (load mode actual.memory (ReaderImage.label mode layout.body) = Arithmetic.encodeNat mode layout.top))
    (notSlot : Not (load mode actual.memory (ReaderImage.label mode layout.body) = Arithmetic.encodeNat mode layout.slot)) : Ready mode layout actual :=
  ⟨location, ready.callerRanges, ready.calleeRanges, ready.callerFits, ready.bodyFits, ready.slotFits,
    ready.enough, ready.gap, ready.callerWithin, ready.calleeWithin, intact, topFrame.trans ready.topValue,
    ready.topOwned, ready.slotOwned, pointerOwned, notTop, notSlot, ready.topDifferentSlot, ready.labelDifferentSlot⟩

theorem caller_run (mode : Mode) (layout : Layout mode) (state : State mode) :
    runForms mode (callerProgram mode layout) state = afterCaller mode layout state := rfl

theorem caller_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Calls.StackReady mode state (Arithmetic.encodeNat mode layout.top) (Arithmetic.encodeNat mode layout.slot)
      (CallsImage.firstDisp mode layout.caller layout.top) (CallsImage.secondDisp mode layout.caller layout.top) :=
  CallsImage.stack_ready mode layout.caller layout.top layout.slot (.relative (entryPC mode layout)) state
    ready.location ready.callerRanges ready.topValue

theorem caller_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).pc = Arithmetic.encodeNat mode (entryPC mode layout) :=
  CallsImage.target_pc mode layout.caller layout.top (.relative (entryPC mode layout)) state ready.location ready.callerRanges

theorem caller_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).memory = ByteMemory.putWord mode state.memory
      (Arithmetic.encodeNat mode layout.slot).toNat (callerEnd mode layout) := by
  rw [afterCaller, Calls.called_memory mode state _ _ _ _ _ (caller_ready mode layout state ready)]
  unfold callerTarget
  rw [CallsImage.return_next mode layout.caller layout.top (.relative (entryPC mode layout)) state ready.location]
  rfl

theorem caller_return_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.slot) = callerEnd mode layout := by
  rw [caller_memory mode layout state ready, load_put_word]

theorem label_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.body) :=
  Or.inl (ReaderView.label_owned mode layout.body layout.origin layout.initial layout.whole
    (ReadCalleeImage.reader_fits mode layout.body ready.bodyFits)
    (Fragment.within_trans mode _ _ _ (ReadCalleeImage.reader_within mode layout.body layout.top layout.slot layout.initial)
      ready.calleeWithin))

theorem caller_label (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (ReaderImage.label mode layout.body) =
      load mode state.memory (ReaderImage.label mode layout.body) := by
  rw [caller_memory mode layout state ready]
  exact Writes.load_frame mode state.memory _ _ _ (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase
    _ _ ready.gap (label_owned mode layout state ready) ready.slotOwned ready.labelDifferentSlot)

theorem caller_top (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [caller_memory mode layout state ready, Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
      ready.topOwned ready.slotOwned ready.topDifferentSlot)]
  exact ready.topValue

theorem caller_accumulator (mode : Mode) (layout : Layout mode) (state : State mode) :
    (afterCaller mode layout state).accumulator = state.accumulator :=
  Calls.called_accumulator mode state _ _ _

theorem caller_carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (afterCaller mode layout state).carry = state.carry :=
  Calls.called_carry mode state _ _ _

theorem caller_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (callerProgram mode layout) (afterCaller mode layout state) :=
  CallsImage.trace mode layout.caller layout.top layout.origin layout.gridBase (.relative (entryPC mode layout)) layout.whole state
    ready.location ready.callerRanges ready.callerFits ready.enough ready.gap ready.callerWithin ready.intact ready.topOwned

theorem caller_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (callerProgram mode layout) state :=
  CallsImage.owned_run mode layout.caller layout.top layout.slot layout.origin layout.gridBase (.relative (entryPC mode layout))
    layout.whole state ready.location ready.callerRanges ready.topValue ready.topOwned ready.slotOwned

theorem caller_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (afterCaller mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (caller_owned_run mode layout state ready) (caller_trace mode layout state ready)

theorem callee_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    StoreCalleeImage.Ready mode (calleeLayout mode layout) (afterCaller mode layout state) := by
  refine ⟨caller_pc mode layout state ready, ready.calleeRanges, ready.bodyFits, ready.slotFits,
    ready.enough, ready.gap, ready.calleeWithin, caller_intact mode layout state ready,
    caller_top mode layout state ready, ready.topOwned, ready.slotOwned, ?_, ?_, ?_, ready.topDifferentSlot⟩
  · simpa only [StoreCalleeImage.target, StoreCalleeImage.label, calleeLayout, caller_label mode layout state ready] using ready.pointerOwned
  · simpa only [StoreCalleeImage.target, StoreCalleeImage.label, calleeLayout, caller_label mode layout state ready] using ready.targetDifferentTop
  · simpa only [StoreCalleeImage.target, StoreCalleeImage.label, calleeLayout, caller_label mode layout state ready] using ready.targetDifferentSlot

theorem callee_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode (afterCaller mode layout state)
      (StoreCalleeImage.program mode (calleeLayout mode layout) (afterCaller mode layout state)) (finish mode layout state) :=
  StoreCalleeImage.trace mode (calleeLayout mode layout) (afterCaller mode layout state) (callee_ready mode layout state ready)

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (caller_trace mode layout state ready) (callee_trace mode layout state ready)

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode layout state) state := by
  rw [program, Writes.owned_run_append, caller_run]
  exact ⟨caller_owned_run mode layout state ready,
    StoreCalleeImage.owned_run mode (calleeLayout mode layout) (afterCaller mode layout state) (callee_ready mode layout state ready)⟩

theorem return_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = callerEnd mode layout := by
  rw [finish, StoreCalleeImage.return_pc mode _ _ (callee_ready mode layout state ready)]
  exact caller_return_word mode layout state ready

theorem return_position (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc.toNat = layout.caller + CallsImage.totalSize mode (.relative (entryPC mode layout)) := by
  rw [return_pc mode layout state ready]
  exact Arithmetic.encode_nat_toNat mode _ ready.callerFits

/-- The caller's intermediate push disappears from the final memory contract.
Only the source store and the callee's final return-field write remain. -/
theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory (load mode state.memory (ReaderImage.label mode layout.body)).toNat state.accumulator)
      layout.slot (calleeEnd mode layout) := by
  rw [finish, StoreCalleeImage.memory_effect mode _ _ (callee_ready mode layout state ready)]
  change ByteMemory.putWord mode
    (ByteMemory.putWord mode (afterCaller mode layout state).memory
      (load mode (afterCaller mode layout state).memory (ReaderImage.label mode layout.body)).toNat
      (afterCaller mode layout state).accumulator) layout.slot (calleeEnd mode layout) = _
  rw [caller_label mode layout state ready, caller_accumulator, caller_memory mode layout state ready,
    Arithmetic.encode_nat_toNat mode _ ready.slotFits]
  have separate := Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
    ready.slotOwned ready.pointerOwned (fun same => ready.targetDifferentSlot same.symm)
  rw [Arithmetic.encode_nat_toNat mode _ ready.slotFits] at separate
  rw [Writes.put_words_commute mode state.memory _ _ _ _ separate, Writes.put_word_overwrite]

/-- The final return-field write is disjoint from the actual stored field. -/
theorem written_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (load mode state.memory (ReaderImage.label mode layout.body)) = state.accumulator := by
  have separate := Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
    ready.pointerOwned ready.slotOwned ready.targetDifferentSlot
  have frame := Writes.load_frame mode
    (ByteMemory.putWord mode state.memory (load mode state.memory (ReaderImage.label mode layout.body)).toNat state.accumulator)
    (Arithmetic.encodeNat mode layout.slot) (load mode state.memory (ReaderImage.label mode layout.body)) (calleeEnd mode layout) separate
  rw [Arithmetic.encode_nat_toNat mode layout.slot ready.slotFits] at frame
  rw [memory_effect mode layout state ready]
  exact frame.trans (load_put_word mode state.memory _ state.accumulator)

/-- Other owned operand words are unchanged by the store and final slot write. -/
theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (notTarget : Not (observed = load mode state.memory (ReaderImage.label mode layout.body)))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  have slotFrame := Writes.load_frame mode
    (ByteMemory.putWord mode state.memory (load mode state.memory (ReaderImage.label mode layout.body)).toNat state.accumulator)
    (Arithmetic.encodeNat mode layout.slot) observed (calleeEnd mode layout)
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap owned ready.slotOwned notSlot)
  rw [Arithmetic.encode_nat_toNat mode layout.slot ready.slotFits] at slotFrame
  have targetFrame := Writes.load_frame mode state.memory (load mode state.memory (ReaderImage.label mode layout.body)) observed state.accumulator
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap owned ready.pointerOwned notTarget)
  rw [memory_effect mode layout state ready]
  exact slotFrame.trans targetFrame

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).accumulator = state.accumulator := by
  rw [finish, StoreCalleeImage.accumulator, caller_accumulator]

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.slot :=
  StoreCalleeImage.stack mode _ _ (callee_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).carry = state.carry := by
  rw [finish, StoreCalleeImage.carry, caller_carry]

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  StoreCalleeImage.top_reusable mode _ _ (callee_ready mode layout state ready)

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (owned_run mode layout state ready) (trace mode layout state ready)

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outsideSlot : Not (ByteMemory.Inside layout.slot mode.wordBytes position))
    (outsideTarget : Not (ByteMemory.Inside (load mode state.memory (ReaderImage.label mode layout.body)).toNat mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [memory_effect mode layout state ready]
  unfold ByteMemory.putWord
  rw [ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot)]
  exact ByteMemory.put_frame _ _ _ position (by simpa using outsideTarget)

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) :
    (program mode layout state).length = 7 := rfl

end SmcTuring.Native.StoreInvocationImage
