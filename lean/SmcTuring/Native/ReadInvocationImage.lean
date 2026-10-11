module
public import SmcTuring.Native.ReadCalleeImage

public section

namespace SmcTuring.Native.ReadInvocationImage

open Execution ControlImage

structure Layout (mode : Mode) where
  caller : Nat
  callee : Nat
  top : Nat
  slot : Nat
  origin : Nat
  gridBase : Nat
  initial : Word mode
  whole : List (SpacedPacking.Piece mode)

@[expose] def callerTarget (mode : Mode) (layout : Layout mode) : Calls.Target :=
  CallsImage.callTarget mode layout.caller (.relative layout.callee)

@[expose] def afterCaller (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Calls.called mode state (CallsImage.firstDisp mode layout.caller layout.top)
    (CallsImage.secondDisp mode layout.caller layout.top) (callerTarget mode layout)

@[expose] def calleeParams (mode : Mode) (layout : Layout mode) : ReadCallee.Params mode :=
  ReadCalleeImage.params mode layout.callee layout.top layout.slot

@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadCallee.finish mode (calleeParams mode layout) (afterCaller mode layout state)

@[expose] def callerProgram (mode : Mode) (layout : Layout mode) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode layout.caller layout.top)
    (CallsImage.secondDisp mode layout.caller layout.top) (callerTarget mode layout)

@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  callerProgram mode layout ++ ReadCallee.program mode (calleeParams mode layout) (afterCaller mode layout state)

@[expose] def callerEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (layout.caller + CallsImage.totalSize mode (.relative layout.callee))

@[expose] def calleeEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (layout.callee + ReadCalleeImage.totalSize mode)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode layout.caller
  callerRanges : CallsImage.Ranges mode layout.caller layout.top (.relative layout.callee)
  calleeRanges : ReadCalleeImage.Ranges mode layout.callee layout.top layout.slot
  callerFits : layout.caller + CallsImage.totalSize mode (.relative layout.callee) < 2 ^ (8 * mode.wordBytes)
  calleeFits : layout.callee + ReadCalleeImage.totalSize mode < 2 ^ (8 * mode.wordBytes)
  slotFits : layout.slot < 2 ^ (8 * mode.wordBytes)
  enough : moffsOperandOffset mode <= layout.gridBase
  gap : layout.origin + SpacedPacking.size mode layout.whole <= layout.gridBase - moffsOperandOffset mode
  callerWithin : Fragment.Within mode
    (ControlPacking.place mode layout.caller (CallsImage.packets mode layout.caller layout.top (.relative layout.callee)))
    (SpacedPacking.place mode layout.origin layout.whole)
  calleeWithin : Fragment.Within mode
    (ControlPacking.place mode layout.callee (ReadCalleeImage.packets mode layout.callee layout.top layout.slot layout.initial))
    (SpacedPacking.place mode layout.origin layout.whole)
  intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase state.memory
  topValue : load mode state.memory (Arithmetic.encodeNat mode layout.top) =
    Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes
  topOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.top)
  slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot)
  pointerOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase
    (load mode state.memory (ReaderImage.label mode layout.callee))
  topDifferent : Not (Arithmetic.encodeNat mode layout.top = Arithmetic.encodeNat mode layout.slot)
  labelDifferent : Not (ReaderImage.label mode layout.callee = Arithmetic.encodeNat mode layout.slot)

/-- A computed reader pointer may replace the original pointer. Its ownership
is checked in the actual input; all placement and reusable top setup is static. -/
theorem transport_ready_pointer (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.caller)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.top) = load mode original.memory (Arithmetic.encodeNat mode layout.top))
    (pointerOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (load mode actual.memory (ReaderImage.label mode layout.callee))) : Ready mode layout actual :=
  ⟨location, ready.callerRanges, ready.calleeRanges, ready.callerFits, ready.calleeFits,
    ready.slotFits, ready.enough, ready.gap, ready.callerWithin, ready.calleeWithin, intact,
    topFrame.trans ready.topValue, ready.topOwned, ready.slotOwned, pointerOwned, ready.topDifferent, ready.labelDifferent⟩

/-- Transfer the static invocation setup to an executed state. The two memory
frames retain the reusable stack top and the reader's current pointer. -/
theorem transport_ready (mode : Mode) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.caller)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.top) =
      load mode original.memory (Arithmetic.encodeNat mode layout.top))
    (labelFrame : load mode actual.memory (ReaderImage.label mode layout.callee) =
      load mode original.memory (ReaderImage.label mode layout.callee)) : Ready mode layout actual := by
  refine ⟨location, ready.callerRanges, ready.calleeRanges, ready.callerFits, ready.calleeFits,
    ready.slotFits, ready.enough, ready.gap, ready.callerWithin, ready.calleeWithin, intact,
    topFrame.trans ready.topValue, ready.topOwned, ready.slotOwned, ?_, ready.topDifferent, ready.labelDifferent⟩
  rw [labelFrame]
  exact ready.pointerOwned

theorem caller_run (mode : Mode) (layout : Layout mode) (state : State mode) :
    runForms mode (callerProgram mode layout) state = afterCaller mode layout state := rfl

theorem caller_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Calls.StackReady mode state (Arithmetic.encodeNat mode layout.top) (Arithmetic.encodeNat mode layout.slot)
      (CallsImage.firstDisp mode layout.caller layout.top) (CallsImage.secondDisp mode layout.caller layout.top) :=
  CallsImage.stack_ready mode layout.caller layout.top layout.slot (.relative layout.callee) state
    ready.location ready.callerRanges ready.topValue

theorem caller_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).pc = Arithmetic.encodeNat mode layout.callee :=
  CallsImage.target_pc mode layout.caller layout.top (.relative layout.callee) state ready.location ready.callerRanges

theorem caller_memory (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (afterCaller mode layout state).memory = ByteMemory.putWord mode state.memory
      (Arithmetic.encodeNat mode layout.slot).toNat (callerEnd mode layout) := by
  rw [afterCaller, Calls.called_memory mode state _ _ _ _ _ (caller_ready mode layout state ready)]
  unfold callerTarget
  rw [CallsImage.return_next mode layout.caller layout.top (.relative layout.callee) state ready.location]
  rfl

theorem caller_return_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.slot) = callerEnd mode layout := by
  rw [caller_memory mode layout state ready, load_put_word]

theorem label_owned (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (ReaderImage.label mode layout.callee) :=
  Or.inl (ReaderView.label_owned mode layout.callee layout.origin layout.initial layout.whole
    (ReadCalleeImage.reader_fits mode layout.callee ready.calleeFits)
    (Fragment.within_trans mode _ _ _ (ReadCalleeImage.reader_within mode layout.callee layout.top layout.slot layout.initial)
      ready.calleeWithin))

theorem caller_label (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (ReaderImage.label mode layout.callee) =
      load mode state.memory (ReaderImage.label mode layout.callee) := by
  rw [caller_memory mode layout state ready]
  exact Writes.load_frame mode state.memory _ _ _ (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase
    _ _ ready.gap (label_owned mode layout state ready) ready.slotOwned ready.labelDifferent)

theorem caller_top (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterCaller mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [caller_memory mode layout state ready, Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
      ready.topOwned ready.slotOwned ready.topDifferent)]
  exact ready.topValue

theorem caller_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (callerProgram mode layout) (afterCaller mode layout state) :=
  CallsImage.trace mode layout.caller layout.top layout.origin layout.gridBase (.relative layout.callee) layout.whole state
    ready.location ready.callerRanges ready.callerFits ready.enough ready.gap ready.callerWithin ready.intact ready.topOwned

theorem caller_owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (callerProgram mode layout) state :=
  CallsImage.owned_run mode layout.caller layout.top layout.slot layout.origin layout.gridBase (.relative layout.callee)
    layout.whole state ready.location ready.callerRanges ready.topValue ready.topOwned ready.slotOwned

theorem caller_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (afterCaller mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (caller_owned_run mode layout state ready) (caller_trace mode layout state ready)

theorem callee_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadCallee.Ready mode (calleeParams mode layout) (afterCaller mode layout state) :=
  ReadCalleeImage.ready mode layout.callee layout.top layout.slot (afterCaller mode layout state)
    (caller_pc mode layout state ready) ready.calleeRanges (caller_top mode layout state ready)

theorem callee_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode (afterCaller mode layout state)
      (ReadCallee.program mode (calleeParams mode layout) (afterCaller mode layout state)) (finish mode layout state) := by
  apply ReadCalleeImage.trace mode layout.callee layout.top layout.slot layout.origin layout.gridBase layout.initial
    layout.whole (afterCaller mode layout state) (caller_pc mode layout state ready) ready.calleeRanges ready.calleeFits
    ready.enough ready.gap ready.calleeWithin (caller_intact mode layout state ready)
  · rw [caller_label mode layout state ready]; exact ready.pointerOwned
  · exact ready.topOwned

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (caller_trace mode layout state ready) (callee_trace mode layout state ready)

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode layout state) state := by
  rw [program, Writes.owned_run_append, caller_run]
  constructor
  · exact caller_owned_run mode layout state ready
  · apply ReadCalleeImage.owned_run mode layout.callee layout.top layout.slot layout.origin layout.gridBase layout.initial
      layout.whole (afterCaller mode layout state) (caller_pc mode layout state ready) ready.calleeRanges ready.calleeFits
      ready.calleeWithin (caller_top mode layout state ready)
    · rw [caller_label mode layout state ready]; exact ready.pointerOwned
    · exact ready.topOwned
    · exact ready.slotOwned

theorem return_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = callerEnd mode layout := by
  rw [finish, ReadCallee.target_pc mode _ _ (callee_ready mode layout state ready)]
  exact caller_return_word mode layout state ready

theorem return_position (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc.toNat = layout.caller + CallsImage.totalSize mode (.relative layout.callee) := by
  rw [return_pc mode layout state ready]
  exact Arithmetic.encode_nat_toNat mode _ ready.callerFits

theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode state.memory layout.slot (calleeEnd mode layout) := by
  rw [finish, calleeParams, ReadCalleeImage.memory_effect mode layout.callee layout.top layout.slot (afterCaller mode layout state)
    (caller_pc mode layout state ready) ready.calleeRanges ready.slotFits (caller_top mode layout state ready),
    caller_memory mode layout state ready, Arithmetic.encode_nat_toNat mode _ ready.slotFits, Writes.put_word_overwrite]
  rfl

/-- Loading the return field itself returns the caller's just-pushed IP.
Every other owned source field retains its pre-invocation value. -/
theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator =
      if load mode state.memory (ReaderImage.label mode layout.callee) = Arithmetic.encodeNat mode layout.slot
      then callerEnd mode layout else load mode state.memory (load mode state.memory (ReaderImage.label mode layout.callee)) := by
  rw [finish, ReadCallee.accumulator mode _ _ (callee_ready mode layout state ready)]
  have pointer : load mode (afterCaller mode layout state).memory (calleeParams mode layout).label =
      load mode state.memory (ReaderImage.label mode layout.callee) := caller_label mode layout state ready
  rw [pointer, caller_memory mode layout state ready]
  by_cases same : load mode state.memory (ReaderImage.label mode layout.callee) = Arithmetic.encodeNat mode layout.slot
  · rw [ite_eq_left same, same, load_put_word]
  · rw [ite_eq_right same]
    exact Writes.load_frame mode state.memory _ _ _
      (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
        ready.pointerOwned ready.slotOwned same)

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.slot :=
  ReadCallee.stack mode _ _ (callee_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).carry = state.carry := by
  rw [finish, ReadCallee.carry]
  exact Calls.called_carry mode state _ _ _

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  ReadCalleeImage.top_reusable mode layout.callee layout.top layout.slot layout.origin layout.gridBase layout.whole
    (afterCaller mode layout state) (caller_pc mode layout state ready) ready.calleeRanges ready.gap
    (caller_top mode layout state ready) ready.topOwned ready.slotOwned ready.topDifferent

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (owned_run mode layout state ready) (trace mode layout state ready)

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outside : Not (ByteMemory.Inside layout.slot mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [memory_effect mode layout state ready]
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

/-- The round trip writes only the owned return field. Other distinct owned
words have disjoint byte spans, so their complete loaded values are preserved. -/
theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (observedOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (different : Not (observed = Arithmetic.encodeNat mode layout.slot)) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [memory_effect mode layout state ready, ← Arithmetic.encode_nat_toNat mode layout.slot ready.slotFits]
  exact Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap observedOwned ready.slotOwned different)

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) :
    (program mode layout state).length = 10 := rfl

end SmcTuring.Native.ReadInvocationImage
