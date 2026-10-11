module
public import SmcTuring.Native.ScalarImage

public section

namespace SmcTuring.Native.ReadScalarImage

open Execution ControlImage

/-- A complete reader caller/callee round trip followed by one fixed scalar
operation. Both units share one padded control/grid placement context. -/
structure Layout (mode : Mode) where
  reader : ReadInvocationImage.Layout mode
  target : Nat

@[expose] def scalarStart (mode : Mode) (layout : Layout mode) : Nat :=
  layout.reader.caller + CallsImage.totalSize mode (.relative layout.reader.callee)
@[expose] def scalarLayout (mode : Mode) (layout : Layout mode) : ScalarImage.Layout mode :=
  ⟨scalarStart mode layout, layout.target, layout.reader.origin, layout.reader.gridBase, layout.reader.whole⟩
@[expose] def endPosition (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) : Nat :=
  scalarStart mode layout + ScalarImage.size mode op
@[expose] def scalarView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (scalarStart mode layout) }
@[expose] def afterRead (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadInvocationImage.finish mode layout.reader state
@[expose] def finish (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) : State mode :=
  ScalarImage.finish mode op (scalarLayout mode layout) (afterRead mode layout state)
@[expose] def program (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  ReadInvocationImage.program mode layout.reader state ++ ScalarImage.program mode op (scalarLayout mode layout)
@[expose] def readValue (mode : Mode) (layout : Layout mode) (state : State mode) : Word mode :=
  if load mode state.memory (ReaderImage.label mode layout.reader.callee) = Arithmetic.encodeNat mode layout.reader.slot
  then ReadInvocationImage.callerEnd mode layout.reader
  else load mode state.memory (load mode state.memory (ReaderImage.label mode layout.reader.callee))

structure Ready (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) : Prop where
  readReady : ReadInvocationImage.Ready mode layout.reader state
  scalarSetup : ScalarImage.Ready mode op (scalarLayout mode layout) (scalarView mode layout state)
  targetNotSlot : Not (Arithmetic.encodeNat mode layout.target = Arithmetic.encodeNat mode layout.reader.slot)
  targetNotTop : Not (Arithmetic.encodeNat mode layout.reader.top = Arithmetic.encodeNat mode layout.target)

/-- Static original-memory setup transfers to an executed input through its
computed PC, preserved image, and the stack-top/reader-pointer word frames. -/
theorem transport_ready (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode op layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.reader.caller)
    (intact : SpacedCombinedImage.Intact mode layout.reader.whole layout.reader.origin layout.reader.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.reader.top) =
      load mode original.memory (Arithmetic.encodeNat mode layout.reader.top))
    (labelFrame : load mode actual.memory (ReaderImage.label mode layout.reader.callee) =
      load mode original.memory (ReaderImage.label mode layout.reader.callee)) : Ready mode op layout actual := by
  refine ⟨ReadInvocationImage.transport_ready mode layout.reader original actual ready.readReady location intact topFrame labelFrame,
    ?_, ready.targetNotSlot, ready.targetNotTop⟩
  exact ScalarImage.transport_ready mode op (scalarLayout mode layout) _ _ ready.scalarSetup rfl intact

theorem scalar_ready (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    ScalarImage.Ready mode op (scalarLayout mode layout) (afterRead mode layout state) :=
  ScalarImage.transport_ready mode op (scalarLayout mode layout) _ _ ready.scalarSetup
    (ReadInvocationImage.return_pc mode layout.reader state ready.readReady)
    (ReadInvocationImage.finish_intact mode layout.reader state ready.readReady)

/-- The active reader operand may contain a newly computed owned pointer.
Neither an executed trace nor an intermediate scalar setup is supplied. -/
theorem transport_ready_pointer (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode op layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.reader.caller)
    (intact : SpacedCombinedImage.Intact mode layout.reader.whole layout.reader.origin layout.reader.gridBase actual.memory)
    (topFrame : load mode actual.memory (Arithmetic.encodeNat mode layout.reader.top) = load mode original.memory (Arithmetic.encodeNat mode layout.reader.top))
    (pointerOwned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase
      (load mode actual.memory (ReaderImage.label mode layout.reader.callee))) : Ready mode op layout actual := by
  refine ⟨ReadInvocationImage.transport_ready_pointer mode layout.reader original actual ready.readReady location intact topFrame pointerOwned,
    ?_, ready.targetNotSlot, ready.targetNotTop⟩
  exact ScalarImage.transport_ready mode op (scalarLayout mode layout) _ _ ready.scalarSetup rfl intact

theorem read_value_from (mode : Mode) (layout : Layout mode) (state : State mode) (pointer : Word mode)
    (points : load mode state.memory (ReaderImage.label mode layout.reader.callee) = pointer)
    (notSlot : Not (pointer = Arithmetic.encodeNat mode layout.reader.slot)) :
    readValue mode layout state = load mode state.memory pointer := by
  rw [readValue, points, ite_eq_right notSlot]

theorem read_accumulator (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (afterRead mode layout state).accumulator = readValue mode layout state :=
  ReadInvocationImage.accumulator mode layout.reader state ready.readReady

theorem target_before_scalar (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.target) =
      load mode state.memory (Arithmetic.encodeNat mode layout.target) := by
  have owned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase (Arithmetic.encodeNat mode layout.target) := ready.scalarSetup.owned
  exact ReadInvocationImage.load_frame mode layout.reader state ready.readReady _ owned ready.targetNotSlot

theorem trace (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Fetch.Trace mode state (program mode op layout state) (finish mode op layout state) :=
  Fetch.trace_append mode (ReadInvocationImage.trace mode layout.reader state ready.readReady)
    (ScalarImage.trace mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready))

theorem owned_run (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase)
      (program mode op layout state) state := by
  have readRun : runForms mode (ReadInvocationImage.program mode layout.reader state) state = afterRead mode layout state :=
    (Fetch.trace_run_eq mode (ReadInvocationImage.trace mode layout.reader state ready.readReady)).symm
  rw [program, Writes.owned_run_append, readRun]
  exact ⟨ReadInvocationImage.owned_run mode layout.reader state ready.readReady,
    ScalarImage.owned_run mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)⟩

theorem written_value (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    load mode (finish mode op layout state).memory (Arithmetic.encodeNat mode layout.target) =
      ScalarImage.value mode op (load mode state.memory (Arithmetic.encodeNat mode layout.target)) (readValue mode layout state) state.carry := by
  change load mode (ScalarImage.finish mode op (scalarLayout mode layout) (afterRead mode layout state)).memory
    (Arithmetic.encodeNat mode (scalarLayout mode layout).target) = _
  rw [ScalarImage.written_value mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)]
  change ScalarImage.value mode op (load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.target))
    (afterRead mode layout state).accumulator (afterRead mode layout state).carry = _
  rw [target_before_scalar mode op layout state ready, read_accumulator mode op layout state ready]
  have cf : (afterRead mode layout state).carry = state.carry := ReadInvocationImage.carry mode layout.reader state
  rw [cf]

theorem memory_effect (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.reader.slot (ReadInvocationImage.calleeEnd mode layout.reader)) layout.target
      (ScalarImage.value mode op (load mode state.memory (Arithmetic.encodeNat mode layout.target)) (readValue mode layout state) state.carry) := by
  rw [finish, ScalarImage.memory_effect mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)]
  change ByteMemory.putWord mode (afterRead mode layout state).memory layout.target
    (ScalarImage.value mode op (load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.target))
      (afterRead mode layout state).accumulator (afterRead mode layout state).carry) = _
  rw [target_before_scalar mode op layout state ready, read_accumulator mode op layout state ready]
  have cf : (afterRead mode layout state).carry = state.carry := ReadInvocationImage.carry mode layout.reader state
  rw [cf, afterRead, ReadInvocationImage.memory_effect mode layout.reader state ready.readReady]

theorem accumulator (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).accumulator = readValue mode layout state := by
  rw [finish, ScalarImage.accumulator]
  exact read_accumulator mode op layout state ready

theorem stack (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).stack = Arithmetic.encodeNat mode layout.reader.slot := by
  rw [finish, ScalarImage.stack]
  exact ReadInvocationImage.stack mode layout.reader state ready.readReady

theorem carry (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).carry = ScalarImage.carryValue mode op
      (load mode state.memory (Arithmetic.encodeNat mode layout.target)) (readValue mode layout state) state.carry := by
  rw [finish, ScalarImage.carry mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)]
  change ScalarImage.carryValue mode op (load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.target))
    (afterRead mode layout state).accumulator (afterRead mode layout state).carry = _
  rw [target_before_scalar mode op layout state ready, read_accumulator mode op layout state ready]
  have cf : (afterRead mode layout state).carry = state.carry := ReadInvocationImage.carry mode layout.reader state
  rw [cf]

theorem xor_carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode .bitXor layout state) :
    (finish mode .bitXor layout state).carry = false := carry mode .bitXor layout state ready

theorem and_carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode .bitAnd layout state) :
    (finish mode .bitAnd layout state).carry = false := carry mode .bitAnd layout state ready

theorem pc (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).pc = Arithmetic.encodeNat mode (endPosition mode op layout) :=
  ScalarImage.pc mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)

theorem position (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).pc.toNat = endPosition mode op layout :=
  ScalarImage.position mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)

theorem finish_intact (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    SpacedCombinedImage.Intact mode layout.reader.whole layout.reader.origin layout.reader.gridBase (finish mode op layout state).memory :=
  ScalarImage.finish_intact mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready)

theorem top_reusable (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    load mode (finish mode op layout state).memory (Arithmetic.encodeNat mode layout.reader.top) =
      Arithmetic.encodeNat mode layout.reader.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [finish, ScalarImage.load_frame mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready) _
    ready.readReady.topOwned ready.targetNotTop]
  exact ReadInvocationImage.top_reusable mode layout.reader state ready.readReady

theorem load_frame (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase observed)
    (notTarget : Not (observed = Arithmetic.encodeNat mode layout.target))
    (notSlot : Not (observed = Arithmetic.encodeNat mode layout.reader.slot)) :
    load mode (finish mode op layout state).memory observed = load mode state.memory observed := by
  rw [finish, ScalarImage.load_frame mode op (scalarLayout mode layout) _ (scalar_ready mode op layout state ready) observed owned notTarget]
  exact ReadInvocationImage.load_frame mode layout.reader state ready.readReady observed owned notSlot

theorem memory_frame (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state)
    (position : Nat) (outsideTarget : Not (ByteMemory.Inside layout.target mode.wordBytes position))
    (outsideSlot : Not (ByteMemory.Inside layout.reader.slot mode.wordBytes position)) :
    (finish mode op layout state).memory position = state.memory position := by
  rw [memory_effect mode op layout state ready]
  unfold ByteMemory.putWord
  rw [ByteMemory.put_frame _ _ _ position (by simpa using outsideTarget),
    ByteMemory.put_frame _ _ _ position (by simpa using outsideSlot)]

theorem run (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    runForms mode (program mode op layout state) state = finish mode op layout state :=
  (Fetch.trace_run_eq mode (trace mode op layout state ready)).symm

theorem program_count (mode : Mode) (op : ScalarImage.Op) (layout : Layout mode) (state : State mode) :
    (program mode op layout state).length = 11 := by
  simp only [program, List.length_append, ReadInvocationImage.program_count, ScalarImage.program_count]

end SmcTuring.Native.ReadScalarImage
