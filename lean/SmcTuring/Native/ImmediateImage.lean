module
public import SmcTuring.Native.SourceData
public import SmcTuring.Native.ReadScalarImage

public section

namespace SmcTuring.Native.ImmediateImage

open Execution

structure Layout (mode : Mode) where
  unit : ReadScalarImage.Layout mode
  destination : Dolan.Mov.Register
  constant : Nat
  choice : Bool
  cells : Nat

@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadScalarImage.finish mode .store layout.unit state
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  ReadScalarImage.program mode .store layout.unit state
@[expose] def sourceResult {mode : Mode} (layout : Layout mode) (source : Dolan.Mov.State) : Dolan.Mov.State :=
  { source with registers := write source.registers layout.destination (.offset layout.choice) }

/-- All placement and constant-reader setup refers to the original memory.
The register/heap representation is supplied separately and updated below. -/
structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  unit : ReadScalarImage.Ready mode .store layout.unit state
  target : layout.unit.target = SourceData.registerAddress mode layout.unit.reader.gridBase layout.destination
  capacity : SourceData.Capacity mode layout.unit.reader.gridBase layout.cells
  slotBefore : layout.unit.reader.slot < layout.unit.reader.gridBase
  points : load mode state.memory (ReaderImage.label mode layout.unit.reader.callee) = Arithmetic.encodeNat mode layout.constant
  constantValue : load mode state.memory (Arithmetic.encodeNat mode layout.constant) =
    SourceValues.encodeWord mode layout.unit.reader.gridBase (.offset layout.choice)
  constantNotSlot : Not (Arithmetic.encodeNat mode layout.constant = Arithmetic.encodeNat mode layout.unit.reader.slot)

theorem read_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    ReadScalarImage.readValue mode layout.unit state = SourceValues.encodeWord mode layout.unit.reader.gridBase (.offset layout.choice) := by
  rw [ReadScalarImage.read_value_from mode layout.unit state _ ready.points ready.constantNotSlot]
  exact ready.constantValue

theorem destination_value (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (SourceData.registerWord mode layout.unit.reader.gridBase layout.destination) =
      SourceValues.encodeWord mode layout.unit.reader.gridBase (.offset layout.choice) := by
  have stored := ReadScalarImage.written_value mode .store layout.unit state ready.unit
  change load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.unit.target) = ReadScalarImage.readValue mode layout.unit state at stored
  rw [read_value mode layout state ready, ready.target] at stored
  exact stored

theorem other_register_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (register : Dolan.Mov.Register) (different : Not (register = layout.destination)) :
    load mode (finish mode layout state).memory (SourceData.registerWord mode layout.unit.reader.gridBase register) =
      load mode state.memory (SourceData.registerWord mode layout.unit.reader.gridBase register) := by
  apply ReadScalarImage.load_frame mode .store layout.unit state ready.unit
  · exact SourceData.register_owned mode layout.unit.reader.whole layout.unit.reader.origin layout.unit.reader.gridBase layout.cells register ready.capacity
  · rw [ready.target]
    exact fun same => different (SourceData.register_injective mode layout.unit.reader.gridBase layout.cells ready.capacity same)
  · exact SourceData.register_not_before mode layout.unit.reader.gridBase layout.cells layout.unit.reader.slot register ready.capacity
      ready.unit.readReady.slotFits ready.slotBefore

theorem heap_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (pointer : Nat × Bool) (inside : pointer.1 < layout.cells) :
    load mode (finish mode layout state).memory (SourceData.heapWord mode layout.unit.reader.gridBase pointer) =
      load mode state.memory (SourceData.heapWord mode layout.unit.reader.gridBase pointer) := by
  apply ReadScalarImage.load_frame mode .store layout.unit state ready.unit
  · exact SourceData.heap_owned mode layout.unit.reader.whole layout.unit.reader.origin layout.unit.reader.gridBase layout.cells pointer ready.capacity inside
  · rw [ready.target]
    exact fun same => SourceData.register_heap_separate mode layout.unit.reader.gridBase layout.cells layout.destination pointer ready.capacity inside same.symm
  · exact SourceData.heap_not_before mode layout.unit.reader.gridBase layout.cells layout.unit.reader.slot pointer ready.capacity inside
      ready.unit.readReady.slotFits ready.slotBefore

theorem represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.unit.reader.gridBase layout.cells source state.memory) :
    SourceData.Rep mode layout.unit.reader.gridBase layout.cells (sourceResult layout source) (finish mode layout state).memory := by
  constructor
  · intro register
    by_cases same : register = layout.destination
    · subst register
      simpa only [sourceResult, read_write_same] using destination_value mode layout state ready
    · rw [other_register_frame mode layout state ready register same]
      simpa only [sourceResult, read_write_other source.registers layout.destination register (.offset layout.choice) same] using rep.registers register
  · intro pointer inside
    rw [heap_frame mode layout state ready pointer inside]
    exact rep.heap pointer inside

theorem source_step (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) :
    Dolan.Mov.execute (.immediate layout.destination (.offset layout.choice)) source = some (sourceResult layout source) := rfl

theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory layout.unit.reader.slot (ReadInvocationImage.calleeEnd mode layout.unit.reader))
      (SourceData.registerAddress mode layout.unit.reader.gridBase layout.destination)
      (SourceValues.encodeWord mode layout.unit.reader.gridBase (.offset layout.choice)) := by
  rw [finish, ReadScalarImage.memory_effect mode .store layout.unit state ready.unit]
  change ByteMemory.putWord mode (ByteMemory.putWord mode state.memory layout.unit.reader.slot _) layout.unit.target
    (ReadScalarImage.readValue mode layout.unit state) = _
  rw [read_value mode layout state ready, ready.target]

/-- The native trace implements the actual source immediate instruction and
preserves every represented heap word and every other source register. -/
structure Spec (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (start stop : State mode) : Prop where
  sourceStep : Dolan.Mov.execute (.immediate layout.destination (.offset layout.choice)) source = some (sourceResult layout source)
  represented : SourceData.Rep mode layout.unit.reader.gridBase layout.cells (sourceResult layout source) stop.memory
  trace : Fetch.Trace mode start (program mode layout start) stop
  owned : Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.unit.reader.whole layout.unit.reader.origin layout.unit.reader.gridBase) (program mode layout start) start
  pc : stop.pc = Arithmetic.encodeNat mode (ReadScalarImage.endPosition mode .store layout.unit)
  intact : SpacedCombinedImage.Intact mode layout.unit.reader.whole layout.unit.reader.origin layout.unit.reader.gridBase stop.memory
  top : load mode stop.memory (Arithmetic.encodeNat mode layout.unit.reader.top) =
    Arithmetic.encodeNat mode layout.unit.reader.slot + Arithmetic.encodeNat mode mode.wordBytes
  stack : stop.stack = Arithmetic.encodeNat mode layout.unit.reader.slot
  carry : stop.carry = start.carry
  accumulator : stop.accumulator = SourceValues.encodeWord mode layout.unit.reader.gridBase (.offset layout.choice)

theorem correct (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.unit.reader.gridBase layout.cells source state.memory) :
    Spec mode layout source state (finish mode layout state) := by
  refine ⟨source_step mode layout source, represented mode layout source state ready rep,
    ReadScalarImage.trace mode .store layout.unit state ready.unit,
    ReadScalarImage.owned_run mode .store layout.unit state ready.unit,
    ReadScalarImage.pc mode .store layout.unit state ready.unit,
    ReadScalarImage.finish_intact mode .store layout.unit state ready.unit,
    ReadScalarImage.top_reusable mode .store layout.unit state ready.unit,
    ReadScalarImage.stack mode .store layout.unit state ready.unit,
    ReadScalarImage.carry mode .store layout.unit state ready.unit, ?_⟩
  rw [finish, ReadScalarImage.accumulator mode .store layout.unit state ready.unit]
  exact read_value mode layout state ready

end SmcTuring.Native.ImmediateImage
