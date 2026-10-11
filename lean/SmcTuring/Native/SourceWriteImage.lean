module
public import SmcTuring.Native.SourceData
public import SmcTuring.Native.ReadScalarImage
public import SmcTuring.Native.StoreInvocationImage

public section

namespace SmcTuring.Native.SourceWriteImage

open Execution

@[expose] def registerResult (source : Dolan.Mov.State) (destination : Dolan.Mov.Register) (value : Dolan.Mov.Word) : Dolan.Mov.State :=
  { source with registers := write source.registers destination value }

/-- The final native read/store pair implements a typed source register
update, irrespective of whether the value came from a constant or heap cell.
Every other register and every represented heap word is framed explicitly. -/
theorem register_rep (mode : Mode) (layout : ReadScalarImage.Layout mode) (cells : Nat)
    (destination : Dolan.Mov.Register) (value : Dolan.Mov.Word) (source : Dolan.Mov.State) (state : State mode)
    (ready : ReadScalarImage.Ready mode .store layout state)
    (capacity : SourceData.Capacity mode layout.reader.gridBase cells)
    (slotBefore : layout.reader.slot < layout.reader.gridBase)
    (target : layout.target = SourceData.registerAddress mode layout.reader.gridBase destination)
    (readValue : ReadScalarImage.readValue mode layout state = SourceValues.encodeWord mode layout.reader.gridBase value)
    (rep : SourceData.Rep mode layout.reader.gridBase cells source state.memory) :
    SourceData.Rep mode layout.reader.gridBase cells (registerResult source destination value)
      (ReadScalarImage.finish mode .store layout state).memory := by
  constructor
  · intro register
    by_cases same : register = destination
    · subst register
      have stored := ReadScalarImage.written_value mode .store layout state ready
      change load mode (ReadScalarImage.finish mode .store layout state).memory (Arithmetic.encodeNat mode layout.target) = ReadScalarImage.readValue mode layout state at stored
      rw [target, readValue] at stored
      simpa only [registerResult, read_write_same, SourceData.registerWord] using stored
    · have frame := ReadScalarImage.load_frame mode .store layout state ready (SourceData.registerWord mode layout.reader.gridBase register)
        (SourceData.register_owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase cells register capacity)
        (by rw [target]; exact fun equality => same (SourceData.register_injective mode layout.reader.gridBase cells capacity equality))
        (SourceData.register_not_before mode layout.reader.gridBase cells layout.reader.slot register capacity ready.readReady.slotFits slotBefore)
      rw [frame]
      simpa only [registerResult, read_write_other source.registers destination register value same] using rep.registers register
  · intro position inside
    have frame := ReadScalarImage.load_frame mode .store layout state ready (SourceData.heapWord mode layout.reader.gridBase position)
      (SourceData.heap_owned mode layout.reader.whole layout.reader.origin layout.reader.gridBase cells position capacity inside)
      (by rw [target]; exact fun equality => SourceData.register_heap_separate mode layout.reader.gridBase cells destination position capacity inside equality.symm)
      (SourceData.heap_not_before mode layout.reader.gridBase cells layout.reader.slot position capacity inside ready.readReady.slotFits slotBefore)
    rw [frame]
    exact rep.heap position inside

@[expose] def heapResult (source : Dolan.Mov.State) (position : Prod Nat Bool) (value : Dolan.Mov.Word) : Dolan.Mov.State :=
  { source with memory := write source.memory position value }

/-- The shared native store changes exactly the selected source heap word.
All source registers and other represented heap words are framed using owned
field separation; source values and register names may alias. -/
theorem heap_rep (mode : Mode) (layout : StoreInvocationImage.Layout mode) (cells : Nat)
    (position : Prod Nat Bool) (value : Dolan.Mov.Word) (source : Dolan.Mov.State) (state : State mode)
    (ready : StoreInvocationImage.Ready mode layout state)
    (capacity : SourceData.Capacity mode layout.gridBase cells) (inside : position.1 < cells)
    (slotBefore : layout.slot < layout.gridBase)
    (pointer : load mode state.memory (ReaderImage.label mode layout.body) = SourceData.heapWord mode layout.gridBase position)
    (accumulator : state.accumulator = SourceValues.encodeWord mode layout.gridBase value)
    (rep : SourceData.Rep mode layout.gridBase cells source state.memory) :
    SourceData.Rep mode layout.gridBase cells (heapResult source position value) (StoreInvocationImage.finish mode layout state).memory := by
  constructor
  · intro register
    have frame := StoreInvocationImage.load_frame mode layout state ready (SourceData.registerWord mode layout.gridBase register)
      (SourceData.register_owned mode layout.whole layout.origin layout.gridBase cells register capacity)
      (by rw [pointer]; exact SourceData.register_heap_separate mode layout.gridBase cells register position capacity inside)
      (SourceData.register_not_before mode layout.gridBase cells layout.slot register capacity ready.slotFits slotBefore)
    rw [frame]
    exact rep.registers register
  · intro observed observedInside
    by_cases same : observed = position
    · subst observed
      have stored := StoreInvocationImage.written_value mode layout state ready
      rw [pointer, accumulator] at stored
      simpa only [heapResult, read_write_same] using stored
    · have frame := StoreInvocationImage.load_frame mode layout state ready (SourceData.heapWord mode layout.gridBase observed)
        (SourceData.heap_owned mode layout.whole layout.origin layout.gridBase cells observed capacity observedInside)
        (by rw [pointer]; exact fun equality => same (SourceData.heap_injective mode layout.gridBase cells observed position capacity observedInside inside equality))
        (SourceData.heap_not_before mode layout.gridBase cells layout.slot observed capacity observedInside ready.slotFits slotBefore)
      rw [frame]
      simpa only [heapResult, read_write_other source.memory position observed value same] using rep.heap observed observedInside

end SmcTuring.Native.SourceWriteImage
