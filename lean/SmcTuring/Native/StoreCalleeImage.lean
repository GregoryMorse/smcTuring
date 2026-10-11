module
public import SmcTuring.Native.ReadInvocationImage

public section

namespace SmcTuring.Native.StoreCalleeImage

open Execution ControlImage

structure Layout (mode : Mode) where
  body : Nat
  top : Nat
  slot : Nat
  origin : Nat
  gridBase : Nat
  initial : Word mode
  whole : List (SpacedPacking.Piece mode)

/-- Store calls enter the very same mutable MOFFS instruction used by the
reader's fourth operation. No duplicate address operand is introduced. -/
@[expose] def entryPC (mode : Mode) (layout : Layout mode) : Nat := layout.body + ReaderImage.prefixSize mode
@[expose] def label (mode : Mode) (layout : Layout mode) : Word mode := ReaderImage.label mode layout.body
@[expose] def target (mode : Mode) (layout : Layout mode) (state : State mode) : Word mode := load mode state.memory (label mode layout)
@[expose] def stored (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  execute mode (.moffs (target mode layout state)) state

@[expose] def callTarget (mode : Mode) (layout : Layout mode) : Calls.Target :=
  CallsImage.callTarget mode (ReadCalleeImage.callStart mode layout.body) (.indirect layout.slot)

@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  Calls.called mode (stored mode layout state) (CallsImage.firstDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top)
    (CallsImage.secondDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top) (callTarget mode layout)

@[expose] def callProgram (mode : Mode) (layout : Layout mode) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top)
    (CallsImage.secondDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top) (callTarget mode layout)

@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  [.moffs (target mode layout state)] ++ callProgram mode layout

@[expose] def calleeEnd (mode : Mode) (layout : Layout mode) : Word mode :=
  Arithmetic.encodeNat mode (layout.body + ReadCalleeImage.totalSize mode)

structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode (entryPC mode layout)
  ranges : ReadCalleeImage.Ranges mode layout.body layout.top layout.slot
  bodyFits : layout.body + ReadCalleeImage.totalSize mode < 2 ^ (8 * mode.wordBytes)
  slotFits : layout.slot < 2 ^ (8 * mode.wordBytes)
  enough : moffsOperandOffset mode <= layout.gridBase
  gap : layout.origin + SpacedPacking.size mode layout.whole <= layout.gridBase - moffsOperandOffset mode
  within : Fragment.Within mode
    (ControlPacking.place mode layout.body (ReadCalleeImage.packets mode layout.body layout.top layout.slot layout.initial))
    (SpacedPacking.place mode layout.origin layout.whole)
  intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase state.memory
  topValue : load mode state.memory (Arithmetic.encodeNat mode layout.top) =
    Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes
  topOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.top)
  slotOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.slot)
  pointerOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (target mode layout state)
  targetDifferentTop : Not (target mode layout state = Arithmetic.encodeNat mode layout.top)
  targetDifferentSlot : Not (target mode layout state = Arithmetic.encodeNat mode layout.slot)
  topDifferentSlot : Not (Arithmetic.encodeNat mode layout.top = Arithmetic.encodeNat mode layout.slot)

theorem store_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (stored mode layout state).pc = Arithmetic.encodeNat mode (ReadCalleeImage.callStart mode layout.body) := by
  change state.pc + Arithmetic.encodeNat mode (instructionLength mode (.moffs (target mode layout state))) = _
  rw [ready.location]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [entryPC, ReaderImage.prefixSize, ReadCalleeImage.callStart,
    ReaderImage.totalSize, instructionLength, wordPrefix, Mode.wordBytes, Nat.add_assoc]

theorem store_memory (mode : Mode) (layout : Layout mode) (state : State mode) :
    (stored mode layout state).memory = ByteMemory.putWord mode state.memory (target mode layout state).toNat state.accumulator := rfl

theorem store_top (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (stored mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [store_memory, Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
      ready.topOwned ready.pointerOwned (fun same => ready.targetDifferentTop same.symm))]
  exact ready.topValue

theorem store_return_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (stored mode layout state).memory (Arithmetic.encodeNat mode layout.slot) =
      load mode state.memory (Arithmetic.encodeNat mode layout.slot) := by
  rw [store_memory]
  exact Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
      ready.slotOwned ready.pointerOwned (fun same => ready.targetDifferentSlot same.symm))

theorem store_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (stored mode layout state).memory :=
  SpacedCombinedImage.execute_intact mode layout.whole layout.origin layout.gridBase state (.moffs (target mode layout state))
    ready.enough ready.gap ready.intact ready.pointerOwned

theorem call_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Calls.StackReady mode (stored mode layout state) (Arithmetic.encodeNat mode layout.top) (Arithmetic.encodeNat mode layout.slot)
      (CallsImage.firstDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top)
      (CallsImage.secondDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top) :=
  CallsImage.stack_ready mode (ReadCalleeImage.callStart mode layout.body) layout.top layout.slot (.indirect layout.slot)
    (stored mode layout state) (store_pc mode layout state ready) ready.ranges (store_top mode layout state ready)

theorem return_next (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    nextPC mode ((callTarget mode layout).form mode)
      (Calls.reset mode (stored mode layout state) (CallsImage.firstDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top)
        (CallsImage.secondDisp mode (ReadCalleeImage.callStart mode layout.body) layout.top)) = calleeEnd mode layout := by
  unfold callTarget
  rw [CallsImage.return_next mode (ReadCalleeImage.callStart mode layout.body) layout.top (.indirect layout.slot)
    (stored mode layout state) (store_pc mode layout state ready)]
  unfold calleeEnd
  congr 1
  cases mode <;> simp [ReadCalleeImage.callStart, ReaderImage.totalSize, CallsImage.totalSize,
    CallsImage.resetSize, ReadCalleeImage.totalSize, Nat.add_assoc]

theorem store_fetch (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.fetch mode state.memory state.pc.toNat = some (.moffs (target mode layout state)) := by
  have localMember : List.Mem (ReaderImage.lastEntry mode layout.body layout.initial)
      (ControlPacking.place mode layout.body (ReaderImage.packets mode layout.body layout.initial)) := by
    rw [ReaderImage.placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have member := ready.within _ (ReadCalleeImage.reader_within mode layout.body layout.top layout.slot layout.initial _ localMember)
  have live := Protected.fetch_moffs mode state.memory (entryPC mode layout) (ready.intact.1 _ member)
  have field := ReaderImage.label_location mode layout.body layout.initial (ReadCalleeImage.reader_fits mode layout.body ready.bodyFits)
  have fieldLocation : (ReaderImage.label mode layout.body).toNat = entryPC mode layout + moffsOperandOffset mode :=
    by simpa only [ReaderImage.lastEntry, entryPC] using field
  rw [<-fieldLocation] at live
  have entryFits : entryPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have bound := ready.bodyFits
    cases mode <;> simp [entryPC, ReaderImage.prefixSize, ReadCalleeImage.totalSize, Mode.wordBytes] at * <;> omega
  rw [ready.location, Arithmetic.encode_nat_toNat mode _ entryFits]
  exact live

theorem call_trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode (stored mode layout state) (callProgram mode layout) (finish mode layout state) :=
  CallsImage.trace mode (ReadCalleeImage.callStart mode layout.body) layout.top layout.origin layout.gridBase (.indirect layout.slot)
    layout.whole (stored mode layout state) (store_pc mode layout state ready) ready.ranges
    (ReadCalleeImage.call_fits mode layout.body layout.slot ready.bodyFits) ready.enough ready.gap
    (Fragment.within_trans mode _ _ _ (ReadCalleeImage.call_within mode layout.body layout.top layout.slot layout.initial)
      ready.within) (store_intact mode layout state ready) ready.topOwned

theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  .step (store_fetch mode layout state ready) (call_trace mode layout state ready)

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode layout state) state := by
  change And (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (target mode layout state))
    (Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (callProgram mode layout) (stored mode layout state))
  constructor
  · exact ready.pointerOwned
  · exact CallsImage.owned_run mode (ReadCalleeImage.callStart mode layout.body) layout.top layout.slot layout.origin layout.gridBase
      (.indirect layout.slot) layout.whole (stored mode layout state) (store_pc mode layout state ready) ready.ranges
      (store_top mode layout state ready) ready.topOwned ready.slotOwned

theorem return_pc (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).pc = load mode state.memory (Arithmetic.encodeNat mode layout.slot) := by
  rw [finish, callTarget, CallsImage.target_pc mode (ReadCalleeImage.callStart mode layout.body) layout.top (.indirect layout.slot)
    (stored mode layout state) (store_pc mode layout state ready) ready.ranges]
  exact store_return_word mode layout state ready

theorem memory_effect (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).memory = ByteMemory.putWord mode
      (ByteMemory.putWord mode state.memory (target mode layout state).toNat state.accumulator) layout.slot (calleeEnd mode layout) := by
  rw [finish, Calls.called_memory mode (stored mode layout state) _ _ _ _ _ (call_ready mode layout state ready),
    return_next mode layout state ready, store_memory, Arithmetic.encode_nat_toNat mode _ ready.slotFits]

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).accumulator = state.accumulator := by
  rw [finish, Calls.called_accumulator]
  rfl

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.slot :=
  Calls.called_stack mode (stored mode layout state) _ _ _ _ _ (call_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode layout state).carry = state.carry := by
  rw [finish, Calls.called_carry]
  rfl

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.top) =
      Arithmetic.encodeNat mode layout.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  Calls.called_top_word mode (stored mode layout state) _ _ _ _ _ (call_ready mode layout state ready)
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap
      ready.topOwned ready.slotOwned ready.topDifferentSlot)

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (owned_run mode layout state ready) (trace mode layout state ready)

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 4 := rfl

end SmcTuring.Native.StoreCalleeImage
