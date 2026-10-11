module
public import SmcTuring.Native.Calls

public section

namespace SmcTuring.Native.ReadCallee

open Execution

structure Params (mode : Mode) where
  label : Word mode
  top : Word mode
  slot : Word mode
  readFirst : BitVec 32
  readSecond : BitVec 32
  resetFirst : BitVec 32
  resetSecond : BitVec 32
  returnDisp : BitVec 32

@[expose] def readEnd (mode : Mode) (params : Params mode) (state : State mode) : State mode :=
  Reader.finish mode state params.label params.readFirst params.readSecond

@[expose] def finish (mode : Mode) (params : Params mode) (state : State mode) : State mode :=
  Calls.called mode (readEnd mode params state) params.resetFirst params.resetSecond (.indirect params.returnDisp)

@[expose] def returnNext (mode : Mode) (params : Params mode) (state : State mode) : Word mode :=
  nextPC mode (.memory .callIndirect params.returnDisp)
    (Calls.reset mode (readEnd mode params state) params.resetFirst params.resetSecond)

structure Ready (mode : Mode) (params : Params mode) (state : State mode) : Prop where
  firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc params.readFirst) state) params.readFirst = params.label
  secondHits : Reader.storeAddress mode (Reader.swapped mode state params.readFirst) params.label params.readSecond = params.label
  stack : Calls.StackReady mode (readEnd mode params state) params.top params.slot params.resetFirst params.resetSecond
  returnHits : memoryAddress mode (returnNext mode params state) params.returnDisp = params.slot

/-- Complete seven-instruction shared reader, including its reset and aliased
indirect return. The incoming return target is read before the return push. -/
theorem target_pc (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state) :
    (finish mode params state).pc = load mode state.memory params.slot := by
  unfold finish
  rw [Calls.indirect_target mode _ params.top params.slot params.resetFirst params.resetSecond
    params.returnDisp ready.stack.reset ready.returnHits]
  exact congrArg (fun memory => load mode memory params.slot)
    (Reader.finish_memory mode state params.label params.readFirst params.readSecond ready.firstHits ready.secondHits)

theorem memory_effect (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state) :
    (finish mode params state).memory = ByteMemory.putWord mode state.memory params.slot.toNat (returnNext mode params state) := by
  unfold finish
  rw [Calls.called_memory mode _ params.top params.slot params.resetFirst params.resetSecond _ ready.stack]
  change ByteMemory.putWord mode (Reader.finish mode state params.label params.readFirst params.readSecond).memory
    params.slot.toNat (returnNext mode params state) = _
  rw [Reader.finish_memory mode state params.label params.readFirst params.readSecond ready.firstHits ready.secondHits]

theorem accumulator (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state) :
    (finish mode params state).accumulator = load mode state.memory (load mode state.memory params.label) := by
  unfold finish
  rw [Calls.called_accumulator]
  exact Reader.finish_accumulator mode state params.label params.readFirst params.readSecond ready.firstHits ready.secondHits

theorem stack (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state) :
    (finish mode params state).stack = params.slot :=
  Calls.called_stack mode _ params.top params.slot params.resetFirst params.resetSecond _ ready.stack

theorem carry (mode : Mode) (params : Params mode) (state : State mode) :
    (finish mode params state).carry = state.carry := by
  unfold finish
  rw [Calls.called_carry]
  exact Reader.finish_carry mode state params.label params.readFirst params.readSecond

theorem return_word (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state) :
    load mode (finish mode params state).memory params.slot = returnNext mode params state := by
  rw [memory_effect mode params state ready]
  exact load_put_word mode state.memory params.slot _

theorem memory_frame (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state)
    (position : Nat) (outside : Not (ByteMemory.Inside params.slot.toNat mode.wordBytes position)) :
    (finish mode params state).memory position = state.memory position := by
  rw [memory_effect mode params state ready]
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

theorem top_word (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state)
    (separate : forall index : Fin mode.wordBytes,
      Not (ByteMemory.Inside params.slot.toNat mode.wordBytes (params.top.toNat + index.val))) :
    load mode (finish mode params state).memory params.top = params.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  Calls.called_top_word mode _ params.top params.slot params.resetFirst params.resetSecond _ ready.stack separate

/-- This is the expected form sequence; execution remains automatic byte fetch.
The last MOFFS form must really be present in its event's current memory. -/
@[expose] def program (mode : Mode) (params : Params mode) (state : State mode) : List (Form mode) :=
  [.memory .exchangeAcc params.readFirst, Reader.storeForm mode params.label params.readSecond,
    .exchangeIndirect, .moffs (load mode state.memory params.label)] ++
      Calls.program mode params.resetFirst params.resetSecond (.indirect params.returnDisp)

/-- Each of the seven reached instructions writes an owned code field. -/
theorem owned_run (mode : Mode) (params : Params mode) (state : State mode) (ready : Ready mode params state)
    (owned : Word mode -> Prop) (labelOwned : owned params.label)
    (pointerOwned : owned (load mode state.memory params.label)) (topOwned : owned params.top) (slotOwned : owned params.slot) :
    Writes.OwnedRun mode owned (program mode params state) state := by
  rw [program, Writes.owned_run_append]
  constructor
  · have fields := Reader.four_writes_owned mode state params.label params.readFirst params.readSecond
      ready.firstHits ready.secondHits owned labelOwned pointerOwned
    simpa only [Writes.OwnedRun, and_true, Reader.swapped, Reader.restored, Reader.dereferenced] using fields
  · change Writes.OwnedRun mode owned (Calls.program mode params.resetFirst params.resetSecond (.indirect params.returnDisp))
      (readEnd mode params state)
    exact Calls.owned_run mode _ params.top params.slot params.resetFirst params.resetSecond
      (.indirect params.returnDisp) ready.stack owned topOwned slotOwned

theorem trace_of_components (mode : Mode) (params : Params mode) (state : State mode)
    (readTrace : Fetch.Trace mode state
      [.memory .exchangeAcc params.readFirst, Reader.storeForm mode params.label params.readSecond,
        .exchangeIndirect, .moffs (load mode state.memory params.label)] (readEnd mode params state))
    (returnTrace : Fetch.Trace mode (readEnd mode params state)
      (Calls.program mode params.resetFirst params.resetSecond (.indirect params.returnDisp)) (finish mode params state)) :
    Fetch.Trace mode state (program mode params state) (finish mode params state) :=
  Fetch.trace_append mode readTrace returnTrace

/-- A live automatic-fetch callee trace has the complete loaded-value, fixed
return-slot, old-target, outside-memory and carry contracts above. -/
theorem trace_result (mode : Mode) (params : Params mode) (state result : State mode)
    (ready : Ready mode params state) (trace : Fetch.Trace mode state (program mode params state) result) :
    And (result.pc = load mode state.memory params.slot)
      (And (result.memory = ByteMemory.putWord mode state.memory params.slot.toNat (returnNext mode params state))
        (And (result.accumulator = load mode state.memory (load mode state.memory params.label))
          (And (result.stack = params.slot) (result.carry = state.carry)))) := by
  have effect := Fetch.trace_run_eq mode trace
  change result = finish mode params state at effect
  rw [effect]
  exact And.intro (target_pc mode params state ready)
    (And.intro (memory_effect mode params state ready)
      (And.intro (accumulator mode params state ready)
        (And.intro (stack mode params state ready) (carry mode params state))))

theorem program_length (mode : Mode) (params : Params mode) (state : State mode) :
    ((program mode params state).map (instructionLength mode)).sum =
      (match mode with | .x86 => 36 | .x64 => 47) := by cases mode <;> rfl

/-- A direct invocation followed by this callee returns to the caller's
complete next IP, even though the final CALL overwrites the shared slot. -/
theorem invocation_returns (mode : Mode) (params : Params mode) (state : State mode)
    (firstDisp secondDisp entryDisp : BitVec 32)
    (caller : Calls.StackReady mode state params.top params.slot firstDisp secondDisp)
    (callee : Ready mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))) :
    (finish mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))).pc =
      nextPC mode (.callRelative entryDisp) (Calls.reset mode state firstDisp secondDisp) := by
  rw [target_pc mode params _ callee]
  exact Calls.called_return_word mode state params.top params.slot firstDisp secondDisp (.relative entryDisp) caller

/-- The two writes to the return slot collapse to the callee's final return
word; every other byte of the original caller memory is restored. -/
theorem invocation_memory (mode : Mode) (params : Params mode) (state : State mode)
    (firstDisp secondDisp entryDisp : BitVec 32)
    (caller : Calls.StackReady mode state params.top params.slot firstDisp secondDisp)
    (callee : Ready mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))) :
    (finish mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))).memory =
      ByteMemory.putWord mode state.memory params.slot.toNat
        (returnNext mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))) := by
  rw [memory_effect mode params _ callee,
    Calls.called_memory mode state params.top params.slot firstDisp secondDisp (.relative entryDisp) caller,
    Writes.put_word_overwrite]

theorem invocation_carry (mode : Mode) (params : Params mode) (state : State mode) (firstDisp secondDisp entryDisp : BitVec 32) :
    (finish mode params (Calls.called mode state firstDisp secondDisp (.relative entryDisp))).carry = state.carry := by
  rw [carry, Calls.called_carry]

end SmcTuring.Native.ReadCallee
