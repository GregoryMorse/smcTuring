module
public import SmcTuring.Native.Reader

public section

namespace SmcTuring.Native.Calls

open Execution

/-- The native generator uses only these two near-CALL forms. -/
inductive Target where
  | relative (displacement : BitVec 32)
  | indirect (displacement : BitVec 32)

@[expose] def Target.form (mode : Mode) : Target -> Form mode
  | .relative displacement => .callRelative displacement
  | .indirect displacement => .memory .callIndirect displacement

/-- The transfer target is evaluated from the pre-push state. -/
@[expose] def Target.value (mode : Mode) (target : Target) (state : State mode) : Word mode :=
  let next := nextPC mode (target.form mode) state
  match target with
  | .relative displacement => next + displacementWord mode displacement
  | .indirect displacement => load mode state.memory (memoryAddress mode next displacement)

@[expose] def exchanged (mode : Mode) (state : State mode) (firstDisp : BitVec 32) : State mode :=
  execute mode (.memory .exchangeStack firstDisp) state

@[expose] def reset (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) : State mode :=
  execute mode (.memory .storeStack secondDisp) (exchanged mode state firstDisp)

@[expose] def called (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) (target : Target) : State mode :=
  execute mode (target.form mode) (reset mode state firstDisp secondDisp)

structure ResetReady (mode : Mode) (state : State mode) (top : Word mode) (firstDisp secondDisp : BitVec 32) : Prop where
  firstHits : memoryAddress mode (nextPC mode (.memory .exchangeStack firstDisp) state) firstDisp = top
  secondHits : memoryAddress mode (nextPC mode (.memory .storeStack secondDisp) (exchanged mode state firstDisp)) secondDisp = top

/-- Capacity and physical validity are independent realization conditions.
This premise states the native StackTop word, including modular word arithmetic. -/
structure StackReady (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32) : Prop where
  reset : ResetReady mode state top firstDisp secondDisp
  topValue : load mode state.memory top = slot + Arithmetic.encodeNat mode mode.wordBytes

theorem exchange_effect (mode : Mode) (state : State mode) (top : Word mode) (firstDisp : BitVec 32)
    (hits : memoryAddress mode (nextPC mode (.memory .exchangeStack firstDisp) state) firstDisp = top) :
    exchanged mode state firstDisp =
      { state with pc := nextPC mode (.memory .exchangeStack firstDisp) state, stack := load mode state.memory top, memory := ByteMemory.putWord mode state.memory top.toNat state.stack } := by
  simp only [exchanged, execute, executeMemory, hits]

theorem store_effect (mode : Mode) (state : State mode) (top : Word mode) (secondDisp : BitVec 32)
    (hits : memoryAddress mode (nextPC mode (.memory .storeStack secondDisp) state) secondDisp = top) :
    execute mode (.memory .storeStack secondDisp) state =
      storeState mode state (nextPC mode (.memory .storeStack secondDisp) state) top state.stack state.carry := by
  simp only [execute, executeMemory, hits]

/-- Two reset instructions restore every StackTop byte, for any incoming SP. -/
theorem reset_memory (mode : Mode) (state : State mode) (top : Word mode) (firstDisp secondDisp : BitVec 32)
    (ready : ResetReady mode state top firstDisp secondDisp) :
    (reset mode state firstDisp secondDisp).memory = state.memory := by
  unfold reset
  rw [store_effect mode _ top secondDisp ready.secondHits, exchange_effect mode state top firstDisp ready.firstHits]
  change ByteMemory.putWord mode (ByteMemory.putWord mode state.memory top.toNat state.stack)
    top.toNat (load mode state.memory top) = state.memory
  rw [Writes.put_word_overwrite, Writes.put_word_back]

theorem reset_stack (mode : Mode) (state : State mode) (top : Word mode) (firstDisp secondDisp : BitVec 32)
    (ready : ResetReady mode state top firstDisp secondDisp) :
    (reset mode state firstDisp secondDisp).stack = load mode state.memory top := by
  unfold reset
  rw [store_effect mode _ top secondDisp ready.secondHits, exchange_effect mode state top firstDisp ready.firstHits]
  rfl

theorem reset_accumulator (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) :
    (reset mode state firstDisp secondDisp).accumulator = state.accumulator := rfl

theorem reset_carry (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) :
    (reset mode state firstDisp secondDisp).carry = state.carry := rfl

/-- Every reset places the subsequent CALL's push at the fixed code slot.
The arbitrary incoming SP cannot cause a growing ordinary stack. -/
theorem stack_slot (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32)
    (ready : StackReady mode state top slot firstDisp secondDisp) :
    (reset mode state firstDisp secondDisp).stack - Arithmetic.encodeNat mode mode.wordBytes = slot := by
  rw [reset_stack mode state top firstDisp secondDisp ready.reset, ready.topValue, BitVec.add_sub_cancel]

/-- Complete state effect of reset followed by either selected near CALL. -/
theorem called_effect (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32)
    (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp) :
    called mode state firstDisp secondDisp target =
      { reset mode state firstDisp secondDisp with pc := target.value mode (reset mode state firstDisp secondDisp), stack := slot, memory := ByteMemory.putWord mode state.memory slot.toNat (nextPC mode (target.form mode) (reset mode state firstDisp secondDisp)) } := by
  cases target <;>
    simp only [called, Target.form, Target.value, execute, executeMemory, callState,
      stack_slot mode state top slot firstDisp secondDisp ready,
      reset_memory mode state top firstDisp secondDisp ready.reset]

theorem called_memory (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32)
    (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp) :
    (called mode state firstDisp secondDisp target).memory =
      ByteMemory.putWord mode state.memory slot.toNat (nextPC mode (target.form mode) (reset mode state firstDisp secondDisp)) := by
  rw [called_effect mode state top slot firstDisp secondDisp target ready]

theorem called_stack (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32)
    (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp) :
    (called mode state firstDisp secondDisp target).stack = slot := by
  rw [called_effect mode state top slot firstDisp secondDisp target ready]

theorem called_accumulator (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) (target : Target) :
    (called mode state firstDisp secondDisp target).accumulator = state.accumulator := by cases target <;> rfl

theorem called_carry (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) (target : Target) :
    (called mode state firstDisp secondDisp target).carry = state.carry := by cases target <;> rfl

theorem called_return_word (mode : Mode) (state : State mode) (top slot : Word mode) (firstDisp secondDisp : BitVec 32)
    (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp) :
    load mode (called mode state firstDisp secondDisp target).memory slot =
      nextPC mode (target.form mode) (reset mode state firstDisp secondDisp) := by
  rw [called_memory mode state top slot firstDisp secondDisp target ready]
  exact load_put_word mode state.memory slot _

theorem indirect_target (mode : Mode) (state : State mode) (top field : Word mode)
    (firstDisp secondDisp callDisp : BitVec 32) (ready : ResetReady mode state top firstDisp secondDisp)
    (hits : memoryAddress mode (nextPC mode (.memory .callIndirect callDisp) (reset mode state firstDisp secondDisp)) callDisp = field) :
    (called mode state firstDisp secondDisp (.indirect callDisp)).pc = load mode state.memory field := by
  change (execute mode (.memory .callIndirect callDisp) (reset mode state firstDisp secondDisp)).pc = _
  rw [indirect_call_target, hits, reset_memory mode state top firstDisp secondDisp ready]

/-- The aliased return CALL jumps to the old slot value and then replaces the
same slot with its own complete next IP. No RET or external stack is used. -/
theorem aliased_return (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp callDisp : BitVec 32) (ready : StackReady mode state top slot firstDisp secondDisp)
    (hits : memoryAddress mode (nextPC mode (.memory .callIndirect callDisp) (reset mode state firstDisp secondDisp)) callDisp = slot) :
    And ((called mode state firstDisp secondDisp (.indirect callDisp)).pc = load mode state.memory slot)
      (load mode (called mode state firstDisp secondDisp (.indirect callDisp)).memory slot =
        nextPC mode (.memory .callIndirect callDisp) (reset mode state firstDisp secondDisp)) :=
  And.intro (indirect_target mode state top slot firstDisp secondDisp callDisp ready.reset hits)
    (called_return_word mode state top slot firstDisp secondDisp (.indirect callDisp) ready)

theorem called_frame (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp)
    (position : Nat) (outside : Not (ByteMemory.Inside slot.toNat mode.wordBytes position)) :
    (called mode state firstDisp secondDisp target).memory position = state.memory position := by
  rw [called_memory mode state top slot firstDisp secondDisp target ready]
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

/-- The StackTop constant survives each call when its bytes are separate from
the return slot. This is the reusable stack invariant, not a saved host stack. -/
theorem called_top_word (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp)
    (separate : forall index : Fin mode.wordBytes,
      Not (ByteMemory.Inside slot.toNat mode.wordBytes (top.toNat + index.val))) :
    load mode (called mode state firstDisp secondDisp target).memory top =
      slot + Arithmetic.encodeNat mode mode.wordBytes := by
  rw [called_memory mode state top slot firstDisp secondDisp target ready,
    Writes.load_frame mode state.memory slot top _ separate]
  exact ready.topValue

theorem call_write_address (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp) :
    Writes.address mode (target.form mode) (reset mode state firstDisp secondDisp) = slot := by
  cases target <;> exact stack_slot mode state top slot firstDisp secondDisp ready

theorem three_writes_owned (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp)
    (owned : Word mode -> Prop) (topOwned : owned top) (slotOwned : owned slot) :
    And (owned (Writes.address mode (.memory .exchangeStack firstDisp) state))
      (And (owned (Writes.address mode (.memory .storeStack secondDisp) (exchanged mode state firstDisp)))
        (owned (Writes.address mode (target.form mode) (reset mode state firstDisp secondDisp)))) := by
  constructor
  · change owned (memoryAddress mode (nextPC mode (.memory .exchangeStack firstDisp) state) firstDisp)
    rw [ready.reset.firstHits]
    exact topOwned
  · constructor
    · change owned (memoryAddress mode (nextPC mode (.memory .storeStack secondDisp) (exchanged mode state firstDisp)) secondDisp)
      rw [ready.reset.secondHits]
      exact topOwned
    · rw [call_write_address mode state top slot firstDisp secondDisp target ready]
      exact slotOwned

@[expose] def program (mode : Mode) (firstDisp secondDisp : BitVec 32) (target : Target) : List (Form mode) :=
  [.memory .exchangeStack firstDisp, .memory .storeStack secondDisp, target.form mode]

theorem owned_run (mode : Mode) (state : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp)
    (owned : Word mode -> Prop) (topOwned : owned top) (slotOwned : owned slot) :
    Writes.OwnedRun mode owned (program mode firstDisp secondDisp target) state := by
  have fields := three_writes_owned mode state top slot firstDisp secondDisp target ready owned topOwned slotOwned
  simpa only [program, Writes.OwnedRun, and_true, exchanged, reset] using fields

theorem trace_of_fetches (mode : Mode) (state : State mode) (firstDisp secondDisp : BitVec 32) (target : Target)
    (firstFetched : Fetch.fetch mode state.memory state.pc.toNat = some (.memory .exchangeStack firstDisp))
    (secondFetched : Fetch.fetch mode (exchanged mode state firstDisp).memory
      (exchanged mode state firstDisp).pc.toNat = some (.memory .storeStack secondDisp))
    (callFetched : Fetch.fetch mode (reset mode state firstDisp secondDisp).memory
      (reset mode state firstDisp secondDisp).pc.toNat = some (target.form mode)) :
    Fetch.Trace mode state (program mode firstDisp secondDisp target) (called mode state firstDisp secondDisp target) :=
  .step firstFetched (.step secondFetched (.step callFetched (.nil _)))

/-- The reset/CALL effect holds for actual opcode-derived packet traces. -/
theorem trace_result (mode : Mode) (state result : State mode) (top slot : Word mode)
    (firstDisp secondDisp : BitVec 32) (target : Target) (ready : StackReady mode state top slot firstDisp secondDisp)
    (trace : Fetch.Trace mode state (program mode firstDisp secondDisp target) result) :
    And (result.memory = ByteMemory.putWord mode state.memory slot.toNat
      (nextPC mode (target.form mode) (reset mode state firstDisp secondDisp)))
      (And (result.stack = slot) (And (result.accumulator = state.accumulator) (result.carry = state.carry))) := by
  have effect := Fetch.trace_run_eq mode trace
  change result = called mode state firstDisp secondDisp target at effect
  rw [effect]
  exact And.intro (called_memory mode state top slot firstDisp secondDisp target ready)
    (And.intro (called_stack mode state top slot firstDisp secondDisp target ready)
      (And.intro (called_accumulator mode state firstDisp secondDisp target)
        (called_carry mode state firstDisp secondDisp target)))

theorem reset_length (mode : Mode) (firstDisp secondDisp : BitVec 32) :
    instructionLength mode (.memory .exchangeStack firstDisp) + instructionLength mode (.memory .storeStack secondDisp) =
      (match mode with | .x86 => 12 | .x64 => 14) := by cases mode <;> rfl

theorem program_length (mode : Mode) (firstDisp secondDisp : BitVec 32) (target : Target) :
    instructionLength mode (.memory .exchangeStack firstDisp) + instructionLength mode (.memory .storeStack secondDisp) +
      instructionLength mode (target.form mode) =
        (match mode, target with | .x86, .relative _ => 17 | .x86, .indirect _ => 18 | .x64, .relative _ => 19 | .x64, .indirect _ => 20) := by cases mode <;> cases target <;> rfl

end SmcTuring.Native.Calls
