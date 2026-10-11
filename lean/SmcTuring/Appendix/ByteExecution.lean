module
public import SmcTuring.Appendix.ByteCode

public section

namespace SmcTuring.Appendix.ByteExecution

open ByteCode

abbrev State := Native.Execution.State .x86

/-- Selected nonfaulting flat-segment x86 projection: PC/EAX/ESP/CF and unified
byte memory. Other architectural state and physical fetch remain external. -/
@[expose] def nextPC (form : Form) (state : State) : Word :=
  BitVec.add state.pc (BitVec.ofNat 32 (instructionLength form))

@[expose] def prior (state : State) (address : Word) : Word :=
  Native.Execution.load .x86 state.memory address

@[expose] def executeImmediate (op : ImmediateOp) (address value : Word)
    (state : State) (next : Word) : State :=
  match op with
  | .store => Native.Execution.storeState .x86 state next address value state.carry
  | .bitXor => Native.Execution.storeState .x86 state next address (prior state address ^^^ value) false
  | .bitAnd => Native.Execution.storeState .x86 state next address (prior state address &&& value) false

@[expose] def executeMemory (op : MemoryOp) (address : Word) (state : State) (next : Word) : State :=
  match op with
  | .exchangeAcc => Native.Execution.executeMemory .x86 .exchangeAcc state next address
  | .exchangeStack => Native.Execution.executeMemory .x86 .exchangeStack state next address
  | .subtractAcc => Native.Execution.executeMemory .x86 .subtract state next address
  | .addAcc => Native.Execution.executeMemory .x86 .add state next address
  | .sbbZero => Native.Execution.executeMemory .x86 .subtractBorrowZero state next address
  | .negate => Native.Execution.storeState .x86 state next address (-prior state address)
      (decide (prior state address ≠ 0))
  | .complement => Native.Execution.storeState .x86 state next address (~~~prior state address) state.carry
  | .addFour => Native.Execution.storeState .x86 state next address (BitVec.add (prior state address) 4)
      ((prior state address).uaddOverflow 4)

@[expose] def execute (form : Form) (state : State) : State :=
  let next := nextPC form state
  match form with
  | .immediate op address value => executeImmediate op address value state next
  | .memory op address => executeMemory op address state next
  | .storeAcc address => Native.Execution.storeState .x86 state next address state.accumulator state.carry
  | .callRelative displacement => Native.Execution.callState .x86 state next (next + displacement)

/-- CALL writes the decremented ESP slot, not its transfer target. -/
@[expose] def destination (form : Form) (state : State) : Word :=
  match form with
  | .immediate _ address _ | .memory _ address | .storeAcc address => address
  | .callRelative _ => BitVec.sub state.stack 4

@[expose] def value (form : Form) (state : State) : Word :=
  match form with
  | .immediate .store _ value => value
  | .immediate .bitXor address value => prior state address ^^^ value
  | .immediate .bitAnd address value => prior state address &&& value
  | .memory .exchangeAcc _ | .storeAcc _ => state.accumulator
  | .memory .exchangeStack _ => state.stack
  | .memory .subtractAcc address => BitVec.sub (prior state address) state.accumulator
  | .memory .addAcc address => BitVec.add (prior state address) state.accumulator
  | .memory .negate address => -prior state address
  | .memory .complement address => ~~~prior state address
  | .memory .sbbZero address => BitVec.sub (prior state address) (if state.carry then 1 else 0)
  | .memory .addFour address => BitVec.add (prior state address) 4
  | .callRelative _ => nextPC form state

@[expose] def carry (form : Form) (state : State) : Bool :=
  match form with
  | .immediate .bitXor _ _ | .immediate .bitAnd _ _ => false
  | .memory .subtractAcc address => decide ((prior state address).toNat < state.accumulator.toNat)
  | .memory .addAcc address => (prior state address).uaddOverflow state.accumulator
  | .memory .negate address => decide (prior state address ≠ 0)
  | .memory .sbbZero address => decide ((prior state address).toNat < (if state.carry then 1 else 0 : Nat))
  | .memory .addFour address => (prior state address).uaddOverflow 4
  | _ => state.carry

@[expose] def accumulator (form : Form) (state : State) : Word :=
  match form with
  | .memory .exchangeAcc address => prior state address
  | _ => state.accumulator

@[expose] def stack (form : Form) (state : State) : Word :=
  match form with
  | .memory .exchangeStack address => prior state address
  | .callRelative _ => BitVec.sub state.stack 4
  | _ => state.stack

@[expose] def pc (form : Form) (state : State) : Word :=
  match form with
  | .callRelative displacement => nextPC form state + displacement
  | _ => nextPC form state

/-- Complete observed effect, for every operand bit pattern and incoming state.
Each form includes exactly one full DWORD store, even if its value is unchanged. -/
theorem execute_effect (form : Form) (state : State) :
    execute form state =
      { pc := pc form state
        accumulator := accumulator form state
        stack := stack form state
        carry := carry form state
        memory := Native.ByteMemory.putWord .x86 state.memory
          (destination form state).toNat (value form state) } := by
  cases form with
  | immediate op address value => cases op <;> rfl
  | memory op address => cases op <;> rfl
  | storeAcc => rfl
  | callRelative => rfl

theorem execute_memory (form : Form) (state : State) :
    (execute form state).memory = Native.ByteMemory.putWord .x86 state.memory
      (destination form state).toNat (value form state) := by rw [execute_effect]

theorem execute_accumulator (form : Form) (state : State) :
    (execute form state).accumulator = accumulator form state := by rw [execute_effect]

theorem execute_stack (form : Form) (state : State) :
    (execute form state).stack = stack form state := by rw [execute_effect]

theorem execute_carry (form : Form) (state : State) :
    (execute form state).carry = carry form state := by rw [execute_effect]

theorem execute_pc (form : Form) (state : State) :
    (execute form state).pc = pc form state := by rw [execute_effect]

theorem written_word (form : Form) (state : State) :
    Native.Execution.load .x86 (execute form state).memory (destination form state) = value form state := by
  rw [execute_memory]
  exact Native.Execution.load_put_word .x86 state.memory _ _

theorem execute_frame (form : Form) (state : State) (position : Nat)
    (outside : ¬Native.ByteMemory.Inside (destination form state).toNat 4 position) :
    (execute form state).memory position = state.memory position := by
  rw [execute_memory]
  exact Native.ByteMemory.put_frame _ _ _ _ (by simpa only [Native.LittleEndian.word_encode_length, Native.Mode.wordBytes] using outside)

theorem load_frame (form : Form) (state : State) (observed : Word)
    (separate : ∀ index : Fin 4,
      ¬Native.ByteMemory.Inside (destination form state).toNat 4 (observed.toNat + index.val)) :
    Native.Execution.load .x86 (execute form state).memory observed = prior state observed := by
  rw [execute_memory]
  exact Native.Writes.load_frame .x86 state.memory _ observed _ separate

/-- Four actual destination bytes; purity does not require a changed value. -/
@[expose] def footprint (form : Form) (state : State) : List Nat :=
  (List.range 4).map (fun index => (destination form state).toNat + index)

theorem footprint_length (form : Form) (state : State) : (footprint form state).length = 4 := by
  simp [footprint]

theorem footprint_nonempty (form : Form) (state : State) : footprint form state ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  rw [footprint_length] at length
  cases length

theorem store_preserves_carry (address value : Word) (state : State) :
    (execute (.immediate .store address value) state).carry = state.carry := rfl

theorem xor_clears_carry (address value : Word) (state : State) :
    (execute (.immediate .bitXor address value) state).carry = false := rfl

theorem and_clears_carry (address value : Word) (state : State) :
    (execute (.immediate .bitAnd address value) state).carry = false := rfl

theorem neg_carry (address : Word) (state : State) :
    (execute (.memory .negate address) state).carry = decide (prior state address ≠ 0) := rfl

theorem not_preserves_carry (address : Word) (state : State) :
    (execute (.memory .complement address) state).carry = state.carry := rfl

theorem sbb_value (address : Word) (state : State) :
    Native.Execution.load .x86 (execute (.memory .sbbZero address) state).memory address =
      BitVec.sub (prior state address) (if state.carry then 1 else 0) := written_word _ _

theorem add_four_carry (address : Word) (state : State) :
    (execute (.memory .addFour address) state).carry = (prior state address).uaddOverflow 4 := rfl

theorem call_target (displacement : Word) (state : State) :
    (execute (.callRelative displacement) state).pc = nextPC (.callRelative displacement) state + displacement := rfl

theorem call_return (displacement : Word) (state : State) :
    Native.Execution.load .x86 (execute (.callRelative displacement) state).memory (BitVec.sub state.stack 4) =
      nextPC (.callRelative displacement) state := written_word _ _

/-- Shared forms reuse the previously checked native primitive effects exactly. -/
@[expose] def commonForm : Form → Option (Native.Form .x86)
  | .memory .exchangeAcc address => some (.memory .exchangeAcc address)
  | .memory .exchangeStack address => some (.memory .exchangeStack address)
  | .memory .subtractAcc address => some (.memory .subtract address)
  | .memory .addAcc address => some (.memory .add address)
  | .memory .sbbZero address => some (.memory .subtractBorrowZero address)
  | .storeAcc address => some (.moffs address)
  | .callRelative displacement => some (.callRelative displacement)
  | _ => none

theorem common_encoding (form : Form) (native : Native.Form .x86)
    (correspondence : commonForm form = some native) : encode form = Native.encode .x86 native := by
  cases form with
  | immediate op address value => cases op <;> cases correspondence
  | memory op address => cases op <;> cases correspondence <;> rfl
  | storeAcc => cases correspondence; rfl
  | callRelative => cases correspondence; rfl

theorem common_execution (form : Form) (native : Native.Form .x86) (state : State)
    (correspondence : commonForm form = some native) :
    execute form state = Native.Execution.execute .x86 native state := by
  cases form with
  | immediate op address value => cases op <;> cases correspondence
  | memory op address => cases op <;> cases correspondence <;> rfl
  | storeAcc => cases correspondence; rfl
  | callRelative => cases correspondence; rfl

/-- Execute only a form decoded from the actual current memory/header. -/
@[expose] def step (state : State) : Option State :=
  (fetch state.memory state.pc.toNat).map (fun form => execute form state)

theorem step_current_encoding (state : State) (form : Form)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat (encode form).length = encode form) :
    step state = some (execute form state) := by
  simp only [step, fetch_current_encoding state.memory state.pc.toNat form current, Option.map_some]

theorem fetched_write (state : State) (form : Form)
    (fetched : fetch state.memory state.pc.toNat = some form) :
    (step state).map Native.Execution.State.memory =
      some (Native.ByteMemory.putWord .x86 state.memory (destination form state).toNat (value form state)) := by
  simp only [step, fetched, Option.map_some, execute_memory]

theorem step_patched_immediate (state : State) (op : ImmediateOp) (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat
      (encode (.immediate op address old)).length = encode (.immediate op address old)) :
    let patched : State := { state with memory := Native.ByteMemory.putWord .x86 state.memory (state.pc.toNat + 6) fresh }
    step patched = some (execute (.immediate op address fresh) patched) := by
  simp only [step, fetch_patched_current_immediate state.memory state.pc.toNat op address old fresh current,
    Option.map_some]

theorem step_patched_call (state : State) (old fresh : Word)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat
      (encode (.callRelative old)).length = encode (.callRelative old)) :
    let patched : State := { state with memory := Native.ByteMemory.putWord .x86 state.memory (state.pc.toNat + 1) fresh }
    step patched = some (execute (.callRelative fresh) patched) := by
  simp only [step, fetch_patched_current_call state.memory state.pc.toNat old fresh current, Option.map_some]

theorem step_patched_address (state : State) (op : ImmediateOp) (old fresh value : Word)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat
      (encode (.immediate op old value)).length = encode (.immediate op old value)) :
    let patched : State := { state with memory := Native.ByteMemory.putWord .x86 state.memory (state.pc.toNat + 2) fresh }
    step patched = some (execute (.immediate op fresh value) patched) := by
  simp only [step, fetch_patched_current_address state.memory state.pc.toNat op old fresh value current,
    Option.map_some]

@[expose] def run : List Form → State → State
  | [], state => state
  | form :: rest, state => run rest (execute form state)

/-- Every event's operands come from its own current byte image. -/
inductive Trace : State → List Form → State → Prop where
  | nil (state : State) : Trace state [] state
  | step {state finish : State} {form : Form} {rest : List Form}
      (fetched : fetch state.memory state.pc.toNat = some form)
      (tail : Trace (execute form state) rest finish) : Trace state (form :: rest) finish

theorem trace_run {state finish : State} {forms : List Form} (trace : Trace state forms finish) :
    finish = run forms state := by
  induction trace with
  | nil => rfl
  | step fetched tail ih => exact ih

theorem run_append (first second : List Form) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons form rest ih => simpa [run] using ih (execute form state)

theorem trace_append {state middle finish : State} {first second : List Form}
    (leading : Trace state first middle) (trailing : Trace middle second finish) :
    Trace state (first ++ second) finish := by
  induction leading with
  | nil => exact trailing
  | step fetched tail ih => exact .step fetched (ih trailing)

theorem trace_head_step {state finish : State} {form : Form} {rest : List Form}
    (trace : Trace state (form :: rest) finish) : step state = some (execute form state) := by
  cases trace with
  | step fetched tail => simp only [step, fetched, Option.map_some]

@[expose] def OwnedRun (owned : Word → Prop) : List Form → State → Prop
  | [], _ => True
  | form :: rest, state => owned (destination form state) ∧ OwnedRun owned rest (execute form state)

theorem owned_append (owned : Word → Prop) (first second : List Form) (state : State) :
    OwnedRun owned (first ++ second) state ↔ OwnedRun owned first state ∧ OwnedRun owned second (run first state) := by
  induction first generalizing state with
  | nil => simp [OwnedRun, run]
  | cons form rest ih => simp [OwnedRun, run, ih, and_assoc]

end SmcTuring.Appendix.ByteExecution
