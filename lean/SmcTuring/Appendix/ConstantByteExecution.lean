module
public import SmcTuring.Appendix.ConstantByteCode
public import SmcTuring.Appendix.MultiplyByteExecution

public section
namespace SmcTuring.Appendix.ConstantByteExecution

open ConstantByteCode
abbrev State := MultiplyByteExecution.State
abbrev prior := ByteExecution.prior

@[expose] def nextPC (form : Form) (state : State) : Word :=
  BitVec.add state.pc (BitVec.ofNat 32 (instructionLength form))

/-- Selected nonfaulting flat x86 projection, with actual SHL counts 1..31.
    PC/EAX/ESP/CF and unified byte memory are represented; full CPU/fetch is E05. -/
@[expose] def execute (form : Form) (state : State) : State :=
  match form with
  | .common form => MultiplyByteExecution.execute form state
  | .shiftImmediate address count => Native.Execution.storeState .x86 state (nextPC form state)
      address (prior state address <<< (count.val + 1))
      ((prior state address).getLsbD (32 - (count.val + 1)))

@[expose] def destination (form : Form) (state : State) : Word :=
  match form with
  | .common form => MultiplyByteExecution.destination form state
  | .shiftImmediate address _ => address

@[expose] def value (form : Form) (state : State) : Word :=
  match form with
  | .common form => MultiplyByteExecution.value form state
  | .shiftImmediate address count => prior state address <<< (count.val + 1)

@[expose] def carry (form : Form) (state : State) : Bool :=
  match form with
  | .common form => MultiplyByteExecution.carry form state
  | .shiftImmediate address count => (prior state address).getLsbD (32 - (count.val + 1))

@[expose] def accumulator (form : Form) (state : State) : Word :=
  match form with
  | .common form => MultiplyByteExecution.accumulator form state
  | .shiftImmediate _ _ => state.accumulator

@[expose] def stack (form : Form) (state : State) : Word :=
  match form with
  | .common form => MultiplyByteExecution.stack form state
  | .shiftImmediate _ _ => state.stack

@[expose] def pc (form : Form) (state : State) : Word :=
  match form with
  | .common form => MultiplyByteExecution.pc form state
  | .shiftImmediate _ _ => nextPC form state

/-- Exact full DWORD store and observed effects for every operand/state. -/
theorem execute_effect (form : Form) (state : State) :
    execute form state =
      { pc := pc form state
        accumulator := accumulator form state
        stack := stack form state
        carry := carry form state
        memory := Native.ByteMemory.putWord .x86 state.memory
          (destination form state).toNat (value form state) } := by
  cases form with
  | common form => exact MultiplyByteExecution.execute_effect form state
  | shiftImmediate => rfl

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
  exact Native.ByteMemory.put_frame _ _ _ _
    (by simpa only [Native.LittleEndian.word_encode_length, Native.Mode.wordBytes] using outside)

theorem load_frame (form : Form) (state : State) (observed : Word)
    (separate : ∀ index : Fin 4,
      ¬Native.ByteMemory.Inside (destination form state).toNat 4 (observed.toNat + index.val)) :
    Native.Execution.load .x86 (execute form state).memory observed = prior state observed := by
  rw [execute_memory]
  exact Native.Writes.load_frame .x86 state.memory _ observed _ separate

@[expose] def footprint (form : Form) (state : State) : List Nat :=
  (List.range 4).map (fun index => (destination form state).toNat + index)

theorem footprint_length (form : Form) (state : State) : (footprint form state).length = 4 := by
  simp [footprint]

theorem footprint_nonempty (form : Form) (state : State) : footprint form state ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  rw [footprint_length] at length
  cases length

theorem common_execution (form : MultiplyByteCode.Form) (state : State) :
    execute (.common form) state = MultiplyByteExecution.execute form state := rfl


theorem shift_carry (address : Word) (count : Count) (state : State) :
    (execute (.shiftImmediate address count) state).carry =
      (prior state address).getLsbD (32 - (count.val + 1)) := rfl

@[expose] def step (state : State) : Option State :=
  (fetch state.memory state.pc.toNat).map (fun form => execute form state)

theorem step_current_encoding (state : State) (form : Form)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat (encode form).length = encode form) :
    step state = some (execute form state) := by
  simp only [step, fetch_current_encoding state.memory state.pc.toNat form current, Option.map_some]

theorem step_patched_add (state : State) (address old fresh : Word)
    (current : Native.ByteMemory.bytesAt state.memory state.pc.toNat
      (encode (.common (.addImmediate address old))).length = encode (.common (.addImmediate address old))) :
    let patched : State := { state with memory := Native.ByteMemory.putWord .x86 state.memory (state.pc.toNat + 6) fresh }
    step patched = some (execute (.common (.addImmediate address fresh)) patched) := by
  simp only [step, fetch_patched_current_add state.memory state.pc.toNat address old fresh current,
    Option.map_some]

@[expose] def run : List Form → State → State
  | [], state => state
  | form :: rest, state => run rest (execute form state)

/-- Each event is decoded from its own actual current byte state. This relation
is infrastructure; constructing the entire image trace remains a layout task. -/
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

@[expose] def OwnedRun (owned : Word → Prop) : List Form → State → Prop
  | [], _ => True
  | form :: rest, state => owned (destination form state) ∧ OwnedRun owned rest (execute form state)

theorem owned_append (owned : Word → Prop) (first second : List Form) (state : State) :
    OwnedRun owned (first ++ second) state ↔ OwnedRun owned first state ∧ OwnedRun owned second (run first state) := by
  induction first generalizing state with
  | nil => simp [OwnedRun, run]
  | cons form rest ih => simp [OwnedRun, run, ih, and_assoc]

end SmcTuring.Appendix.ConstantByteExecution
