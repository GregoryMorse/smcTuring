module
public import SmcTuring.Native.StringForm

public section
namespace SmcTuring.Native.StringExecution
open StringForm

/-- Selected flat-segment, nonfaulting state. SI/DI and DF are represented in
addition to the existing PC/AX/SP/CF byte-memory projection. Physical mapping,
segment/CET conditions and instruction-cache coherence remain realization
conditions. DF=0 is a proved-use precondition, not a state-update shortcut. -/
structure State (mode : Mode) where
  principal : Execution.State mode
  sourceIndex : Word mode
  destinationIndex : Word mode
  backwards : Bool

@[expose] def nextPC (mode : Mode) (form : StringForm.Form mode) (state : State mode) : Word mode :=
  state.principal.pc + Arithmetic.encodeNat mode (length mode form)
@[expose] def address (mode : Mode) (form : StringForm.Form mode) (state : State mode) (displacement : BitVec 32) : Word mode :=
  Execution.memoryAddress mode (nextPC mode form state) displacement

@[expose] def execute (mode : Mode) (form : StringForm.Form mode) (state : State mode) : State mode :=
  let next := nextPC mode form state
  match form with
  | .native native => { state with principal := Execution.execute mode native state.principal }
  | .initialize32 target value =>
    { state with principal := { state.principal with
        pc := next
        memory := ByteMemory.putBytes state.principal.memory target.toNat (LittleEndian.wordEncode 4 value) } }
  | .exchangeIndex destination displacement =>
    let target := address mode form state displacement
    let loaded := Execution.load mode state.principal.memory target
    if destination then
      { state with
        principal := { state.principal with
          pc := next
          memory := ByteMemory.putWord mode state.principal.memory target.toNat state.destinationIndex }
        destinationIndex := loaded }
    else
      { state with
        principal := { state.principal with
          pc := next
          memory := ByteMemory.putWord mode state.principal.memory target.toNat state.sourceIndex }
        sourceIndex := loaded }
  | .subtractSmall displacement value =>
    let target := address mode form state displacement
    let loaded := Execution.load mode state.principal.memory target
    let immediate : Word mode := value.signExtend (8*mode.wordBytes)
    { state with principal := Execution.storeState mode state.principal next target (loaded-immediate) (Arithmetic.unsignedBorrow loaded immediate) }
  | .subtractFull displacement value =>
    let target := address mode form state displacement
    let loaded := Execution.load mode state.principal.memory target
    let immediate := Execution.displacementWord mode value
    { state with principal := Execution.storeState mode state.principal next target (loaded-immediate) (Arithmetic.unsignedBorrow loaded immediate) }
  | .move width =>
    let increment := Arithmetic.encodeNat mode width
    { state with
      principal := { state.principal with
        pc := next
        memory := ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat width) }
      sourceIndex := if state.backwards then state.sourceIndex-increment else state.sourceIndex+increment
      destinationIndex := if state.backwards then state.destinationIndex-increment else state.destinationIndex+increment }

@[expose] def run (mode : Mode) : List (StringForm.Form mode) -> State mode -> State mode
  | [], state => state
  | form :: rest, state => run mode rest (execute mode form state)
@[expose] def step (mode : Mode) (state : State mode) : Option (State mode) :=
  (StringForm.fetch mode state.principal.memory state.principal.pc.toNat).map (fun form => execute mode form state)

inductive Trace (mode : Mode) : State mode -> List (StringForm.Form mode) -> State mode -> Prop where
  | nil (state : State mode) : Trace mode state [] state
  | step {state finish : State mode} {form : StringForm.Form mode} {rest : List (StringForm.Form mode)}
      (fetched : StringForm.fetch mode state.principal.memory state.principal.pc.toNat = some form)
      (tail : Trace mode (execute mode form state) rest finish) : Trace mode state (form :: rest) finish

theorem native_effect (mode : Mode) (form : Native.Form mode) (state : State mode) :
    (execute mode (.native form) state).principal = Execution.execute mode form state.principal := rfl

theorem native_indices (mode : Mode) (form : Native.Form mode) (state : State mode) :
    (execute mode (.native form) state).sourceIndex = state.sourceIndex ∧
    (execute mode (.native form) state).destinationIndex = state.destinationIndex := ⟨rfl,rfl⟩

theorem direction_preserved (mode : Mode) (form : StringForm.Form mode) (state : State mode) :
    (execute mode form state).backwards = state.backwards := by
  cases form <;> simp [execute]
  split <;> rfl

theorem run_direction (mode : Mode) (forms : List (StringForm.Form mode)) (state : State mode) :
    (run mode forms state).backwards = state.backwards := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih => exact (ih (execute mode form state)).trans (direction_preserved mode form state)

/-- Literal forward MOVS, including its current byte load and full element
store. Only SI/DI, PC and the destination bytes change in the selected state. -/
theorem move_effect (mode : Mode) (width : Nat) (state : State mode) (forward : state.backwards = false) :
    execute mode (.move width) state = { state with
      principal := { state.principal with
        pc := nextPC mode (.move width) state
        memory := ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat width) }
      sourceIndex := state.sourceIndex+Arithmetic.encodeNat mode width
      destinationIndex := state.destinationIndex+Arithmetic.encodeNat mode width } := by
  simp only [execute,forward,Bool.false_eq_true,ite_false]

theorem move_frame (mode : Mode) (width : Nat) (state : State mode) (position : Nat)
    (outside : ¬ByteMemory.Inside state.destinationIndex.toNat width position) :
    (execute mode (.move width) state).principal.memory position = state.principal.memory position := by
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

theorem move_accumulator (mode : Mode) (width : Nat) (state : State mode) :
    (execute mode (.move width) state).principal.accumulator = state.principal.accumulator := rfl

theorem move_stack (mode : Mode) (width : Nat) (state : State mode) :
    (execute mode (.move width) state).principal.stack = state.principal.stack := rfl

theorem move_carry (mode : Mode) (width : Nat) (state : State mode) :
    (execute mode (.move width) state).principal.carry = state.principal.carry := rfl

theorem exchange_source (mode : Mode) (state : State mode) (displacement : BitVec 32) (target : Word mode)
    (hits : address mode (.exchangeIndex false displacement) state displacement = target) :
    execute mode (.exchangeIndex false displacement) state = { state with
      principal := { state.principal with
        pc := nextPC mode (.exchangeIndex false displacement) state
        memory := ByteMemory.putWord mode state.principal.memory target.toNat state.sourceIndex }
      sourceIndex := Execution.load mode state.principal.memory target } := by
  simp only [execute,Bool.false_eq_true,ite_false,hits]

theorem exchange_destination (mode : Mode) (state : State mode) (displacement : BitVec 32) (target : Word mode)
    (hits : address mode (.exchangeIndex true displacement) state displacement = target) :
    execute mode (.exchangeIndex true displacement) state = { state with
      principal := { state.principal with
        pc := nextPC mode (.exchangeIndex true displacement) state
        memory := ByteMemory.putWord mode state.principal.memory target.toNat state.destinationIndex }
      destinationIndex := Execution.load mode state.principal.memory target } := by
  simp [execute,hits]

theorem trace_run (mode : Mode) {state finish : State mode} {forms : List (StringForm.Form mode)} (trace : Trace mode state forms finish) : finish = run mode forms state := by
  induction trace with
  | nil => rfl
  | step _ _ ih => exact ih

theorem run_append (mode : Mode) (first second : List (StringForm.Form mode)) (state : State mode) :
    run mode (first++second) state = run mode second (run mode first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons form rest ih => exact ih (execute mode form state)

theorem trace_append (mode : Mode) {state middle finish : State mode} {first second : List (StringForm.Form mode)}
    (leading : Trace mode state first middle) (trailing : Trace mode middle second finish) : Trace mode state (first++second) finish := by
  induction leading with
  | nil => exact trailing
  | step fetched _ ih => exact .step fetched (ih trailing)

theorem step_current_encoding (mode : Mode) (form : StringForm.Form mode) (legal : Legal mode form) (state : State mode)
    (current : ByteMemory.bytesAt state.principal.memory state.principal.pc.toNat (StringForm.encode mode form).length = StringForm.encode mode form) :
    step mode state = some (execute mode form state) := by
  simp only [step,StringForm.fetch_current_encoding mode _ _ form legal current,Option.map_some]

end SmcTuring.Native.StringExecution
