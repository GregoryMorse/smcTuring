module
public import SmcTuring.Appendix.DivisionWords
public import SmcTuring.Appendix.MultiplyControl

public section
namespace SmcTuring.Appendix.DivisionControl
abbrev Word := Machine32.Word
abbrev State := BranchTail.State
abbrev StackReady := MultiplyControl.StackReady

/-- Literal full-width data lengths, with static imm8 ADC 0 and SHR 31.
Actual current-byte codecs are the later refinement of these selected forms. -/
@[expose] def dataLength : DivisionWords.Instruction → Nat
  | .simple instruction => MultiplyControl.dataLength instruction
  | .subtractFrom _ _ | .subtractConstant _ _ | .addConstant _ _ => 10
  | .right31 _ | .adcZero _ => 7
  | .decrement _ => 6

inductive Instruction where
  | data (instruction : DivisionWords.Instruction)
  | control (instruction : MultiplyControl.Instruction)
  deriving DecidableEq, Repr

@[expose] def destination (instruction : Instruction) (state : State) : Nat :=
  match instruction with
  | .data instruction => DivisionWords.destination instruction
  | .control instruction => MultiplyControl.destination instruction state

@[expose] def execute (instruction : Instruction) (state : State) : State :=
  match instruction with
  | .data instruction => {state with
      data := DivisionWords.execute instruction state.data
      pc := state.pc + BitVec.ofNat 32 (dataLength instruction)}
  | .control instruction => MultiplyControl.execute instruction state

@[expose] def run : List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)

@[expose] def PureRun (codeField : Nat → Prop) : List Instruction → State → Prop
  | [], _ => True
  | instruction :: rest, state =>
      codeField (destination instruction state) ∧ PureRun codeField rest (execute instruction state)

@[expose] def lift (program : List DivisionWords.Instruction) : List Instruction := program.map .data
@[expose] def embed (program : List MultiplyControl.Instruction) : List Instruction := program.map .control
@[expose] def span (program : List DivisionWords.Instruction) : Nat := (program.map dataLength).sum
@[expose] def roundTrip (pointer address displacement : Nat) : List Instruction :=
  embed (MultiplyControl.roundTrip pointer address displacement)

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem pure_append (codeField : Nat → Prop) (first second : List Instruction) (state : State) :
    PureRun codeField (first ++ second) state ↔
      PureRun codeField first state ∧ PureRun codeField second (run first state) := by
  induction first generalizing state with
  | nil => simp [PureRun, run]
  | cons instruction rest ih => simp [PureRun, run, ih, and_assoc]

theorem lift_effect (program : List DivisionWords.Instruction) (state : State) :
    run (lift program) state =
      { state with
        data := DivisionWords.run program state.data
        pc := state.pc + BitVec.ofNat 32 (span program)} := by
  induction program generalizing state with
  | nil => simp [lift, run, span, DivisionWords.run]
  | cons instruction rest ih =>
      change run (lift rest) (execute (.data instruction) state) =
        { state with
          data := DivisionWords.run rest (DivisionWords.execute instruction state.data)
          pc := state.pc + BitVec.ofNat 32 (dataLength instruction + span rest)}
      rw [ih]
      simp only [execute, BitVec.ofNat_add, BitVec.add_assoc]

theorem lift_pure (program : List DivisionWords.Instruction) (state : State) (codeField : Nat → Prop)
    (pure : DivisionWords.PureRun codeField program state.data) :
    PureRun codeField (lift program) state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih => exact ⟨pure.1, ih _ pure.2⟩

theorem embed_run (program : List MultiplyControl.Instruction) (state : State) :
    run (embed program) state = MultiplyControl.run program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [embed, run, execute, MultiplyControl.run] using ih (MultiplyControl.execute instruction state)

theorem embed_pure (program : List MultiplyControl.Instruction) (state : State) (codeField : Nat → Prop)
    (pure : MultiplyControl.PureRun codeField program state) :
    PureRun codeField (embed program) state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih => exact ⟨pure.1, ih _ pure.2⟩

theorem round_trip_effect (pointer address displacement : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (ready : StackReady pointer address state) :
    run (roundTrip pointer address displacement) state =
      {data := MultiplyControl.clearCarry state.data, stack := state.stack,
        pc := BranchTail.next state + state.data.memory displacement + 30} := by
  rw [roundTrip, embed_run]
  exact MultiplyControl.round_trip_effect _ _ _ _ callSeparate addressSeparate ready

theorem round_trip_ready (pointer address displacement : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (ready : StackReady pointer address state) :
    StackReady pointer address (run (roundTrip pointer address displacement) state) := by
  rw [roundTrip, embed_run]
  exact MultiplyControl.round_trip_ready _ _ _ _ callSeparate addressSeparate ready

theorem round_trip_pure (pointer address displacement : Nat) (state : State)
    (ready : StackReady pointer address state) (codeField : Nat → Prop)
    (pointerOwned : codeField pointer) (addressOwned : codeField address) :
    PureRun codeField (roundTrip pointer address displacement) state := by
  rw [roundTrip]
  exact embed_pure _ _ _ (MultiplyControl.round_trip_pure _ _ _ _ ready codeField pointerOwned addressOwned)

theorem ready_lift (program : List DivisionWords.Instruction) (state : State) (pointer address : Nat)
    (ready : StackReady pointer address state)
    (pointerFrame : (DivisionWords.run program state.data).memory pointer = state.data.memory pointer)
    (addressFrame : (DivisionWords.run program state.data).memory address = state.data.memory address) :
    StackReady pointer address (run (lift program) state) := by
  rw [lift_effect]
  constructor
  · simpa only [BranchTail.slot, pointerFrame] using ready.slot
  · simpa only [pointerFrame, addressFrame] using ready.same
  · simpa only [pointerFrame] using ready.nonwrap

theorem initial_ready (pointer address : Nat) (state : State)
    (coordinate : pointer = address + 4) (capacity : pointer < 4294967296)
    (pointerValue : state.data.memory pointer = BitVec.ofNat 32 pointer)
    (addressValue : state.data.memory address = BitVec.ofNat 32 pointer) :
    StackReady pointer address state := by
  constructor
  · simp only [BranchTail.slot, pointerValue, BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt capacity]
    norm_num
    omega
  · rw [pointerValue, addressValue]
  · rw [pointerValue]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacity]
    omega

theorem lift_length (program : List DivisionWords.Instruction) : (lift program).length = program.length := by
  simp [lift]

theorem round_trip_length (pointer address displacement : Nat) :
    (roundTrip pointer address displacement).length = 7 := rfl

end SmcTuring.Appendix.DivisionControl
