module
public import SmcTuring.Appendix.MultiplyLoop
public import SmcTuring.Appendix.BranchTail

public section
namespace SmcTuring.Appendix.MultiplyControl
abbrev Word := Machine32.Word
abbrev State := BranchTail.State

/-- Literal selected instruction lengths; current byte fetch is the next bridge. -/
@[expose] def dataLength : MultiplyWords.Instruction -> Nat
  | .selected (.exchange _) | .selected (.subtractAcc _) | .selected (.addAcc _)
  | .selected (.negate _) | .selected (.complement _) | .andAcc _ | .shiftLeft _ | .shiftRight _ => 6
  | .selected (.sbbZero _) => 7
  | .storeAcc _ => 5
  | _ => 10

inductive Instruction where
  | data (instruction : MultiplyWords.Instruction)
  | exchangeStack (pointer : Nat)
  | addFour (pointer : Nat)
  | callField (displacement : Nat)
  deriving DecidableEq, Repr

@[expose] def destination (instruction : Instruction) (state : State) : Nat :=
  match instruction with
  | .data instruction => MultiplyWords.destination instruction
  | .exchangeStack pointer | .addFour pointer => pointer
  | .callField _ => (state.stack - 4).toNat

@[expose] def execute (instruction : Instruction) (state : State) : State :=
  match instruction with
  | .data instruction =>
      { state with
        data := MultiplyWords.execute instruction state.data
        pc := state.pc + BitVec.ofNat 32 (dataLength instruction) }
  | .exchangeStack pointer => BranchTail.exchangeStack pointer state
  | .addFour pointer =>
      { state with
        data := Machine32.put state.data pointer (state.data.memory pointer + 4)
          ((state.data.memory pointer).uaddOverflow 4)
        pc := state.pc + 7 }
  | .callField displacement => BranchTail.call (state.data.memory displacement) state

@[expose] def run : List Instruction -> State -> State
  | [], state => state
  | instruction :: rest, state => run rest (execute instruction state)
@[expose] def PureRun (codeField : Nat -> Prop) : List Instruction -> State -> Prop
  | [], _ => True
  | instruction :: rest, state => codeField (destination instruction state) ∧ PureRun codeField rest (execute instruction state)
@[expose] def lift (program : List MultiplyWords.Instruction) : List Instruction := program.map .data
@[expose] def span (program : List MultiplyWords.Instruction) : Nat := (program.map dataLength).sum

@[expose] def tailProgram (pointer displacement : Nat) : List Instruction :=
  [.exchangeStack pointer, .callField displacement]
@[expose] def restoreProgram (pointer address : Nat) : List Instruction :=
  [.exchangeStack pointer, .addFour pointer, .data (.selected (.exchange pointer)),
   .data (.storeAcc address), .data (.selected (.exchange pointer))]
@[expose] def roundTrip (pointer address displacement : Nat) : List Instruction :=
  tailProgram pointer displacement ++ restoreProgram pointer address

structure StackReady (pointer address : Nat) (state : State) : Prop where
  slot : (BranchTail.slot pointer state).toNat = address
  same : state.data.memory address = state.data.memory pointer
  nonwrap : 4 ≤ (state.data.memory pointer).toNat

@[expose] def clearCarry (state : Machine32.State) : Machine32.State := { state with carry := false }

theorem run_append (first second : List Instruction) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [run] using ih (execute instruction state)

theorem pure_append (codeField : Nat -> Prop) (first second : List Instruction) (state : State) :
    PureRun codeField (first ++ second) state ↔ PureRun codeField first state ∧ PureRun codeField second (run first state) := by
  induction first generalizing state with
  | nil => simp [PureRun, run]
  | cons instruction rest ih => simp [PureRun, run, ih, and_assoc]

theorem lift_effect (program : List MultiplyWords.Instruction) (state : State) :
    run (lift program) state =
      { state with
        data := MultiplyWords.run program state.data
        pc := state.pc + BitVec.ofNat 32 (span program) } := by
  induction program generalizing state with
  | nil => simp [lift, run, span, MultiplyWords.run]
  | cons instruction rest ih =>
      change run (lift rest) (execute (.data instruction) state) =
        { state with
          data := MultiplyWords.run rest (MultiplyWords.execute instruction state.data)
          pc := state.pc + BitVec.ofNat 32 (dataLength instruction + span rest) }
      rw [ih]
      simp only [execute, BitVec.ofNat_add, BitVec.add_assoc]

theorem lift_pure (program : List MultiplyWords.Instruction) (state : State) (codeField : Nat -> Prop)
    (pure : MultiplyWords.PureRun codeField program state.data) : PureRun codeField (lift program) state := by
  induction program generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
      exact ⟨pure.1, ih _ pure.2⟩

theorem literal_lengths (fields : MultiplyWords.Fields) (delta : Word) (pointer address displacement : Nat) :
    span (MultiplyWords.initialProgram fields) = 44 ∧ span (MultiplyWords.guard fields delta) = 65 ∧
    span (MultiplyWords.body fields) = 130 ∧ span (MultiplyWords.finish fields) = 20 ∧
    (tailProgram pointer displacement).length = 2 ∧ (restoreProgram pointer address).length = 5 := by
  simp [span, dataLength, MultiplyWords.initialProgram, MultiplyWords.copyProgram,
    MultiplyWords.guard, MultiplyWords.body, MultiplyWords.finish, tailProgram, restoreProgram]

theorem tail_effect (pointer displacement : Nat) (state : State) :
    run (tailProgram pointer displacement) state = BranchTail.tail pointer displacement state := rfl

theorem restore_effect (pointer address : Nat) (state : State) :
    run (restoreProgram pointer address) state =
      { data := (BranchTail.restore pointer address state).data,
        stack := (BranchTail.restore pointer address state).stack, pc := state.pc + 30 } := by
  simp only [restoreProgram, run, execute, BranchTail.restore, BranchTail.exchangeStack,
    MultiplyWords.execute, Machine32.execute, Machine32.put, dataLength]
  congr 1
  simp only [BitVec.add_assoc]
  rfl

theorem round_trip_effect (pointer address displacement : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (ready : StackReady pointer address state) :
    run (roundTrip pointer address displacement) state =
      { data := clearCarry state.data, stack := state.stack,
        pc := BranchTail.next state + state.data.memory displacement + 30 } := by
  rw [roundTrip, run_append, tail_effect, restore_effect,
    BranchTail.continued_alias_no_carry pointer displacement address state callSeparate addressSeparate ready.slot ready.same ready.nonwrap,
    BranchTail.tail_pc pointer displacement state callSeparate]
  rfl

theorem round_trip_ready (pointer address displacement : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (ready : StackReady pointer address state) : StackReady pointer address (run (roundTrip pointer address displacement) state) := by
  rw [round_trip_effect pointer address displacement state callSeparate addressSeparate ready]
  exact ⟨ready.slot, ready.same, ready.nonwrap⟩

theorem round_trip_pure (pointer address displacement : Nat) (state : State)
    (ready : StackReady pointer address state) (codeField : Nat -> Prop)
    (pointerOwned : codeField pointer) (addressOwned : codeField address) :
    PureRun codeField (roundTrip pointer address displacement) state := by
  have slot : ((state.data.memory pointer) - 4).toNat = address := ready.slot
  change codeField pointer ∧ codeField (state.data.memory pointer - 4).toNat ∧
    codeField pointer ∧ codeField pointer ∧ codeField pointer ∧ codeField address ∧ codeField pointer ∧ True
  rw [slot]
  exact ⟨pointerOwned, addressOwned, pointerOwned, pointerOwned, pointerOwned, addressOwned, pointerOwned, True.intro⟩

theorem guard_ignore_carry (fields : MultiplyWords.Fields) (delta : Word) (state : Machine32.State) (carry : Bool) :
    MultiplyWords.run (MultiplyWords.guard fields delta) { state with carry := carry } =
      MultiplyWords.run (MultiplyWords.guard fields delta) state := rfl

theorem loop_ignore_carry (fuel : Nat) (fields : MultiplyWords.Fields) (delta : Word) (state : Machine32.State) (carry : Bool) :
    MultiplyLoop.loop fuel fields delta { state with carry := carry } = MultiplyLoop.loop fuel fields delta state := by
  cases fuel <;> simp only [MultiplyLoop.loop, guard_ignore_carry] <;> rfl

theorem clear_carry_memory (state : Machine32.State) (field : Nat) : (clearCarry state).memory field = state.memory field := rfl

theorem lift_length (program : List MultiplyWords.Instruction) : (lift program).length = program.length := by simp [lift]

end SmcTuring.Appendix.MultiplyControl
