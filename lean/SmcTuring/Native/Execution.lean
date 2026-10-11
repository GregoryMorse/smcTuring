module
public import SmcTuring.Native.Arithmetic

public section

namespace SmcTuring.Native.Execution

/-- Sequential, non-faulting projection of the selected flat-segment ISA forms.
Only CF is observed by this construction. Permissions, canonical addresses,
CET, other architectural state and hardware fetch discipline are separate
realization conditions, rather than hidden claims about this effect model. -/
structure State (mode : Mode) where
  pc : Word mode
  accumulator : Word mode
  stack : Word mode
  carry : Bool
  memory : ByteMemory.Memory

/-- A full-width byte load is always defined in the sequential memory model. -/
@[expose] def load (mode : Mode) (memory : ByteMemory.Memory) (address : Word mode) : Word mode :=
  BitVec.ofNat (8 * mode.wordBytes)
    (LittleEndian.pack (ByteMemory.bytesAt memory address.toNat mode.wordBytes))

@[expose] def nextPC (mode : Mode) (form : Form mode) (state : State mode) : Word mode :=
  state.pc + Arithmetic.encodeNat mode (instructionLength mode form)

/-- Near relative CALL sign-extends rel32 in long mode. In x86, addition
already takes place in the 32-bit instruction-pointer word. -/
@[expose] def displacementWord (mode : Mode) (displacement : BitVec 32) : Word mode :=
  match mode with
  | .x86 => displacement
  | .x64 => displacement.signExtend 64

/-- The selected ModR/M memory operand is absolute disp32 in x86 and
relative to the complete next instruction (including SBB's imm8) in x64. -/
@[expose] def memoryAddress (mode : Mode) (next : Word mode) (displacement : BitVec 32) : Word mode :=
  match mode with
  | .x86 => displacement
  | .x64 => BitVec.add next (displacement.signExtend (8 * Mode.x64.wordBytes))

@[expose] def storeState (mode : Mode) (state : State mode)
    (next address value : Word mode) (carry : Bool) : State mode :=
  { state with pc := next, carry := carry, memory := ByteMemory.putWord mode state.memory address.toNat value }

/-- CALL pushes the next IP at decremented SP. Its target is an already
evaluated argument, so an aliased return-slot write cannot change that target. -/
@[expose] def callState (mode : Mode) (state : State mode) (next target : Word mode) : State mode :=
  let stack := state.stack - Arithmetic.encodeNat mode mode.wordBytes
  { state with pc := target, stack := stack, memory := ByteMemory.putWord mode state.memory stack.toNat next }

@[expose] def executeMemory (mode : Mode) (operation : MemoryOp)
    (state : State mode) (next address : Word mode) : State mode :=
  let prior := load mode state.memory address
  match operation with
  | .exchangeAcc =>
    { state with pc := next, accumulator := prior, memory := ByteMemory.putWord mode state.memory address.toNat state.accumulator }
  | .storeAcc => storeState mode state next address state.accumulator state.carry
  | .add => storeState mode state next address (prior + state.accumulator)
      (BitVec.uaddOverflow prior state.accumulator)
  | .subtract => storeState mode state next address (prior - state.accumulator)
      (Arithmetic.unsignedBorrow prior state.accumulator)
  | .bitXor => storeState mode state next address (prior ^^^ state.accumulator) false
  | .bitAnd => storeState mode state next address (prior &&& state.accumulator) false
  | .exchangeStack =>
    { state with pc := next, stack := prior, memory := ByteMemory.putWord mode state.memory address.toNat state.stack }
  | .storeStack => storeState mode state next address state.stack state.carry
  | .subtractBorrowZero => storeState mode state next address (prior - (if state.carry then 1 else 0))
      (decide (prior.toNat < (if state.carry then 1 else 0 : Nat)))
  | .callIndirect => callState mode state next prior

@[expose] def execute (mode : Mode) (form : Form mode) (state : State mode) : State mode :=
  let next := nextPC mode form state
  match form with
  | .moffs address => storeState mode state next address state.accumulator state.carry
  | .memory operation displacement =>
    executeMemory mode operation state next (memoryAddress mode next displacement)
  | .exchangeIndirect =>
    { state with pc := next, accumulator := load mode state.memory state.accumulator, memory := ByteMemory.putWord mode state.memory state.accumulator.toNat state.accumulator }
  | .callRelative displacement => callState mode state next (next + displacementWord mode displacement)

/-- Decode the supplied instruction window from current memory. Determining
packet length from the immutable opcode and proving actual hardware fetch are
separate obligations; no stale operand is substituted into this packet step. -/
@[expose] def executeBytes (mode : Mode) (length : Nat) (state : State mode) : Option (State mode) :=
  (decode mode (ByteMemory.bytesAt state.memory state.pc.toNat length)).map
    (fun form => execute mode form state)

@[expose] def CarryPreserving {mode : Mode} : Form mode -> Prop
  | .memory operation _ => match operation with
    | .exchangeAcc | .storeAcc | .exchangeStack | .storeStack | .callIndirect => True
    | _ => False
  | _ => True

@[expose] def runForms (mode : Mode) : List (Form mode) -> State mode -> State mode
  | [], state => state
  | form :: rest, state => runForms mode rest (execute mode form state)

theorem read_word_total (mode : Mode) (memory : ByteMemory.Memory) (address : Word mode) :
    ByteMemory.readWord mode memory address.toNat = some (load mode memory address) := by
  simp [ByteMemory.readWord, LittleEndian.wordDecode, load]

theorem load_put_word (mode : Mode) (memory : ByteMemory.Memory) (address value : Word mode) :
    load mode (ByteMemory.putWord mode memory address.toNat value) address = value := by
  have written := ByteMemory.read_put_word mode memory address.toNat value
  rw [read_word_total mode _ address] at written
  exact Option.some.inj written

theorem execute_byte_encoding (mode : Mode) (form : Form mode) (state : State mode)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat (encode mode form).length = encode mode form) :
    executeBytes mode (encode mode form).length state = some (execute mode form state) := by
  simp only [executeBytes, current, form_roundtrip, Option.map_some]

theorem execute_preserves_carry (mode : Mode) (form : Form mode) (state : State mode)
    (preserves : CarryPreserving form) : (execute mode form state).carry = state.carry := by
  cases form with
  | moffs address => rfl
  | exchangeIndirect => rfl
  | callRelative displacement => rfl
  | memory operation displacement =>
    cases operation <;> simp_all [CarryPreserving, execute, executeMemory, storeState, callState]

theorem run_preserves_carry (mode : Mode) (forms : List (Form mode)) (state : State mode)
    (preserves : forall form, List.Mem form forms -> CarryPreserving form) :
    (runForms mode forms state).carry = state.carry := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih =>
    have head := preserves form (List.Mem.head rest)
    have tail : forall next, List.Mem next rest -> CarryPreserving next := by
      intro next member
      exact preserves next (List.Mem.tail form member)
    exact (ih (execute mode form state) tail).trans (execute_preserves_carry mode form state head)

theorem execute_byte_carry (mode : Mode) (length : Nat) (form : Form mode) (state : State mode)
    (current : decode mode (ByteMemory.bytesAt state.memory state.pc.toNat length) = some form)
    (preserves : CarryPreserving form) :
    (executeBytes mode length state).map State.carry = some state.carry := by
  simp only [executeBytes, current, Option.map_some, execute_preserves_carry mode form state preserves]

theorem moffs_written_value (mode : Mode) (address : Word mode) (state : State mode) :
    load mode (execute mode (.moffs address) state).memory address = state.accumulator := by
  exact load_put_word mode state.memory address state.accumulator

theorem indirect_exchange_accumulator (mode : Mode) (state : State mode) :
    (execute mode .exchangeIndirect state).accumulator = load mode state.memory state.accumulator := rfl

theorem indirect_exchange_written_value (mode : Mode) (state : State mode) :
    load mode (execute mode .exchangeIndirect state).memory state.accumulator = state.accumulator := by
  exact load_put_word mode state.memory state.accumulator state.accumulator

theorem call_accumulator_frame (mode : Mode) (state : State mode) (next target : Word mode) :
    (callState mode state next target).accumulator = state.accumulator := rfl

theorem call_stack (mode : Mode) (state : State mode) (next target : Word mode) :
    (callState mode state next target).stack = state.stack - Arithmetic.encodeNat mode mode.wordBytes := rfl

theorem call_return_word (mode : Mode) (state : State mode) (next target : Word mode) :
    load mode (callState mode state next target).memory
      (state.stack - Arithmetic.encodeNat mode mode.wordBytes) = next := by
  exact load_put_word mode state.memory _ next

theorem indirect_call_target (mode : Mode) (state : State mode) (displacement : BitVec 32) :
    (execute mode (.memory .callIndirect displacement) state).pc =
      load mode state.memory (memoryAddress mode (nextPC mode (.memory .callIndirect displacement) state) displacement) := rfl

theorem indirect_call_alias (mode : Mode) (state : State mode) (displacement : BitVec 32)
    (sameSlot : memoryAddress mode (nextPC mode (.memory .callIndirect displacement) state) displacement =
      state.stack - Arithmetic.encodeNat mode mode.wordBytes) :
    And ((execute mode (.memory .callIndirect displacement) state).pc =
          load mode state.memory (state.stack - Arithmetic.encodeNat mode mode.wordBytes))
        (load mode (execute mode (.memory .callIndirect displacement) state).memory
          (state.stack - Arithmetic.encodeNat mode mode.wordBytes) =
          nextPC mode (.memory .callIndirect displacement) state) := by
  constructor
  case left => rw [indirect_call_target, sameSlot]
  case right => exact call_return_word mode state _ _

theorem subtract_carry (mode : Mode) (state : State mode) (displacement : BitVec 32) :
    (execute mode (.memory .subtract displacement) state).carry =
      Arithmetic.unsignedBorrow
        (load mode state.memory (memoryAddress mode (nextPC mode (.memory .subtract displacement) state) displacement))
        state.accumulator := rfl

theorem sbb_written_value (mode : Mode) (state : State mode) (displacement : BitVec 32) :
    load mode (execute mode (.memory .subtractBorrowZero displacement) state).memory
      (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero displacement) state) displacement) =
      load mode state.memory (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero displacement) state) displacement) -
        (if state.carry then 1 else 0) := by
  exact load_put_word mode state.memory _ _

theorem sbb_zero_result (mode : Mode) (state : State mode) (displacement : BitVec 32)
    (zero : load mode state.memory (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero displacement) state) displacement) = 0) :
    load mode (execute mode (.memory .subtractBorrowZero displacement) state).memory
      (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero displacement) state) displacement) =
      Arithmetic.sbbZero mode state.carry := by
  rw [sbb_written_value, zero]
  simp [Arithmetic.sbbZero]

theorem sbb_zero_carry (mode : Mode) (state : State mode) (displacement : BitVec 32)
    (zero : load mode state.memory (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero displacement) state) displacement) = 0) :
    (execute mode (.memory .subtractBorrowZero displacement) state).carry = state.carry := by
  change decide ((load mode state.memory _).toNat < (if state.carry then 1 else 0 : Nat)) = state.carry
  rw [zero]
  cases state.carry <;> simp

theorem xor_carry_clear (mode : Mode) (state : State mode) (displacement : BitVec 32) :
    (execute mode (.memory .bitXor displacement) state).carry = false := rfl

theorem and_carry_clear (mode : Mode) (state : State mode) (displacement : BitVec 32) :
    (execute mode (.memory .bitAnd displacement) state).carry = false := rfl


/-- Each trace event is decoded from that event's current memory and PC.
Packet lengths and non-faulting validity remain explicit at this layer. -/
inductive Trace (mode : Mode) : State mode -> List (Form mode) -> State mode -> Prop where
  | nil (state : State mode) : Trace mode state [] state
  | step {state finish : State mode} {form : Form mode} {rest : List (Form mode)}
      (fetched : decode mode (ByteMemory.bytesAt state.memory state.pc.toNat (instructionLength mode form)) = some form)
      (tail : Trace mode (execute mode form state) rest finish) : Trace mode state (form :: rest) finish

/-- Actual decoded traces agree with the selected instruction evaluator. -/
theorem trace_run_eq (mode : Mode) {state finish : State mode} {forms : List (Form mode)}
    (trace : Trace mode state forms finish) : finish = runForms mode forms state := by
  induction trace with
  | nil => rfl
  | step fetched tail ih => exact ih

/-- Arbitrary decoded MOV/XCHG/near-CALL chains preserve the incoming CF. -/
theorem trace_preserves_carry (mode : Mode) {state finish : State mode} {forms : List (Form mode)}
    (trace : Trace mode state forms finish)
    (preserves : forall form, List.Mem form forms -> CarryPreserving form) : finish.carry = state.carry := by
  rw [trace_run_eq mode trace]
  exact run_preserves_carry mode forms state preserves

/-- The CF consumed after a decoded reader/call bridge is the prior SUB borrow. -/
theorem sub_bridge_sbb_mask (mode : Mode) (state finish : State mode) (subDisp sbbDisp : BitVec 32)
    (forms : List (Form mode))
    (bridge : Trace mode (execute mode (.memory .subtract subDisp) state) forms finish)
    (preserves : forall form, List.Mem form forms -> CarryPreserving form)
    (zero : load mode finish.memory (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero sbbDisp) finish) sbbDisp) = 0) :
    load mode (execute mode (.memory .subtractBorrowZero sbbDisp) finish).memory
      (memoryAddress mode (nextPC mode (.memory .subtractBorrowZero sbbDisp) finish) sbbDisp) =
      Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow
        (load mode state.memory (memoryAddress mode (nextPC mode (.memory .subtract subDisp) state) subDisp))
        state.accumulator) := by
  rw [sbb_zero_result mode finish sbbDisp zero, trace_preserves_carry mode bridge preserves, subtract_carry]

/-- A live MOFFS packet executes with its new address after a payload patch. -/
theorem execute_patched_moffs (mode : Mode) (state : State mode) (old fresh : Word mode) :
    let patched : State mode := { state with memory := ByteMemory.putWord mode (ByteMemory.putBytes state.memory state.pc.toNat (encode mode (.moffs old))) (state.pc.toNat + moffsOperandOffset mode) fresh }
    executeBytes mode (moffsOperandOffset mode + mode.wordBytes) patched =
      some (execute mode (.moffs fresh) patched) := by
  have fetched := ByteMemory.fetch_patched_moffs mode state.memory state.pc.toNat old fresh
  unfold ByteMemory.fetchMoffs at fetched
  simp only [executeBytes, fetched, Option.map_some]

end SmcTuring.Native.Execution
