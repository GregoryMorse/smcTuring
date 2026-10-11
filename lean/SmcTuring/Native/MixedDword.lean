module
public import SmcTuring.Native.DwordArithmetic

public section
namespace SmcTuring.Native.MixedDword
open LittleEndian
/-- A decoder for the DWORD arithmetic/helper forms and full-width x64 cursor
exchange. Its constructor index excludes a REX.W exchange in x86 mode. -/
inductive Form : Mode → Type
  | arithmetic {mode} (form : DwordArithmetic.Form) : Form mode
  | copy {mode} (form : DwordCode.Form mode) : Form mode
  | wideExchange (displacement : BitVec 32) : Form .x64
  deriving DecidableEq, Repr

@[expose] def encode (mode : Mode) : Form mode → List Byte
  | .arithmetic form => DwordArithmetic.encode form
  | .copy form => DwordCode.encode mode form
  | .wideExchange d => Native.encode .x64 (.memory .exchangeAcc d)
@[expose] def length (mode : Mode) : Form mode → Nat
  | .arithmetic form => DwordArithmetic.length form
  | .copy form => DwordCode.length mode form
  | .wideExchange _ => 7
@[expose] def execute (mode : Mode) : Form mode → Execution.State mode → Execution.State mode
  | .arithmetic form => DwordArithmetic.execute mode form
  | .copy form => DwordCode.execute mode form
  | .wideExchange d => Execution.execute .x64 (.memory .exchangeAcc d)

/-- Current header chooses DWORD arithmetic, a bare DWORD helper, or REX.W.
The actual selected decoder then validates the complete current packet. -/
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  match DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) with
  | some _ => (DwordArithmetic.fetch memory pc).map Form.arithmetic
  | none => match mode with
    | .x86 => (DwordCode.fetch .x86 memory pc).map Form.copy
    | .x64 => if memory pc = 0x48 then
        (Fetch.fetch .x64 memory pc).bind fun form => match form with
          | .memory .exchangeAcc d => some (.wideExchange d)
          | _ => none
      else (DwordCode.fetch .x64 memory pc).map Form.copy

@[expose] def step (mode : Mode) (state : Execution.State mode) : Option (Execution.State mode) :=
  (fetch mode state.memory state.pc.toNat).map (fun form => execute mode form state)
inductive Trace (mode : Mode) : Execution.State mode → List (Form mode) → Execution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state forms final form} (current : fetch mode state.memory state.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem encode_length (mode : Mode) (form : Form mode) : (encode mode form).length = length mode form := by
  cases form with
  | arithmetic form => exact DwordArithmetic.encode_length form
  | copy form => exact DwordCode.encode_length mode form
  | wideExchange d => rfl

theorem arithmetic_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : DwordArithmetic.Form)
    (current : DwordArithmetic.fetch memory pc = some form) :
    fetch mode memory pc = some (.arithmetic form) := by
  have full := current
  unfold DwordArithmetic.fetch at current
  cases header : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) with
  | none => simp only [header,Option.bind_none] at current; cases current
  | some n => simp only [fetch.eq_def,header,full,Option.map_some]

theorem arithmetic_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : DwordArithmetic.Form)
    (current : ByteMemory.bytesAt memory pc (DwordArithmetic.encode form).length = DwordArithmetic.encode form) :
    fetch mode memory pc = some (.arithmetic form) :=
  arithmetic_fetch mode memory pc form (DwordArithmetic.fetch_encoding memory pc form current)

theorem copy_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : DwordCode.Form mode)
    (current : ByteMemory.bytesAt memory pc (DwordCode.encode mode form).length = DwordCode.encode mode form) :
    fetch mode memory pc = some (.copy form) := by
  have bound : 2 ≤ (DwordCode.encode mode form).length := by
    rw [DwordCode.encode_length]
    cases mode <;> cases form <;> simp [DwordCode.length,Mode.wordBytes]
  have header : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) = none := by
    rw [←Fetch.bytes_at_take memory pc _ 2 bound,current]
    cases form <;> rfl
  simp only [fetch.eq_def,header]
  have actual := DwordCode.fetch_encoding mode memory pc form current
  cases mode with
  | x86 => rw [actual]; rfl
  | x64 =>
    have first := DwordCode.current_header .x64 memory pc form current
    have bare : memory pc ≠ 0x48 := by
      rw [first]
      cases form <;> simp [DwordCode.header]
    rw [ite_eq_right bare,actual]
    rfl

theorem wide_encoding (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32)
    (current : ByteMemory.bytesAt memory pc 7 = Native.encode .x64 (.memory .exchangeAcc d)) :
    fetch .x64 memory pc = some (.wideExchange d) := by
  have header : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) = none := by
    rw [←Fetch.bytes_at_take memory pc 7 2 (by decide),current]
    rfl
  have first := congrArg (fun bytes : List Byte => bytes[0]?) current
  change some (memory pc) = some (0x48 : Byte) at first
  have rex : memory pc = 0x48 := Option.some.inj first
  simp only [fetch.eq_def,header,ite_eq_left rex,
    Fetch.fetch_current_encoding .x64 memory pc (.memory .exchangeAcc d) current,Option.bind_some]

theorem current_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode)
    (current : ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form) :
    fetch mode memory pc = some form := by
  cases form with
  | arithmetic form => exact arithmetic_encoding mode memory pc form current
  | copy form => exact copy_encoding mode memory pc form current
  | wideExchange d => exact wide_encoding memory pc d current

theorem step_encoding (mode : Mode) (state : Execution.State mode) (form : Form mode)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat (encode mode form).length = encode mode form) :
    step mode state = some (execute mode form state) := by
  rw [step,current_encoding mode state.memory state.pc.toNat form current]
  rfl

theorem arithmetic_trace (mode : Mode) {state final : Execution.State mode} {forms : List DwordArithmetic.Form}
    (trace : DwordArithmetic.Trace mode state forms final) :
    Trace mode state (forms.map Form.arithmetic) final := by
  induction trace with
  | nil state => exact .nil state
  | step current rest ih => exact .step (arithmetic_fetch mode _ _ _ current) ih

theorem trace_append (mode : Mode) {state middle final : Execution.State mode} {first second : List (Form mode)}
    (left : Trace mode state first middle) (right : Trace mode middle second final) :
    Trace mode state (first++second) final := by
  induction left with
  | nil => exact right
  | step current rest ih => exact .step current (ih right)

@[expose] def exchange (mode : Mode) (d : BitVec 32) : Form mode :=
  match mode with | .x86 => .copy (.exchange d) | .x64 => .wideExchange d

theorem exchange_bytes (mode : Mode) (d : BitVec 32) :
    encode mode (exchange mode d) = Native.encode mode (.memory .exchangeAcc d) := by
  cases mode <;> rfl

theorem exchange_length (mode : Mode) (d : BitVec 32) :
    length mode (exchange mode d) = instructionLength mode (.memory .exchangeAcc d) := by
  cases mode <;> rfl

theorem exchange_execution (mode : Mode) (d : BitVec 32) (state : Execution.State mode) :
    execute mode (exchange mode d) state = Execution.execute mode (.memory .exchangeAcc d) state := by
  cases mode with
  | x64 => rfl
  | x86 =>
    change { state with
      pc := state.pc+Arithmetic.encodeNat .x86 6
      accumulator := DwordCode.lift .x86 (DwordCode.get state.memory d.toNat)
      memory := DwordCode.put state.memory d.toNat (DwordCode.low .x86 state.accumulator) } =
      { state with
        pc := state.pc+Arithmetic.encodeNat .x86 6
        accumulator := Execution.load .x86 state.memory d
        memory := ByteMemory.putWord .x86 state.memory d.toNat state.accumulator }
    have identity32 (value : BitVec 32) : BitVec.ofNat 32 value.toNat = value := by
      simpa only [BitVec.setWidth_eq] using BitVec.ofNat_toNat 32 value
    have low : DwordCode.low .x86 state.accumulator = state.accumulator := by
      change BitVec.ofNat 32 state.accumulator.toNat = state.accumulator
      exact identity32 state.accumulator
    have lifted : DwordCode.lift .x86 (DwordCode.get state.memory d.toNat) = Execution.load .x86 state.memory d := by
      change BitVec.ofNat 32 (Execution.load .x86 state.memory d).toNat = Execution.load .x86 state.memory d
      exact identity32 (Execution.load .x86 state.memory d)
    rw [low,lifted]
    rfl

@[expose] def address (mode : Mode) : Form mode → Execution.State mode → Word mode
  | .arithmetic form => DwordArithmetic.address mode form
  | .copy form => DwordCode.address mode form
  | .wideExchange d => fun state => Execution.memoryAddress .x64
      (Execution.nextPC .x64 (.memory .exchangeAcc d) state) d
@[expose] def width (mode : Mode) : Form mode → Nat
  | .wideExchange _ => 8
  | _ => 4
@[expose] def OwnedRun (mode : Mode) (owned : Nat → Nat → Prop) :
    List (Form mode) → Execution.State mode → Prop
  | [], _ => True
  | form::forms, state => owned (address mode form state).toNat (width mode form) ∧
      OwnedRun mode owned forms (execute mode form state)

theorem exchange_address (mode : Mode) (d : BitVec 32) (state : Execution.State mode) :
    address mode (exchange mode d) state =
      Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc d) state) d := by
  cases mode <;> rfl

theorem exchange_width (mode : Mode) (d : BitVec 32) :
    width mode (exchange mode d) = mode.wordBytes := by cases mode <;> rfl

theorem write_nonempty (mode : Mode) (form : Form mode) (state : Execution.State mode) :
    ByteMemory.Inside (address mode form state).toNat (width mode form) (address mode form state).toNat := by
  cases form <;> simp [width,ByteMemory.Inside]

theorem frame (mode : Mode) (form : Form mode) (state : Execution.State mode) (position : Nat)
    (outside : ¬ByteMemory.Inside (address mode form state).toNat (width mode form) position) :
    (execute mode form state).memory position = state.memory position := by
  cases form with
  | arithmetic form => exact DwordArithmetic.frame mode form state position outside
  | copy form => exact DwordCode.frame mode form state position outside
  | wideExchange d =>
    have size := LittleEndian.word_encode_length Mode.x64.wordBytes state.accumulator
    exact ByteMemory.put_frame _ _ _ _ (by rw [size]; exact outside)

end SmcTuring.Native.MixedDword
