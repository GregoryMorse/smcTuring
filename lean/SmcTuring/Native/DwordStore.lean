module
public import SmcTuring.Appendix.ByteCode
public import SmcTuring.Native.Relocation

public section
namespace SmcTuring.Native.DwordStore

open LittleEndian
abbrev Dword := BitVec 32

/-- C7 /0 with ModR/M 05 and a DWORD immediate, without REX.W in either mode.
The same displacement bytes denote absolute x86 or RIP-relative x64 memory. -/
structure Form where
  displacement : Dword
  value : Dword
  deriving DecidableEq, Repr

@[expose] def common (form : Form) : Appendix.ByteCode.Form :=
  .immediate .store form.displacement form.value
@[expose] def encode (form : Form) : List Byte := Appendix.ByteCode.encode (common form)
@[expose] def decode (bytes : List Byte) : Option Form :=
  match Appendix.ByteCode.decode bytes with
  | some (.immediate .store displacement value) => some ⟨displacement, value⟩
  | _ => none

theorem roundtrip (form : Form) : decode (encode form) = some form := by
  cases form with
  | mk displacement value =>
    simp only [decode, encode, common, Appendix.ByteCode.form_roundtrip]

theorem length (form : Form) : (encode form).length = 10 := by
  exact Appendix.ByteCode.encode_length (common form)

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [roundtrip, Option.some.injEq] using decoded

@[expose] def fetch (memory : ByteMemory.Memory) (pc : Nat) : Option Form :=
  decode (ByteMemory.bytesAt memory pc 10)
@[expose] def next (mode : Mode) (state : Execution.State mode) : Word mode :=
  state.pc + Arithmetic.encodeNat mode 10
@[expose] def address (mode : Mode) (form : Form) (state : Execution.State mode) : Word mode :=
  Execution.memoryAddress mode (next mode state) form.displacement

/-- Exactly four bytes are stored even in long mode; RAX/RSP and CF are
unchanged. The selected nonfaulting/current-fetch environment is explicit. -/
@[expose] def execute (mode : Mode) (form : Form) (state : Execution.State mode) : Execution.State mode :=
  { state with
    pc := next mode state
    memory := ByteMemory.putWord .x86 state.memory (address mode form state).toNat form.value }
@[expose] def step (mode : Mode) (state : Execution.State mode) : Option (Execution.State mode) :=
  (fetch state.memory state.pc.toNat).map (fun form => execute mode form state)

theorem fetch_encoding (memory : ByteMemory.Memory) (pc : Nat) (form : Form)
    (current : ByteMemory.bytesAt memory pc 10 = encode form) : fetch memory pc = some form := by
  rw [fetch, current, roundtrip]

theorem step_encoding (mode : Mode) (state : Execution.State mode) (form : Form)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat 10 = encode form) :
    step mode state = some (execute mode form state) := by
  rw [step, fetch_encoding _ _ _ current]; rfl

theorem registers (mode : Mode) (form : Form) (state : Execution.State mode) :
    (execute mode form state).accumulator = state.accumulator ∧
      (execute mode form state).stack = state.stack ∧
      (execute mode form state).carry = state.carry := ⟨rfl, rfl, rfl⟩

theorem pc (mode : Mode) (form : Form) (state : Execution.State mode) :
    (execute mode form state).pc = next mode state := rfl

theorem memory (mode : Mode) (form : Form) (state : Execution.State mode) :
    (execute mode form state).memory =
      ByteMemory.putWord .x86 state.memory (address mode form state).toNat form.value := rfl

theorem frame (mode : Mode) (form : Form) (state : Execution.State mode) (position : Nat)
    (outside : ¬ByteMemory.Inside (address mode form state).toNat 4 position) :
    (execute mode form state).memory position = state.memory position := by
  exact ByteMemory.put_frame state.memory _ (wordEncode 4 form.value) position
    (by simpa only [word_encode_length] using outside)

theorem written (mode : Mode) (form : Form) (state : Execution.State mode) :
    ByteMemory.bytesAt (execute mode form state).memory (address mode form state).toNat 4 =
      wordEncode 4 form.value := by
  simpa only [execute, ByteMemory.putWord, Mode.wordBytes, word_encode_length] using
    ByteMemory.bytes_at_put state.memory (address mode form state).toNat (wordEncode 4 form.value)

/-- The store has a nonempty architectural footprint even if all bytes already
equal their new values. -/
theorem writes (mode : Mode) (form : Form) (state : Execution.State mode) :
    ByteMemory.Inside (address mode form state).toNat 4 (address mode form state).toNat := by
  unfold ByteMemory.Inside; omega

@[expose] def emit (mode : Mode) (pc target : Nat) (value : Dword) : Form :=
  ⟨Relocation.memoryDisp mode (pc + 10) target, value⟩

theorem emit_address (mode : Mode) (pc target : Nat) (value : Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (reach : mode = .x64 → Relocation.SignedDelta (pc + 10) target) :
    address mode (emit mode pc target value) state = Arithmetic.encodeNat mode target := by
  have nextPC : next mode state = Arithmetic.encodeNat mode (pc + 10) := by
    rw [next, location]; exact BitVec.ofNat_add_ofNat pc 10
  rw [address, nextPC]
  exact Relocation.memory_hits mode (pc + 10) target reach

end SmcTuring.Native.DwordStore
