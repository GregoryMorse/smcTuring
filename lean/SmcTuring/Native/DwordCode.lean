module
public import SmcTuring.Native.Relocation
public import SmcTuring.Native.Writes

public section
namespace SmcTuring.Native.DwordCode
open LittleEndian
abbrev Dword := BitVec 32

/-- Bare DWORD accumulator forms. Address width remains the mode's width;
long-mode data writes are four bytes and register writes zero-extend EAX. -/
inductive Form (mode : Mode) where
  | exchange (displacement : Dword)
  | store (displacement : Dword)
  | moffs (address : Word mode)
  deriving DecidableEq, Repr

@[expose] def encode (mode : Mode) : Form mode → List Byte
  | .exchange displacement => [0x87,0x05] ++ wordEncode 4 displacement
  | .store displacement => [0x89,0x05] ++ wordEncode 4 displacement
  | .moffs address => [0xa3] ++ wordEncode mode.wordBytes address
@[expose] def decode (mode : Mode) (bytes : List Byte) : Option (Form mode) :=
  (Native.decodeCore mode bytes).bind fun form =>
    match form with
    | .memory .exchangeAcc displacement => some (.exchange displacement)
    | .memory .storeAcc displacement => some (.store displacement)
    | .moffs address => some (.moffs address)
    | _ => none
@[expose] def length (mode : Mode) : Form mode → Nat
  | .moffs _ => 1 + mode.wordBytes
  | _ => 6
@[expose] def header {mode : Mode} : Form mode → Byte
  | .exchange _ => 0x87
  | .store _ => 0x89
  | .moffs _ => 0xa3
@[expose] def packetSize (mode : Mode) (opcode : Byte) : Nat :=
  if opcode = 0xa3 then 1 + mode.wordBytes else 6
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  decode mode (ByteMemory.bytesAt memory pc (packetSize mode (memory pc)))

theorem roundtrip (mode : Mode) (form : Form mode) : decode mode (encode mode form) = some form := by
  cases form with
  | exchange displacement =>
    have taken : (wordEncode 4 displacement).take 4 = wordEncode 4 displacement := rfl
    simp [decode,encode,Native.decodeCore,Native.operationOfTag,
      Native.decodeMemoryPayload,MemoryOp.trailer,taken]
  | store displacement =>
    have taken : (wordEncode 4 displacement).take 4 = wordEncode 4 displacement := rfl
    simp [decode,encode,Native.decodeCore,Native.operationOfTag,
      Native.decodeMemoryPayload,MemoryOp.trailer,taken]
  | moffs address => simp [decode,encode,Native.decodeCore]

theorem encode_injective (mode : Mode) : Function.Injective (encode mode) := by
  intro first second same
  have decoded := congrArg (decode mode) same
  simpa only [roundtrip,Option.some.injEq] using decoded

theorem encode_length (mode : Mode) (form : Form mode) : (encode mode form).length = length mode form := by
  cases form <;> simp [encode,length,Nat.add_comm]

theorem length_bound (mode : Mode) (form : Form mode) : 0 < length mode form ∧ length mode form ≤ 15 := by
  cases mode <;> cases form <;> simp [length,Mode.wordBytes]

theorem current_header (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode)
    (current : ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form) :
    memory pc = header form := by
  have first := congrArg (fun bytes : List Byte => bytes[0]?) current
  cases form with
  | exchange displacement =>
    change some (memory pc) = some (0x87 : Byte) at first
    exact Option.some.inj first
  | store displacement =>
    change some (memory pc) = some (0x89 : Byte) at first
    exact Option.some.inj first
  | moffs address =>
    cases mode <;> change some (memory pc) = some (0xa3 : Byte) at first <;> exact Option.some.inj first

theorem fetch_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode)
    (current : ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form) :
    fetch mode memory pc = some form := by
  have size : packetSize mode (header form) = length mode form := by cases form <;> simp [packetSize,header,length]
  rw [fetch,current_header mode memory pc form current,size,←encode_length,current,roundtrip]

@[expose] def low (mode : Mode) (value : Word mode) : Dword := BitVec.ofNat 32 value.toNat
@[expose] def lift (mode : Mode) (value : Dword) : Word mode := Arithmetic.encodeNat mode value.toNat
@[expose] def get (memory : ByteMemory.Memory) (address : Nat) : Dword :=
  BitVec.ofNat 32 (pack (ByteMemory.bytesAt memory address 4))

@[expose] def put (memory : ByteMemory.Memory) (address : Nat) (value : Dword) : ByteMemory.Memory :=
  ByteMemory.putBytes memory address (wordEncode 4 value)

theorem put_word (memory : ByteMemory.Memory) (address : Nat) (value : Dword) :
    put memory address value = ByteMemory.putWord .x86 memory address value := rfl

theorem put_overwrite (memory : ByteMemory.Memory) (address : Nat) (old fresh : Dword) :
    put (put memory address old) address fresh = put memory address fresh :=
  Writes.put_bytes_overwrite memory address _ _ (by simp only [word_encode_length])

theorem put_commute (memory : ByteMemory.Memory) (first second : Nat) (a b : Dword)
    (separate : ∀ index : Fin 4, ¬ByteMemory.Inside second 4 (first+index.val)) :
    put (put memory first a) second b = put (put memory second b) first a := by
  apply Writes.put_bytes_commute
  intro position inside
  have within : ByteMemory.Inside first 4 position := by simpa only [word_encode_length] using inside
  have bound : position-first < 4 := by unfold ByteMemory.Inside at within; omega
  have outside := separate ⟨position-first,bound⟩
  simpa only [word_encode_length,Nat.add_sub_of_le within.1] using outside

theorem lift_toNat (mode : Mode) (value : Dword) : (lift mode value).toNat = value.toNat := by
  apply Arithmetic.encode_nat_toNat
  have small := value.isLt
  cases mode <;> simp only [Mode.wordBytes] <;> omega

theorem low_lift (mode : Mode) (value : Dword) : low mode (lift mode value) = value := by
  unfold low
  rw [lift_toNat]
  simpa only [BitVec.setWidth_eq] using BitVec.ofNat_toNat 32 value

theorem lift_low_x86 (value : Word .x86) : lift .x86 (low .x86 value) = value := by
  change BitVec 32 at value
  change BitVec.ofNat 32 (BitVec.ofNat 32 value.toNat).toNat = value
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt value.isLt,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem lift_low_x64_bound (value : Word .x64) : (lift .x64 (low .x64 value)).toNat < 2^32 := by
  rw [lift_toNat]
  exact (low .x64 value).isLt

theorem read_total (memory : ByteMemory.Memory) (address : Nat) :
    ByteMemory.readWord .x86 memory address = some (get memory address) := by
  rfl

theorem get_put (memory : ByteMemory.Memory) (address : Nat) (value : Dword) :
    get (put memory address value) address = value := by
  have read := ByteMemory.read_put_word .x86 memory address value
  change ByteMemory.readWord .x86 (put memory address value) address = some value at read
  rw [read_total] at read
  exact Option.some.inj read

theorem put_get_back (memory : ByteMemory.Memory) (address : Nat) :
    put memory address (get memory address) = memory := by
  have encoded := word_encode_decode 4 _ _ (read_total memory address)
  change wordEncode 4 (get memory address) = ByteMemory.bytesAt memory address 4 at encoded
  change ByteMemory.putBytes memory address (wordEncode 4 (get memory address)) = memory
  rw [encoded]
  exact Writes.put_bytes_back memory address 4

theorem get_frame (memory : ByteMemory.Memory) (written observed : Nat) (value : Dword)
    (separate : ∀ index : Fin 4, ¬ByteMemory.Inside written 4 (observed + index.val)) :
    get (put memory written value) observed = get memory observed := by
  have framed := ByteMemory.bytes_at_frame memory written (wordEncode 4 value) observed 4
    (by simpa only [word_encode_length] using separate)
  exact congrArg (fun bytes => BitVec.ofNat 32 (pack bytes)) framed

@[expose] def next (mode : Mode) (form : Form mode) (state : Execution.State mode) : Word mode :=
  state.pc + Arithmetic.encodeNat mode (length mode form)
@[expose] def address (mode : Mode) (form : Form mode) (state : Execution.State mode) : Word mode :=
  match form with
  | .moffs target => target
  | .exchange displacement | .store displacement => Execution.memoryAddress mode (next mode form state) displacement
@[expose] def execute (mode : Mode) (form : Form mode) (state : Execution.State mode) : Execution.State mode :=
  let target := (address mode form state).toNat
  match form with
  | .exchange _ =>
    { state with
      pc := next mode form state
      accumulator := lift mode (get state.memory target)
      memory := put state.memory target (low mode state.accumulator) }
  | _ =>
    { state with
      pc := next mode form state
      memory := put state.memory target (low mode state.accumulator) }
@[expose] def step (mode : Mode) (state : Execution.State mode) : Option (Execution.State mode) :=
  (fetch mode state.memory state.pc.toNat).map (fun form => execute mode form state)

inductive Trace (mode : Mode) : Execution.State mode → List (Form mode) → Execution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state forms final form} (current : fetch mode state.memory state.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem step_encoding (mode : Mode) (state : Execution.State mode) (form : Form mode)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat (encode mode form).length = encode mode form) :
    step mode state = some (execute mode form state) := by
  rw [step,fetch_encoding mode state.memory state.pc.toNat form current]
  rfl

theorem memory (mode : Mode) (form : Form mode) (state : Execution.State mode) :
    (execute mode form state).memory =
      put state.memory (address mode form state).toNat (low mode state.accumulator) := by
  cases form <;> rfl

theorem preserved (mode : Mode) (form : Form mode) (state : Execution.State mode) :
    (execute mode form state).stack = state.stack ∧ (execute mode form state).carry = state.carry := by
  cases form <;> exact ⟨rfl,rfl⟩

theorem frame (mode : Mode) (form : Form mode) (state : Execution.State mode) (position : Nat)
    (outside : ¬ByteMemory.Inside (address mode form state).toNat 4 position) :
    (execute mode form state).memory position = state.memory position := by
  rw [memory]
  apply ByteMemory.put_frame
  change ¬ByteMemory.Inside (address mode form state).toNat 4 position
  exact outside

theorem write_nonempty (mode : Mode) (form : Form mode) (state : Execution.State mode) :
    ByteMemory.Inside (address mode form state).toNat 4 (address mode form state).toNat := by
  unfold ByteMemory.Inside
  omega

/-- Each decoded instruction has the complete four-byte write footprint
proved above; this predicate follows its actual state-dependent address. -/
@[expose] def OwnedRun (mode : Mode) (owned : Nat → Prop) : List (Form mode) → Execution.State mode → Prop
  | [], _ => True
  | form::forms, state => owned (address mode form state).toNat ∧ OwnedRun mode owned forms (execute mode form state)

end SmcTuring.Native.DwordCode
