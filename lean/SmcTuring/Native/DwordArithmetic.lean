module
public import SmcTuring.Native.DwordCode

public section
namespace SmcTuring.Native.DwordArithmetic
open LittleEndian DwordCode
abbrev Dword := BitVec 32

/-- The bare DWORD forms used by Listing 8's comparison and input update.
In long mode ModRM 05 addresses from the actual instruction end; 70 uses RAX+6. -/
inductive Form where
  | store (displacement value : Dword)
  | subtract (displacement value : Dword)
  | bitXor (displacement value : Dword)
  | bitAnd (displacement value : Dword)
  | bitOr (displacement value : Dword)
  | negate (displacement : Dword)
  | complement (displacement : Dword)
  | sbbZero (displacement : Dword)
  | xorAtAccumulator (value : Dword)
  deriving DecidableEq, Repr

@[expose] def encode : Form → List Byte
  | .store d v => [0xc7,0x05] ++ wordEncode 4 d ++ wordEncode 4 v
  | .subtract d v => [0x81,0x2d] ++ wordEncode 4 d ++ wordEncode 4 v
  | .bitXor d v => [0x81,0x35] ++ wordEncode 4 d ++ wordEncode 4 v
  | .bitAnd d v => [0x81,0x25] ++ wordEncode 4 d ++ wordEncode 4 v
  | .bitOr d v => [0x81,0x0d] ++ wordEncode 4 d ++ wordEncode 4 v
  | .negate d => [0xf7,0x1d] ++ wordEncode 4 d
  | .complement d => [0xf7,0x15] ++ wordEncode 4 d
  | .sbbZero d => [0x83,0x1d] ++ wordEncode 4 d ++ [0]
  | .xorAtAccumulator v => [0x81,0x70,6] ++ wordEncode 4 v

@[expose] def twoWords (constructor : Dword → Dword → Form) (bytes : List Byte) : Option Form := do
  let d ← wordDecode 4 (bytes.take 4)
  let v ← wordDecode 4 (bytes.drop 4)
  return constructor d v

@[expose] def decode : List Byte → Option Form
  | 0xc7 :: 0x05 :: bytes => twoWords Form.store bytes
  | 0x81 :: 0x2d :: bytes => twoWords Form.subtract bytes
  | 0x81 :: 0x35 :: bytes => twoWords Form.bitXor bytes
  | 0x81 :: 0x25 :: bytes => twoWords Form.bitAnd bytes
  | 0x81 :: 0x0d :: bytes => twoWords Form.bitOr bytes
  | 0xf7 :: 0x1d :: bytes => (wordDecode 4 bytes).map Form.negate
  | 0xf7 :: 0x15 :: bytes => (wordDecode 4 bytes).map Form.complement
  | 0x83 :: 0x1d :: bytes =>
      if bytes.drop 4 = [0] then (wordDecode 4 (bytes.take 4)).map Form.sbbZero else none
  | 0x81 :: 0x70 :: 6 :: bytes => (wordDecode 4 bytes).map Form.xorAtAccumulator
  | _ => none

theorem two_words (constructor : Dword → Dword → Form) (d v : Dword) :
    twoWords constructor (wordEncode 4 d ++ wordEncode 4 v) = some (constructor d v) := by
  have taken : (wordEncode 4 d ++ wordEncode 4 v).take 4 = wordEncode 4 d := rfl
  have dropped : (wordEncode 4 d ++ wordEncode 4 v).drop 4 = wordEncode 4 v := rfl
  simp only [twoWords,taken,dropped,word_decode_encode]
  rfl

theorem roundtrip (form : Form) : decode (encode form) = some form := by
  cases form <;> simp [encode,decode,two_words]

theorem encode_injective : Function.Injective encode := by
  intro a b same
  have equality := congrArg decode same
  simpa only [roundtrip,Option.some.injEq] using equality

@[expose] def length : Form → Nat
  | .store _ _ | .subtract _ _ | .bitXor _ _ | .bitAnd _ _ | .bitOr _ _ => 10
  | .negate _ | .complement _ => 6
  | _ => 7

theorem encode_length (form : Form) : (encode form).length = length form := by
  cases form <;> simp [encode,length]

@[expose] def packetSize : List Byte → Option Nat
  | 0xc7 :: 0x05 :: _ | 0x81 :: 0x2d :: _ | 0x81 :: 0x35 :: _ | 0x81 :: 0x25 :: _ | 0x81 :: 0x0d :: _ => some 10
  | 0xf7 :: 0x1d :: _ | 0xf7 :: 0x15 :: _ => some 6
  | 0x83 :: 0x1d :: _ | 0x81 :: 0x70 :: _ => some 7
  | _ => none

theorem header_size (form : Form) : packetSize ((encode form).take 2) = some (length form) := by
  cases form <;> rfl

@[expose] def fetch (memory : ByteMemory.Memory) (pc : Nat) : Option Form :=
  (packetSize (ByteMemory.bytesAt memory pc 2)).bind fun n => decode (ByteMemory.bytesAt memory pc n)

theorem fetch_encoding (memory : ByteMemory.Memory) (pc : Nat) (form : Form)
    (current : ByteMemory.bytesAt memory pc (encode form).length = encode form) :
    fetch memory pc = some form := by
  have bound : 2 ≤ (encode form).length := by cases form <;> simp [encode]
  have head : packetSize (ByteMemory.bytesAt memory pc 2) = some (length form) := by
    rw [←Fetch.bytes_at_take memory pc (encode form).length 2 bound,current,header_size]
  rw [fetch,head,Option.bind_some,←encode_length,current,roundtrip]

@[expose] def next (mode : Mode) (form : Form) (state : Execution.State mode) : Word mode :=
  state.pc + Arithmetic.encodeNat mode (length form)
@[expose] def address (mode : Mode) (form : Form) (state : Execution.State mode) : Word mode :=
  match form with
  | .xorAtAccumulator _ => state.accumulator + Arithmetic.encodeNat mode 6
  | .store d _ | .subtract d _ | .bitXor d _ | .bitAnd d _ | .bitOr d _
    | .negate d | .complement d | .sbbZero d => Execution.memoryAddress mode (next mode form state) d
@[expose] def prior (mode : Mode) (form : Form) (state : Execution.State mode) : Dword :=
  get state.memory (address mode form state).toNat
@[expose] def result (form : Form) (old : Dword) (cf : Bool) : Dword :=
  match form with
  | .store _ v => v
  | .subtract _ v => old - v
  | .bitXor _ v | .xorAtAccumulator v => old ^^^ v
  | .bitAnd _ v => old &&& v
  | .bitOr _ v => old ||| v
  | .negate _ => -old
  | .complement _ => ~~~old
  | .sbbZero _ => old - (if cf then 1 else 0)
@[expose] def flag (form : Form) (old : Dword) (cf : Bool) : Bool :=
  match form with
  | .store _ _ | .complement _ => cf
  | .subtract _ v => decide (old.toNat < v.toNat)
  | .bitXor _ _ | .bitAnd _ _ | .bitOr _ _ | .xorAtAccumulator _ => false
  | .negate _ => decide (old ≠ 0)
  | .sbbZero _ => decide (old.toNat < (if cf then 1 else 0 : Nat))
@[expose] def value (mode : Mode) (form : Form) (state : Execution.State mode) : Dword :=
  result form (prior mode form state) state.carry
@[expose] def carry (mode : Mode) (form : Form) (state : Execution.State mode) : Bool :=
  flag form (prior mode form state) state.carry
@[expose] def execute (mode : Mode) (form : Form) (state : Execution.State mode) : Execution.State mode :=
  { state with
    pc := next mode form state
    carry := carry mode form state
    memory := put state.memory (address mode form state).toNat (value mode form state) }
@[expose] def step (mode : Mode) (state : Execution.State mode) : Option (Execution.State mode) :=
  (fetch state.memory state.pc.toNat).map (fun form => execute mode form state)
inductive Trace (mode : Mode) : Execution.State mode → List Form → Execution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state forms final form} (current : fetch state.memory state.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem step_encoding (mode : Mode) (state : Execution.State mode) (form : Form)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat (encode form).length = encode form) :
    step mode state = some (execute mode form state) := by
  rw [step,fetch_encoding state.memory state.pc.toNat form current]
  rfl

theorem registers (mode : Mode) (form : Form) (state : Execution.State mode) :
    (execute mode form state).accumulator = state.accumulator ∧
    (execute mode form state).stack = state.stack := ⟨rfl,rfl⟩

theorem written (mode : Mode) (form : Form) (state : Execution.State mode) :
    get (execute mode form state).memory (address mode form state).toNat = value mode form state :=
  get_put _ _ _

theorem frame (mode : Mode) (form : Form) (state : Execution.State mode) (position : Nat)
    (outside : ¬ByteMemory.Inside (address mode form state).toNat 4 position) :
    (execute mode form state).memory position = state.memory position :=
  ByteMemory.put_frame _ _ _ _ (by simpa only [word_encode_length] using outside)

theorem payload_patch (memory : ByteMemory.Memory) (pc : Nat) (d old fresh : Dword) :
    put (ByteMemory.putBytes memory pc (encode (.subtract d old))) (pc+6) fresh =
      ByteMemory.putBytes memory pc (encode (.subtract d fresh)) := by
  exact ByteMemory.patch_payload memory pc ([0x81,0x2d] ++ wordEncode 4 d)
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp)

theorem base_xor_patch (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Dword) :
    put (ByteMemory.putBytes memory pc (encode (.xorAtAccumulator old))) (pc+3) fresh =
      ByteMemory.putBytes memory pc (encode (.xorAtAccumulator fresh)) := by
  exact ByteMemory.patch_payload memory pc [0x81,0x70,6]
    (wordEncode 4 old) (wordEncode 4 fresh) (by simp)

/-- Replace only the address field; the base-addressed XOR is kept separate. -/
@[expose] def relocate (form : Form) (d : Dword) : Form :=
  match form with
  | .store _ v => .store d v
  | .subtract _ v => .subtract d v
  | .bitXor _ v => .bitXor d v
  | .bitAnd _ v => .bitAnd d v
  | .bitOr _ v => .bitOr d v
  | .negate _ => .negate d
  | .complement _ => .complement d
  | .sbbZero _ => .sbbZero d
  | .xorAtAccumulator v => .xorAtAccumulator v
@[expose] def located (mode : Mode) (form : Form) (pc target : Nat) : Form :=
  relocate form (Relocation.memoryDisp mode (pc+length form) target)
@[expose] def direct : Form → Bool
  | .xorAtAccumulator _ => false
  | _ => true

theorem relocate_length (form : Form) (d : Dword) : length (relocate form d) = length form := by
  cases form <;> rfl

theorem relocate_result (form : Form) (d old : Dword) (cf : Bool) :
    result (relocate form d) old cf = result form old cf := by cases form <;> rfl

theorem relocate_flag (form : Form) (d old : Dword) (cf : Bool) :
    flag (relocate form d) old cf = flag form old cf := by cases form <;> rfl

theorem located_next (mode : Mode) (form : Form) (pc target : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc) :
    next mode (located mode form pc target) state = Arithmetic.encodeNat mode (pc+length form) := by
  rw [next,location]
  simp only [located,relocate_length]
  exact BitVec.ofNat_add_ofNat pc (length form)

theorem located_address (mode : Mode) (form : Form) (pc target : Nat) (state : Execution.State mode)
    (relative : direct form = true) (location : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+length form) target) :
    address mode (located mode form pc target) state = Arithmetic.encodeNat mode target := by
  have next := located_next mode form pc target state location
  cases form <;> simp only [direct] at relative
  all_goals try cases relative
  all_goals change Execution.memoryAddress mode _ _ = _
  all_goals rw [next]
  all_goals exact Relocation.memory_hits mode _ _ range

theorem located_effect (mode : Mode) (form : Form) (pc target : Nat) (state : Execution.State mode)
    (relative : direct form = true) (location : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+length form) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    execute mode (located mode form pc target) state =
      { state with
        pc := Arithmetic.encodeNat mode (pc+length form)
        carry := flag form (get state.memory target) state.carry
        memory := put state.memory target (result form (get state.memory target) state.carry) } := by
  unfold execute value carry prior
  rw [located_address mode form pc target state relative location range,
      Arithmetic.encode_nat_toNat mode target fits,located_next mode form pc target state location]
  simp only [located,relocate_result,relocate_flag]

theorem write_nonempty (mode : Mode) (form : Form) (state : Execution.State mode) :
    ByteMemory.Inside (address mode form state).toNat 4 (address mode form state).toNat := by
  unfold ByteMemory.Inside
  omega

@[expose] def OwnedRun (mode : Mode) (owned : Nat → Prop) : List Form → Execution.State mode → Prop
  | [], _ => True
  | form::forms, state => owned (address mode form state).toNat ∧ OwnedRun mode owned forms (execute mode form state)

end SmcTuring.Native.DwordArithmetic
