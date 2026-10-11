module
public import SmcTuring.Native.DecodeImage

public section
namespace SmcTuring.Native.DwordXor
abbrev Dword := BitVec 32
@[expose] def encode (displacement : Dword) : List LittleEndian.Byte :=
  [0x31,0x05] ++ LittleEndian.wordEncode 4 displacement
@[expose] def decode (mode : Mode) (bytes : List LittleEndian.Byte) : Option Dword :=
  (Native.decodeCore mode bytes).bind fun form => match form with
    | .memory .bitXor displacement => some displacement
    | _ => none
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) :=
  decode mode (ByteMemory.bytesAt memory pc 6)
@[expose] def next (mode : Mode) (state : Execution.State mode) := state.pc+Arithmetic.encodeNat mode 6
@[expose] def address (mode : Mode) (displacement : Dword) (state : Execution.State mode) :=
  Execution.memoryAddress mode (next mode state) displacement
@[expose] def execute (mode : Mode) (displacement : Dword) (state : Execution.State mode) :=
  { state with
    pc := next mode state
    carry := false
    memory := DwordCode.put state.memory (address mode displacement state).toNat
      (DwordCode.get state.memory (address mode displacement state).toNat ^^^ DwordCode.low mode state.accumulator)}

theorem roundtrip (mode : Mode) (displacement : Dword) : decode mode (encode displacement) = some displacement := by
  have taken : (LittleEndian.wordEncode 4 displacement).take 4 = LittleEndian.wordEncode 4 displacement := rfl
  simp [decode,encode,Native.decodeCore,Native.operationOfTag,Native.decodeMemoryPayload,MemoryOp.trailer,taken]

theorem decode_image (mode : Mode) (bytes : List LittleEndian.Byte) (displacement : Dword)
    (decoded : decode mode bytes = some displacement) : bytes = encode displacement := by
  unfold decode at decoded
  rcases Option.bind_eq_some_iff.mp decoded with ⟨form,parsed,decoded⟩
  have image := (DecodeImage.core mode bytes form parsed).1
  cases form with
  | moffs address => cases decoded
  | memory operation d =>
    cases operation <;> simp only at decoded <;> cases decoded
    exact image
  | exchangeIndirect => cases decoded
  | callRelative d => cases decoded

theorem fetch_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (displacement : Dword)
    (current : ByteMemory.bytesAt memory pc 6 = encode displacement) :
    fetch mode memory pc = some displacement := by rw [fetch,current,roundtrip]

theorem fetch_image (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (displacement : Dword)
    (current : fetch mode memory pc = some displacement) : ByteMemory.bytesAt memory pc 6 = encode displacement :=
  decode_image mode _ displacement current

theorem located_effect (mode : Mode) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+6) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    execute mode (Relocation.memoryDisp mode (pc+6) target) state =
      { state with
        pc := Arithmetic.encodeNat mode (pc+6)
        carry := false
        memory := DwordCode.put state.memory target (DwordCode.get state.memory target ^^^ DwordCode.low mode state.accumulator)} := by
  have step : next mode state = Arithmetic.encodeNat mode (pc+6) := by
    rw [next,entry];exact BitVec.ofNat_add_ofNat pc 6
  have hit : address mode (Relocation.memoryDisp mode (pc+6) target) state = Arithmetic.encodeNat mode target := by
    rw [address,step];exact Relocation.memory_hits mode _ _ range
  rw [execute,hit,Arithmetic.encode_nat_toNat mode target fits,step]

theorem native_x86 (displacement : Dword) (state : Execution.State .x86) :
    execute .x86 displacement state = Execution.execute .x86 (.memory .bitXor displacement) state := by
  have low : DwordCode.low .x86 state.accumulator = state.accumulator := by
    change BitVec.ofNat 32 state.accumulator.toNat = state.accumulator
    exact BitVec.ofNat_toNat 32 state.accumulator
  simp [execute,address,next,Execution.execute,Execution.executeMemory,Execution.storeState,Execution.nextPC,
    Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes,low,
    DwordCode.get,DwordCode.put,ByteMemory.putWord,Execution.load,Execution.memoryAddress] <;> rfl

theorem frame (mode : Mode) (displacement : Dword) (state : Execution.State mode) (observed : Nat)
    (outside : ¬ByteMemory.Inside (address mode displacement state).toNat 4 observed) :
    (execute mode displacement state).memory observed = state.memory observed :=
  ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)

theorem registers (mode : Mode) (displacement : Dword) (state : Execution.State mode) :
    (execute mode displacement state).accumulator = state.accumulator ∧
    (execute mode displacement state).stack = state.stack ∧ (execute mode displacement state).carry = false := ⟨rfl,rfl,rfl⟩

end SmcTuring.Native.DwordXor
