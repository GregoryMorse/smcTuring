module
public import SmcTuring.Native.WordNegation

public section
namespace SmcTuring.Native.WordAddImmediate
open LittleEndian
/-- Full-width ADD r/m, signed imm8: the actual Listing 4 stack adjustment. -/
@[expose] def encode (mode : Mode) (d : BitVec 32) (value : Byte) : List Byte :=
  wordPrefix mode ++ [0x83,0x05] ++ wordEncode 4 d ++ [value]
@[expose] def length (mode : Mode) := (wordPrefix mode).length+7
@[expose] def payload (bytes : List Byte) : Option (BitVec 32 × Byte) := do
  let d ← wordDecode 4 (bytes.take 4)
  match bytes.drop 4 with | [value] => some (d,value) | _ => none
@[expose] def decode (mode : Mode) : List Byte → Option (BitVec 32 × Byte) :=
  match mode with
  | .x86 => fun bytes => match bytes with | 0x83::0x05::rest => payload rest | _ => none
  | .x64 => fun bytes => match bytes with | 0x48::0x83::0x05::rest => payload rest | _ => none
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) :=
  decode mode (ByteMemory.bytesAt memory pc (length mode))
@[expose] def next (mode : Mode) (state : Execution.State mode) := state.pc+Arithmetic.encodeNat mode (length mode)
@[expose] def address (mode : Mode) (d : BitVec 32) (state : Execution.State mode) :=
  Execution.memoryAddress mode (next mode state) d
@[expose] def immediate (mode : Mode) (value : Byte) : Word mode := value.signExtend (8*mode.wordBytes)
@[expose] def execute (mode : Mode) (d : BitVec 32) (value : Byte) (state : Execution.State mode) :=
  let target := address mode d state
  let old := Execution.load mode state.memory target
  Execution.storeState mode state (next mode state) target (old+immediate mode value)
    (BitVec.uaddOverflow old (immediate mode value))

theorem encode_length (mode : Mode) (d : BitVec 32) (value : Byte) : (encode mode d value).length = length mode := by
  cases mode <;> simp [encode,length,wordPrefix]

theorem roundtrip (mode : Mode) (d : BitVec 32) (value : Byte) : decode mode (encode mode d value) = some (d,value) := by
  cases mode <;> simp [decode,encode,payload,wordPrefix,word_decode_encode]

theorem fetch_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32) (value : Byte)
    (current : ByteMemory.bytesAt memory pc (encode mode d value).length = encode mode d value) :
    fetch mode memory pc = some (d,value) := by
  rw [fetch,←encode_length mode d value,current,roundtrip]

theorem located_effect (mode : Mode) (pc target : Nat) (value : Byte) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+length mode) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    execute mode (Relocation.memoryDisp mode (pc+length mode) target) value state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+length mode)
        carry := BitVec.uaddOverflow (MixedMemory.getWord mode state.memory target) (immediate mode value)
        memory := ByteMemory.putWord mode state.memory target
          (MixedMemory.getWord mode state.memory target+immediate mode value)} := by
  have step : next mode state = Arithmetic.encodeNat mode (pc+length mode) := by
    rw [next,entry];exact BitVec.ofNat_add_ofNat pc (length mode)
  have hit : address mode (Relocation.memoryDisp mode (pc+length mode) target) state = Arithmetic.encodeNat mode target := by
    rw [address,step];exact Relocation.memory_hits mode _ _ range
  rw [execute,hit,MixedMemory.load_nat mode state.memory target fits,step,Execution.storeState,
    Arithmetic.encode_nat_toNat mode target fits]

theorem positive_four (mode : Mode) : immediate mode 4 = Arithmetic.encodeNat mode 4 := by cases mode <;> rfl
theorem positive_eighteen (mode : Mode) : immediate mode 18 = Arithmetic.encodeNat mode 18 := by cases mode <;> rfl
end SmcTuring.Native.WordAddImmediate
