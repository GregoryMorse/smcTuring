module
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.WordNegation
open LittleEndian
@[expose] def encode (mode : Mode) (d : BitVec 32) : List Byte :=
  wordPrefix mode ++ [0xf7,0x1d] ++ wordEncode 4 d
@[expose] def length (mode : Mode) := (wordPrefix mode).length+6
@[expose] def decode (mode : Mode) : List Byte → Option (BitVec 32) :=
  match mode with
  | .x86 => fun bytes => match bytes with | 0xf7::0x1d::payload => wordDecode 4 payload | _ => none
  | .x64 => fun bytes => match bytes with | 0x48::0xf7::0x1d::payload => wordDecode 4 payload | _ => none
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) :=
  decode mode (ByteMemory.bytesAt memory pc (length mode))
@[expose] def next (mode : Mode) (state : Execution.State mode) := state.pc+Arithmetic.encodeNat mode (length mode)
@[expose] def address (mode : Mode) (d : BitVec 32) (state : Execution.State mode) :=
  Execution.memoryAddress mode (next mode state) d
@[expose] def execute (mode : Mode) (d : BitVec 32) (state : Execution.State mode) :=
  let target := address mode d state
  let old := Execution.load mode state.memory target
  {state with
    pc := next mode state
    carry := decide (old ≠ 0)
    memory := ByteMemory.putWord mode state.memory target.toNat (-old)}

theorem encode_length (mode : Mode) (d : BitVec 32) : (encode mode d).length = length mode := by
  cases mode <;> rfl

theorem roundtrip (mode : Mode) (d : BitVec 32) : decode mode (encode mode d) = some d := by
  cases mode <;> simp [decode,encode,wordPrefix,word_decode_encode]

theorem fetch_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32)
    (current : ByteMemory.bytesAt memory pc (encode mode d).length = encode mode d) :
    fetch mode memory pc = some d := by
  rw [fetch,←encode_length mode d,current,roundtrip]

theorem located_effect (mode : Mode) (pc target : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+length mode) target)
    (fits : target < 2^(8*mode.wordBytes)) :
    execute mode (Relocation.memoryDisp mode (pc+length mode) target) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+length mode)
        carry := decide (MixedMemory.getWord mode state.memory target ≠ 0)
        memory := ByteMemory.putWord mode state.memory target (-MixedMemory.getWord mode state.memory target)} := by
  have step : next mode state = Arithmetic.encodeNat mode (pc+length mode) := by
    rw [next,entry];exact BitVec.ofNat_add_ofNat pc (length mode)
  have hit : address mode (Relocation.memoryDisp mode (pc+length mode) target) state = Arithmetic.encodeNat mode target := by
    rw [address,step];exact Relocation.memory_hits mode _ _ range
  rw [execute,hit,MixedMemory.load_nat mode state.memory target fits,step,Arithmetic.encode_nat_toNat mode target fits]

end SmcTuring.Native.WordNegation
