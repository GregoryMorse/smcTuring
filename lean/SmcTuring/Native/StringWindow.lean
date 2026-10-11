module
public import SmcTuring.Native.StringOperands

public section
namespace SmcTuring.Native.StringWindow
open LittleEndian ByteMemory

theorem bytes_at_slice (memory : Memory) (start total offset count : Nat) (within : offset+count ≤ total) :
    ((bytesAt memory start total).drop offset).take count = bytesAt memory (start+offset) count := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,bytes_at_length]
    omega
  · intro index left right
    simp [bytesAt,Nat.add_comm,Nat.add_left_comm]

theorem packet_window (memory : Memory) (start : Nat) (leading packet trailing : List Byte)
    (current : bytesAt memory start (leading++packet++trailing).length = leading++packet++trailing) :
    bytesAt memory (start+leading.length) packet.length = packet := by
  rw [←bytes_at_slice memory start (leading++packet++trailing).length leading.length packet.length (by simp)]
  rw [current]
  simp

theorem initial_word (mode : Mode) (memory : Memory) (field : Nat) (value : Word mode)
    (fits : field < 2^(8*mode.wordBytes))
    (current : bytesAt memory field mode.wordBytes = wordEncode mode.wordBytes value) :
    Execution.load mode memory (Arithmetic.encodeNat mode field) = value := by
  have total := Execution.read_word_total mode memory (Arithmetic.encodeNat mode field)
  unfold readWord at total
  rw [Arithmetic.encode_nat_toNat mode field fits,current,word_decode_encode] at total
  exact (Option.some.inj total).symm

/-- Full-word frame at natural field coordinates, including unaligned fields. -/
theorem load_frame (mode : Mode) (memory : Memory) (written observed : Nat) (value : Word mode)
    (fits : observed < 2^(8*mode.wordBytes))
    (separate : ∀ index : Fin mode.wordBytes, ¬Inside written mode.wordBytes (observed+index.val)) :
    Execution.load mode (putWord mode memory written value) (Arithmetic.encodeNat mode observed) =
      Execution.load mode memory (Arithmetic.encodeNat mode observed) := by
  unfold Execution.load
  rw [Arithmetic.encode_nat_toNat mode observed fits]
  apply congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (pack bytes))
  exact bytes_at_frame memory written (wordEncode mode.wordBytes value) observed mode.wordBytes (by simpa only [word_encode_length] using separate)

end SmcTuring.Native.StringWindow
