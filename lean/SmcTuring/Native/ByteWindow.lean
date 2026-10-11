module
public import SmcTuring.Native.Fetch

public section
namespace SmcTuring.Native.ByteWindow
open LittleEndian
theorem drop (memory : ByteMemory.Memory) (pc count offset : Nat) :
    (ByteMemory.bytesAt memory pc (offset+count)).drop offset =
      ByteMemory.bytesAt memory (pc+offset) count := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp [ByteMemory.bytesAt,Nat.add_comm,Nat.add_left_comm]

theorem packet (memory : ByteMemory.Memory) (start : Nat) (leading body trailing : List Byte)
    (current : ByteMemory.bytesAt memory start (leading++body++trailing).length = leading++body++trailing) :
    ByteMemory.bytesAt memory (start+leading.length) body.length = body := by
  have taken := Fetch.bytes_at_take memory start (leading++body++trailing).length
    (leading.length+body.length) (by simp)
  rw [current] at taken
  have trimmed : (leading++body++trailing).take (leading.length+body.length) = leading++body := by
    rw [←List.length_append,List.take_append_length]
  rw [trimmed] at taken
  have dropped := congrArg (List.drop leading.length) taken
  rw [drop] at dropped
  simpa only [List.drop_append_length] using dropped.symm
theorem append (memory : ByteMemory.Memory) (start first second : Nat) :
    ByteMemory.bytesAt memory start (first+second) =
      ByteMemory.bytesAt memory start first ++ ByteMemory.bytesAt memory (start+first) second := by
  apply List.ext_getElem
  · simp only [ByteMemory.bytes_at_length,List.length_append]
  · intro index leftBound rightBound
    by_cases before : index < first
    · rw [List.getElem_append_left (by simpa only [ByteMemory.bytes_at_length] using before)]
      simp only [ByteMemory.bytesAt,List.getElem_ofFn]
    · have later : (ByteMemory.bytesAt memory start first).length ≤ index := by
        simpa only [ByteMemory.bytes_at_length] using Nat.le_of_not_gt before
      rw [List.getElem_append_right later]
      simp only [ByteMemory.bytesAt,List.getElem_ofFn,List.length_ofFn]
      congr 1
      omega

/-- Adjacent current windows determine their complete concatenated image. -/
theorem join (memory : ByteMemory.Memory) (start : Nat) (leading trailing : List Byte)
    (first : ByteMemory.bytesAt memory start leading.length = leading)
    (second : ByteMemory.bytesAt memory (start+leading.length) trailing.length = trailing) :
    ByteMemory.bytesAt memory start (leading++trailing).length = leading++trailing := by
  rw [List.length_append,append,first,second]

end SmcTuring.Native.ByteWindow
