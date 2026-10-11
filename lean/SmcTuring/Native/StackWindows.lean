module
public import SmcTuring.Native.StackMemory

public section
namespace SmcTuring.Native.StackWindows
theorem word_window (mode : Mode) (memory : ByteMemory.Memory) (written observed count : Nat) (value : Word mode)
    (separate : written+mode.wordBytes ≤ observed ∨ observed+count ≤ written) :
    ByteMemory.bytesAt (ByteMemory.putWord mode memory written value) observed count = ByteMemory.bytesAt memory observed count := by
  have length : (LittleEndian.wordEncode mode.wordBytes value).length = mode.wordBytes := by cases mode <;> rfl
  apply ByteMemory.bytes_at_frame
  intro index;have bound:=index.isLt
  rw [length]
  change ¬ByteMemory.Inside written mode.wordBytes (observed+index.val)
  unfold ByteMemory.Inside
  rcases separate with before | after <;> omega
end SmcTuring.Native.StackWindows
