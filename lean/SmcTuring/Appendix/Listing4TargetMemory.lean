module
public import SmcTuring.Appendix.Listing4TargetLayout

public section
namespace SmcTuring.Appendix.Listing4TargetMemory
open Native LittleEndian Listing4StackLayout
theorem original_return (mode : Mode) (start : Nat) (memory : ByteMemory.Memory)
    (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    MixedMemory.getWord mode memory (returnField mode start)=Arithmetic.encodeNat mode (stptr mode start) := by
  cases mode with
  | x64 => exact initial_svptr start memory fits current
  | x86 =>
    let address : BitVec 32 := Arithmetic.encodeNat .x86 (stptr .x86 start)
    have code : ByteMemory.bytesAt memory start ([0xc7,0x05]++wordEncode 4 address++wordEncode 4 address).length =
        [0xc7,0x05]++wordEncode 4 address++wordEncode 4 address := current
    have payload := ByteWindow.packet memory start [0xc7,0x05] (wordEncode 4 address) (wordEncode 4 address) code
    have fieldFits : returnField .x86 start<2^32 := by change start+10<2^32 at fits;dsimp [returnField];omega
    rw [←MixedMemory.load_nat .x86 memory _ fieldFits]
    exact StringWindow.initial_word .x86 memory _ address fieldFits payload

theorem restore_return (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) (ret acc : Word mode)
    (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    ByteMemory.putWord mode
      (ByteMemory.putWord mode (ByteMemory.putWord mode memory (returnField mode start) ret) (stptr mode start) acc)
      (returnField mode start) (Arithmetic.encodeNat mode (stptr mode start)) =
      ByteMemory.putWord mode memory (stptr mode start) acc := by
  rw [MixedFrames.words_commute mode _ (stptr mode start) (returnField mode start) _ _ (Or.symm (fields_separate mode start)),
    Writes.put_word_overwrite]
  have back : ByteMemory.putWord mode memory (returnField mode start) (Arithmetic.encodeNat mode (stptr mode start))=memory := by
    rw [←original_return mode start memory fits current,MixedMemory.put_get_back]
  rw [back]
end SmcTuring.Appendix.Listing4TargetMemory
