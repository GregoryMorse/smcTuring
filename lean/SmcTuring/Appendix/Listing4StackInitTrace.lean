module
public import SmcTuring.Appendix.Listing4StackInit

public section
namespace SmcTuring.Appendix.Listing4StackInitTrace
open Native LittleEndian Listing4StackLayout Listing4StackInit
/-- Actual DEFSTACK fetches, including the temporarily overwritten future
MOFFS operand. Its restoration is proved before either MOFFS is fetched. -/
theorem trace (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : start+size mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = bytes mode start) :
    StringStack.Trace mode state (forms mode start) (finish mode start state) := by
  have startFits : start < 2^(8*mode.wordBytes) := by omega
  cases mode with
  | x86 =>
    have fetched := StringForm.fetch_current_encoding .x86 state.principal.memory start
      (.initialize32 (Arithmetic.encodeNat .x86 (stptr .x86 start)) (Arithmetic.encodeNat .x86 (stptr .x86 start))) rfl current
    have full := StringStack.previous_fetch .x86 _ _ _ (StringControl.previous_fetch .x86 _ _ _ (StringDword.string_fetch .x86 _ _ _ fetched))
    exact .step (by rw [entry,Arithmetic.encode_nat_toNat .x86 start startFits];exact full) (.nil _)
  | x64 =>
    let a := Native.encode .x64 (first start)
    let b := Native.encode .x64 (second start)
    let c := Native.encode .x64 (third start)
    let d := Native.encode .x64 (fourth start)
    have code : ByteMemory.bytesAt state.principal.memory start (a++b++c++d).length = a++b++c++d := current
    have firstPacket : ByteMemory.bytesAt state.principal.memory start a.length = a := by
      have packet := ByteWindow.packet state.principal.memory start [] a (b++c++d)
        (by simpa only [List.nil_append,List.append_assoc] using code)
      exact packet
    have secondPacket : ByteMemory.bytesAt state.principal.memory (start+7) b.length = b := by
      exact ByteWindow.packet state.principal.memory start a b (c++d) (by simpa only [List.append_assoc] using code)
    have thirdPacket : ByteMemory.bytesAt state.principal.memory (start+14) c.length = c := by
      exact ByteWindow.packet state.principal.memory start (a++b) c d code
    have fourthPacket : ByteMemory.bytesAt state.principal.memory (start+24) d.length = d := by
      exact ByteWindow.packet state.principal.memory start (a++b++c) d [] (by simpa only [List.append_nil] using code)
    have firstEffect := swapped_effect start state entry fits current
    have secondEffect := restored_effect start state entry fits current
    have thirdEffect := stored_effect start state entry fits current
    have pc1 : (swapped start state).principal.pc = Arithmetic.encodeNat .x64 (start+7) := by rw [firstEffect]
    have pc2 : (restored start state).principal.pc = Arithmetic.encodeNat .x64 (start+14) := by rw [secondEffect]
    have pc3 : (stored start state).principal.pc = Arithmetic.encodeNat .x64 (start+24) := by rw [thirdEffect]
    have mem2 : (restored start state).principal.memory = state.principal.memory := by rw [secondEffect]
    have mem3 : (stored start state).principal.memory = state.principal.memory := by rw [thirdEffect]
    have fetched : StringStack.fetch .x64 state.principal.memory state.principal.pc.toNat = some (StringStack.native .x64 (first start)) := by
      rw [entry,Arithmetic.encode_nat_toNat .x64 start startFits]
      exact StringStack.native_encoding .x64 _ _ _ firstPacket
    have fetched2 : StringStack.fetch .x64 (swapped start state).principal.memory (swapped start state).principal.pc.toNat =
        some (StringStack.native .x64 (second start)) := by
      rw [pc1,Arithmetic.encode_nat_toNat .x64 (start+7) (by change start+7<2^64;change start+34<2^64 at fits;omega)]
      apply StringStack.native_encoding .x64
      rw [firstEffect]
      change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory (start+16)
        (wordEncode 8 state.principal.accumulator)) (start+7) 7 = b
      rw [ByteMemory.bytes_at_frame state.principal.memory (start+16) (wordEncode 8 state.principal.accumulator) (start+7) 7 (by
        intro index;have bound:=index.isLt
        change ¬ByteMemory.Inside (start+16) 8 (start+7+index.val)
        unfold ByteMemory.Inside;omega)]
      exact secondPacket
    have fetched3 : StringStack.fetch .x64 (restored start state).principal.memory (restored start state).principal.pc.toNat =
        some (StringStack.native .x64 (third start)) := by
      rw [pc2,Arithmetic.encode_nat_toNat .x64 (start+14) (by change start+14<2^64;change start+34<2^64 at fits;omega),mem2]
      exact StringStack.native_encoding .x64 _ _ _ thirdPacket
    have fetched4 : StringStack.fetch .x64 (stored start state).principal.memory (stored start state).principal.pc.toNat =
        some (StringStack.native .x64 (fourth start)) := by
      rw [pc3,Arithmetic.encode_nat_toNat .x64 (start+24) (by change start+24<2^64;change start+34<2^64 at fits;omega),mem3]
      exact StringStack.native_encoding .x64 _ _ _ fourthPacket
    exact .step fetched (.step fetched2 (.step fetched3 (.step fetched4 (.nil _))))

theorem initialized_trace (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+size mode < 2^(8*mode.wordBytes)) :
    let initial := {seed with principal := {seed.principal with
      pc := Arithmetic.encodeNat mode start
      memory := ByteMemory.putBytes seed.principal.memory start (bytes mode start)}}
    StringStack.Trace mode initial (forms mode start) (finish mode start initial) := by
  apply trace mode start _ rfl fits
  simpa only [bytes_length] using ByteMemory.bytes_at_put seed.principal.memory start (bytes mode start)
end SmcTuring.Appendix.Listing4StackInitTrace
