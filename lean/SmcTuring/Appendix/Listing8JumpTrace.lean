module
public import SmcTuring.Appendix.Listing8JumpEffects
public import SmcTuring.Native.StackWindows

public section
namespace SmcTuring.Appendix.Listing8JumpTrace
open Native LittleEndian Listing4StackLayout Listing8JumpLayout Listing8JumpEffects
/-- Every later prefix and conditional CALL fetch follows from the current
entry packets and the actual preceding stack writes. -/
theorem trace (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (stackCurrent : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin)
    (jumpCurrent : ByteMemory.bytesAt state.principal.memory (jumpPC mode origin) (prefixBytes mode origin).length=prefixBytes mode origin)
    (callCurrent : ByteMemory.bytesAt state.principal.memory (callPC mode origin) 5=Native.encode mode (call mode origin failed)) :
    StringStack.Trace mode state (forms mode origin failed) (finish mode origin failed state) := by
  have firstEffect:=exchanged_effect mode origin state entry capacity stackCurrent
  have lastEffect:=prefix_effect mode origin state entry capacity stackCurrent
  have stackBefore:=(slots_before mode origin).1
  have savedBefore:=(slots_before mode origin).2
  have jumpFits : jumpPC mode origin<2^(8*mode.wordBytes) := by dsimp [failPC,callPC] at capacity;omega
  have callFits : callPC mode origin<2^(8*mode.wordBytes) := by dsimp [failPC] at capacity;omega
  have callPosition : (prefixEnd mode origin state).principal.pc=Arithmetic.encodeNat mode (callPC mode origin) := by rw [lastEffect]
  have callFetched : StringStack.fetch mode (prefixEnd mode origin state).principal.memory (prefixEnd mode origin state).principal.pc.toNat=
      some (StringStack.native mode (call mode origin failed)) := by
    rw [callPosition,Arithmetic.encode_nat_toNat mode _ callFits]
    apply StringStack.native_encoding mode
    rw [lastEffect,StackWindows.word_window mode state.principal.memory (stptr mode origin) (callPC mode origin) _ _
      (Or.inl (by dsimp [callPC];omega))]
    simpa only [show (Native.encode mode (call mode origin failed)).length=5 by cases mode <;> rfl] using callCurrent
  cases mode with
  | x86 =>
    have fetched : StringStack.fetch .x86 state.principal.memory state.principal.pc.toNat=
        some (StringStack.native .x86 (exchange .x86 origin)) := by
      rw [entry,Arithmetic.encode_nat_toNat .x86 _ jumpFits]
      exact StringStack.native_encoding .x86 _ _ _ jumpCurrent
    exact .step fetched (.step callFetched (.nil _))
  | x64 =>
    let a:=Native.encode .x64 (exchange .x64 origin)
    let b:=WordAddImmediate.encode .x64 (Relocation.memoryDisp .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)) 18
    let c:=Native.encode .x64 (exchangeSaved origin)
    have code : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 origin) (a++b++c).length=a++b++c := jumpCurrent
    have aPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 origin) a.length=a := by
      exact ByteWindow.packet state.principal.memory (jumpPC .x64 origin) [] a (b++c) (by simpa only [List.nil_append,List.append_assoc] using code)
    have bPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 origin+7) b.length=b := by
      exact ByteWindow.packet state.principal.memory (jumpPC .x64 origin) a b c code
    have cPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 origin+7+8) c.length=c := by
      have packet:=ByteWindow.packet state.principal.memory (jumpPC .x64 origin) (a++b) c [] (by simpa only [List.append_nil] using code)
      simpa only [show (a++b).length=7+8 from rfl,Nat.add_assoc] using packet
    have pc1 : (exchanged .x64 origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7) := by rw [firstEffect];rfl
    have secondEffect:=adjusted_effect origin state entry capacity stackCurrent
    have pc2 : (adjusted origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8) := by rw [secondEffect]
    have fetched : StringStack.fetch .x64 state.principal.memory state.principal.pc.toNat=
        some (StringStack.native .x64 (exchange .x64 origin)) := by
      rw [entry,Arithmetic.encode_nat_toNat .x64 _ jumpFits]
      exact StringStack.native_encoding .x64 _ _ _ aPacket
    have fetched2 : StringStack.fetch .x64 (exchanged .x64 origin state).principal.memory (exchanged .x64 origin state).principal.pc.toNat=some (adjust origin) := by
      have small : jumpPC .x64 origin+7<2^64 := by
        change failPC .x64 origin<2^64 at capacity
        dsimp [failPC,callPC,Listing4JumpLayout.prefixSize] at capacity;omega
      rw [pc1,Arithmetic.encode_nat_toNat .x64 _ small]
      apply StringStack.add_encoding .x64
      rw [firstEffect,StackWindows.word_window .x64 _ (stptr .x64 origin) (jumpPC .x64 origin+7) _ _ (Or.inl (by omega))]
      exact bPacket
    have fetched3 : StringStack.fetch .x64 (adjusted origin state).principal.memory (adjusted origin state).principal.pc.toNat=
        some (StringStack.native .x64 (exchangeSaved origin)) := by
      have small : jumpPC .x64 origin+7+8<2^64 := by
        change failPC .x64 origin<2^64 at capacity
        dsimp [failPC,callPC,Listing4JumpLayout.prefixSize] at capacity;omega
      rw [pc2,Arithmetic.encode_nat_toNat .x64 _ small]
      apply StringStack.native_encoding .x64
      rw [secondEffect,StackWindows.word_window .x64 _ (returnField .x64 origin) (jumpPC .x64 origin+7+8) _ _ (Or.inl (by omega)),
        StackWindows.word_window .x64 _ (stptr .x64 origin) (jumpPC .x64 origin+7+8) _ _ (Or.inl (by omega))]
      exact cPacket
    exact .step fetched (.step fetched2 (.step fetched3 (.step callFetched (.nil _))))
end SmcTuring.Appendix.Listing8JumpTrace
