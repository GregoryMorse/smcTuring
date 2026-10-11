module
public import SmcTuring.Appendix.Listing4TargetEffects

public section
namespace SmcTuring.Appendix.Listing4TargetTrace
open Native Listing4StackLayout Listing4TargetLayout Listing4TargetEffects
theorem windows (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start)
    (placement : start+Listing4StackLayout.size mode ≤ target) (observed count : Nat) (later : target ≤ observed) :
    ByteMemory.bytesAt (entry mode start target ret seed).principal.memory observed count=ByteMemory.bytesAt seed.principal.memory observed count ∧
    ByteMemory.bytesAt (swapped mode start target ret seed).principal.memory observed count=ByteMemory.bytesAt seed.principal.memory observed count ∧
    ByteMemory.bytesAt (adjusted mode start target ret seed).principal.memory observed count=ByteMemory.bytesAt seed.principal.memory observed count ∧
    ByteMemory.bytesAt (exchanged mode start target ret seed).principal.memory observed count=ByteMemory.bytesAt seed.principal.memory observed count ∧
    ByteMemory.bytesAt (stored mode start target ret seed).principal.memory observed count=ByteMemory.bytesAt seed.principal.memory observed count := by
  have stBefore : stptr mode start+mode.wordBytes ≤ observed :=
    Nat.le_trans (stptr_fits mode start fits) (Nat.le_trans placement later)
  have returnBefore : returnField mode start+mode.wordBytes ≤ observed := by
    have before := Listing4Boot.return_before_jump mode start
    change returnField mode start+mode.wordBytes ≤ start+Listing4StackLayout.size mode at before
    exact Nat.le_trans before (Nat.le_trans placement later)
  have frame (left right : Word mode) : ByteMemory.bytesAt
      (ByteMemory.putWord mode (ByteMemory.putWord mode seed.principal.memory (returnField mode start) left) (stptr mode start) right)
      observed count=ByteMemory.bytesAt seed.principal.memory observed count := by
    rw [StackWindows.word_window mode _ _ _ _ _ (Or.inl stBefore),StackWindows.word_window mode _ _ _ _ _ (Or.inl returnBefore)]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact frame ret seed.principal.stack
  · rw [swapped_effect mode start target ret seed ranges fits];exact frame ret _
  · rw [adjusted_effect mode start target ret seed ranges fits];exact frame ret _
  · rw [exchanged_effect mode start target ret seed ranges fits];exact frame ret _
  · rw [stored_effect mode start target ret seed ranges fits current]
    exact StackWindows.word_window mode _ _ _ _ _ (Or.inl stBefore)

/-- Five actual target packets consume the computed CALL-result shape. The
CALL-to-target composition derives this shape and these original byte windows. -/
theorem trace (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (fits : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (targetFits : target+Listing4TargetLayout.size mode<2^(8*mode.wordBytes))
    (stackCurrent : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start)
    (placement : start+Listing4StackLayout.size mode ≤ target)
    (current : ByteMemory.bytesAt seed.principal.memory target (Listing4TargetLayout.size mode)=Listing4TargetLayout.bytes mode start target) :
    StringStack.Trace mode (entry mode start target ret seed) (Listing4TargetLayout.forms mode start target) (finish mode start target ret seed) := by
  let a := Native.encode mode (first mode start target)
  let b := adjustBytes mode start target
  let c := Native.encode mode (third mode start target)
  let d := Native.encode mode (fourth mode start target)
  let e := Native.encode mode (fifth mode start target)
  have code : ByteMemory.bytesAt seed.principal.memory target (a++b++c++d++e).length=a++b++c++d++e := by
    change ByteMemory.bytesAt seed.principal.memory target (Listing4TargetLayout.bytes mode start target).length=_
    rw [Listing4TargetLayout.bytes_length];exact current
  have aPacket : ByteMemory.bytesAt seed.principal.memory target a.length=a := by
    exact ByteWindow.packet seed.principal.memory target [] a (b++c++d++e) (by simpa only [List.nil_append,List.append_assoc] using code)
  have bPacket : ByteMemory.bytesAt seed.principal.memory (target+StackMemory.size mode) b.length=b := by
    have packet := ByteWindow.packet seed.principal.memory target a b (c++d++e) (by simpa only [List.append_assoc] using code)
    simpa only [a,first_length] using packet
  have cPacket : ByteMemory.bytesAt seed.principal.memory (thirdPC mode target) c.length=c := by
    have packet := ByteWindow.packet seed.principal.memory target (a++b) c (d++e) (by simpa only [List.append_assoc] using code)
    simpa only [a,b,List.length_append,first_length,adjust_length,thirdPC,Nat.add_assoc] using packet
  have dPacket : ByteMemory.bytesAt seed.principal.memory (fourthPC mode target) d.length=d := by
    have packet := ByteWindow.packet seed.principal.memory target (a++b++c) d e code
    simpa only [a,b,c,List.length_append,first_length,adjust_length,third_length,thirdPC,fourthPC,Nat.add_assoc] using packet
  have ePacket : ByteMemory.bytesAt seed.principal.memory (fifthPC mode target) e.length=e := by
    have packet := ByteWindow.packet seed.principal.memory target (a++b++c++d) e [] (by simpa only [List.append_nil] using code)
    simpa only [a,b,c,d,List.length_append,first_length,adjust_length,third_length,fourth_length,thirdPC,fourthPC,fifthPC,Nat.add_assoc] using packet
  have p1 : (entry mode start target ret seed).principal.pc=Arithmetic.encodeNat mode target := rfl
  have p2 : (swapped mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (target+StackMemory.size mode) := by rw [swapped_effect mode start target ret seed ranges fits]
  have p3 : (adjusted mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (thirdPC mode target) := by rw [adjusted_effect mode start target ret seed ranges fits]
  have p4 : (exchanged mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fourthPC mode target) := by rw [exchanged_effect mode start target ret seed ranges fits]
  have p5 : (stored mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fifthPC mode target) := by rw [stored_effect mode start target ret seed ranges fits stackCurrent]
  have bound : target+StackMemory.size mode<2^(8*mode.wordBytes) ∧ thirdPC mode target<2^(8*mode.wordBytes) ∧
      fourthPC mode target<2^(8*mode.wordBytes) ∧ fifthPC mode target<2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [StackMemory.size,wordPrefix,thirdPC,fourthPC,fifthPC,adjustSize,WordAddImmediate.length,Listing4TargetLayout.size] at * <;> omega
  have fetch1 : StringStack.fetch mode (entry mode start target ret seed).principal.memory (entry mode start target ret seed).principal.pc.toNat=
      some (StringStack.native mode (first mode start target)) := by
    rw [p1,Arithmetic.encode_nat_toNat mode target (by omega)]
    apply StringStack.native_encoding mode
    rw [(windows mode start target ret seed ranges fits stackCurrent placement target a.length (Nat.le_refl _)).1]
    exact aPacket
  have fetch2 : StringStack.fetch mode (swapped mode start target ret seed).principal.memory (swapped mode start target ret seed).principal.pc.toNat=
      some (adjust mode start target) := by
    rw [p2,Arithmetic.encode_nat_toNat mode _ bound.1]
    have kept := (windows mode start target ret seed ranges fits stackCurrent placement (target+StackMemory.size mode) b.length (by omega)).2.1
    have packet : ByteMemory.bytesAt (swapped mode start target ret seed).principal.memory (target+StackMemory.size mode) b.length=b := by rw [kept];exact bPacket
    cases mode with
    | x86 => exact StringStack.add_encoding .x86 _ _ _ _ packet
    | x64 => exact StackAdjust.subtract_encoding .x64 _ _ _ _ packet
  have fetch3 : StringStack.fetch mode (adjusted mode start target ret seed).principal.memory (adjusted mode start target ret seed).principal.pc.toNat=
      some (StringStack.native mode (third mode start target)) := by
    rw [p3,Arithmetic.encode_nat_toNat mode _ bound.2.1]
    apply StringStack.native_encoding mode
    rw [(windows mode start target ret seed ranges fits stackCurrent placement (thirdPC mode target) c.length (by dsimp [thirdPC];omega)).2.2.1]
    exact cPacket
  have fetch4 : StringStack.fetch mode (exchanged mode start target ret seed).principal.memory (exchanged mode start target ret seed).principal.pc.toNat=
      some (StringStack.native mode (fourth mode start target)) := by
    rw [p4,Arithmetic.encode_nat_toNat mode _ bound.2.2.1]
    apply StringStack.native_encoding mode
    rw [(windows mode start target ret seed ranges fits stackCurrent placement (fourthPC mode target) d.length (by dsimp [fourthPC,thirdPC];omega)).2.2.2.1]
    exact dPacket
  have fetch5 : StringStack.fetch mode (stored mode start target ret seed).principal.memory (stored mode start target ret seed).principal.pc.toNat=
      some (StringStack.native mode (fifth mode start target)) := by
    rw [p5,Arithmetic.encode_nat_toNat mode _ bound.2.2.2]
    apply StringStack.native_encoding mode
    rw [(windows mode start target ret seed ranges fits stackCurrent placement (fifthPC mode target) e.length (by dsimp [fifthPC,fourthPC,thirdPC];omega)).2.2.2.2]
    exact ePacket
  exact .step fetch1 (.step fetch2 (.step fetch3 (.step fetch4 (.step fetch5 (.nil _)))))
end SmcTuring.Appendix.Listing4TargetTrace
