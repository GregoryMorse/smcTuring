module
public import SmcTuring.Appendix.Listing4JumpEffects
public import SmcTuring.Native.StackWindows

public section
namespace SmcTuring.Appendix.Listing4Boot
open Native LittleEndian Listing4StackLayout Listing4JumpLayout
@[expose] def bytes (mode : Mode) (start : Nat) := Listing4StackLayout.bytes mode start++Listing4JumpLayout.bytes mode start
@[expose] def size : Mode → Nat | .x86 => 21 | .x64 => 61
@[expose] def forms (mode : Mode) (start : Nat) := Listing4StackLayout.forms mode start++Listing4JumpLayout.forms mode start
@[expose] def initial (mode : Mode) (start : Nat) (seed : StringExecution.State mode) : StringExecution.State mode :=
  {seed with principal := {seed.principal with
    pc := Arithmetic.encodeNat mode start
    memory := ByteMemory.putBytes seed.principal.memory start (bytes mode start)}}
theorem bytes_length (mode : Mode) (start : Nat) : (bytes mode start).length = size mode := by
  rw [bytes,List.length_append,Listing4StackLayout.bytes_length,Listing4JumpLayout.bytes_length]
  cases mode <;> rfl
theorem endpoint (mode : Mode) (start : Nat) : beginPC mode start=start+size mode := by
  cases mode <;> dsimp [beginPC,callPC,jumpPC,Listing4StackLayout.size,prefixSize,size] <;> omega
theorem stack_before_jump (mode : Mode) (start : Nat) : stptr mode start+mode.wordBytes ≤ jumpPC mode start := by
  cases mode <;> dsimp [stptr,jumpPC,Listing4StackLayout.size,Mode.wordBytes] <;> omega
theorem return_before_jump (mode : Mode) (start : Nat) : returnField mode start+mode.wordBytes ≤ jumpPC mode start := by
  cases mode <;> dsimp [returnField,jumpPC,Listing4StackLayout.size,Mode.wordBytes] <;> omega
theorem initial_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (initial mode start seed).principal.memory start (size mode) = bytes mode start := by
  unfold initial
  simpa only [bytes_length] using ByteMemory.bytes_at_put seed.principal.memory start (bytes mode start)
theorem stack_packet (mode : Mode) (start : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (size mode) = bytes mode start) :
    ByteMemory.bytesAt memory start (Listing4StackLayout.size mode) = Listing4StackLayout.bytes mode start := by
  have packet := ByteWindow.packet memory start [] (Listing4StackLayout.bytes mode start) (Listing4JumpLayout.bytes mode start)
    (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt memory start (bytes mode start).length = bytes mode start
      rw [bytes_length];exact current)
  simpa only [List.length_nil,Nat.add_zero,Listing4StackLayout.bytes_length] using packet
theorem jump_packet (mode : Mode) (start : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (size mode) = bytes mode start) :
    ByteMemory.bytesAt memory (jumpPC mode start) (Listing4JumpLayout.bytes mode start).length = Listing4JumpLayout.bytes mode start := by
  have packet := ByteWindow.packet memory start (Listing4StackLayout.bytes mode start) (Listing4JumpLayout.bytes mode start) []
    (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt memory start (bytes mode start).length = bytes mode start
      rw [bytes_length];exact current)
  simpa only [Listing4StackLayout.bytes_length,jumpPC] using packet

/-- One initialized image executes printed DEFSTACK, its JUMP prefix and CALL.
No stack value or future packet/fetch/trace is supplied as a premise. -/
theorem trace (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : start+size mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (size mode) = bytes mode start) :
    StringStack.Trace mode state (forms mode start) (Listing4JumpEffects.finish mode start state) := by
  have capacity : beginPC mode start < 2^(8*mode.wordBytes) := by rw [endpoint];exact fits
  have stackCurrent := stack_packet mode start state.principal.memory current
  have jumpCurrent := jump_packet mode start state.principal.memory current
  have stackFits : start+Listing4StackLayout.size mode < 2^(8*mode.wordBytes) := by
    cases mode <;> dsimp [size,Listing4StackLayout.size] at * <;> omega
  have initEffect := Listing4StackInit.effect mode start state entry stackFits stackCurrent
  have firstEffect := Listing4JumpEffects.exchanged_effect mode start state entry capacity stackCurrent
  have lastEffect := Listing4JumpEffects.prefix_effect mode start state entry capacity stackCurrent
  have stackFirst := stack_before_jump mode start
  have savedFirst := return_before_jump mode start
  have jumpFits : jumpPC mode start < 2^(8*mode.wordBytes) := by dsimp [beginPC,callPC] at capacity;omega
  have callFits : callPC mode start < 2^(8*mode.wordBytes) := by dsimp [beginPC] at capacity;omega
  have callPacket : ByteMemory.bytesAt state.principal.memory (callPC mode start) (Native.encode mode (call mode)).length = Native.encode mode (call mode) := by
    have packet := ByteWindow.packet state.principal.memory (jumpPC mode start) (prefixBytes mode start) (Native.encode mode (call mode)) []
      (by simpa only [List.append_nil,Listing4JumpLayout.bytes] using jumpCurrent)
    simpa only [prefix_length,callPC] using packet
  have firstPC : (Listing4StackInit.finish mode start state).principal.pc = Arithmetic.encodeNat mode (jumpPC mode start) := by rw [initEffect];rfl
  have callPosition : (Listing4JumpEffects.prefixEnd mode start state).principal.pc = Arithmetic.encodeNat mode (callPC mode start) := by rw [lastEffect]
  have callFetched : StringStack.fetch mode (Listing4JumpEffects.prefixEnd mode start state).principal.memory
      (Listing4JumpEffects.prefixEnd mode start state).principal.pc.toNat = some (StringStack.native mode (call mode)) := by
    rw [callPosition,Arithmetic.encode_nat_toNat mode _ callFits]
    apply StringStack.native_encoding mode
    rw [lastEffect,StackWindows.word_window mode state.principal.memory (stptr mode start) (callPC mode start) _ _
      (Or.inl (by dsimp [callPC];omega))]
    exact callPacket
  have localTrace : StringStack.Trace mode (Listing4StackInit.finish mode start state) (Listing4JumpLayout.forms mode start)
      (Listing4JumpEffects.finish mode start state) := by
    cases mode with
    | x86 =>
      have firstPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x86 start) (Native.encode .x86 (exchange .x86 start)).length =
          Native.encode .x86 (exchange .x86 start) := by
        exact ByteWindow.packet state.principal.memory (jumpPC .x86 start) [] (Native.encode .x86 (exchange .x86 start))
          (Native.encode .x86 (call .x86)) (by simpa only [List.nil_append,Listing4JumpLayout.bytes,prefixBytes] using jumpCurrent)
      have fetched : StringStack.fetch .x86 (Listing4StackInit.finish .x86 start state).principal.memory
          (Listing4StackInit.finish .x86 start state).principal.pc.toNat = some (StringStack.native .x86 (exchange .x86 start)) := by
        rw [firstPC,Arithmetic.encode_nat_toNat .x86 _ jumpFits,initEffect]
        exact StringStack.native_encoding .x86 _ _ _ firstPacket
      exact .step fetched (.step callFetched (.nil _))
    | x64 =>
      let a := Native.encode .x64 (exchange .x64 start)
      let b := WordAddImmediate.encode .x64 (Relocation.memoryDisp .x64 (jumpPC .x64 start+7+8) (returnField .x64 start)) 18
      let c := Native.encode .x64 (exchangeSaved start)
      let d := Native.encode .x64 (call .x64)
      have code : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 start) (a++b++c++d).length = a++b++c++d := by
        simpa only [Listing4JumpLayout.bytes,prefixBytes,List.append_assoc] using jumpCurrent
      have aPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 start) a.length = a := by
        exact ByteWindow.packet state.principal.memory (jumpPC .x64 start) [] a (b++c++d) (by simpa only [List.nil_append,List.append_assoc] using code)
      have bPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 start+7) b.length = b := by
        exact ByteWindow.packet state.principal.memory (jumpPC .x64 start) a b (c++d) (by simpa only [List.append_assoc] using code)
      have cPacket : ByteMemory.bytesAt state.principal.memory (jumpPC .x64 start+7+8) c.length = c := by
        have packet := ByteWindow.packet state.principal.memory (jumpPC .x64 start) (a++b) c d code
        simpa only [show (a++b).length=7+8 from rfl,Nat.add_assoc] using packet
      have pc1 : (Listing4JumpEffects.exchanged .x64 start state).principal.pc = Arithmetic.encodeNat .x64 (jumpPC .x64 start+7) := by rw [firstEffect];rfl
      have secondEffect := Listing4JumpEffects.adjusted_effect start state entry capacity stackCurrent
      have pc2 : (Listing4JumpEffects.adjusted start state).principal.pc = Arithmetic.encodeNat .x64 (jumpPC .x64 start+7+8) := by rw [secondEffect]
      have fetched : StringStack.fetch .x64 (Listing4StackInit.finish .x64 start state).principal.memory
          (Listing4StackInit.finish .x64 start state).principal.pc.toNat = some (StringStack.native .x64 (exchange .x64 start)) := by
        rw [firstPC,Arithmetic.encode_nat_toNat .x64 _ jumpFits,initEffect]
        exact StringStack.native_encoding .x64 _ _ _ aPacket
      have fetched2 : StringStack.fetch .x64 (Listing4JumpEffects.exchanged .x64 start state).principal.memory
          (Listing4JumpEffects.exchanged .x64 start state).principal.pc.toNat = some (adjust start) := by
        have small : jumpPC .x64 start+7 < 2^64 := by
          change beginPC .x64 start<2^64 at capacity;dsimp [beginPC,callPC,prefixSize] at capacity;omega
        rw [pc1,Arithmetic.encode_nat_toNat .x64 _ small]
        apply StringStack.add_encoding .x64
        rw [firstEffect,StackWindows.word_window .x64 _ (stptr .x64 start) (jumpPC .x64 start+7) _ _ (Or.inl (by omega))]
        exact bPacket
      have fetched3 : StringStack.fetch .x64 (Listing4JumpEffects.adjusted start state).principal.memory
          (Listing4JumpEffects.adjusted start state).principal.pc.toNat = some (StringStack.native .x64 (exchangeSaved start)) := by
        have small : jumpPC .x64 start+7+8 < 2^64 := by
          change beginPC .x64 start<2^64 at capacity;dsimp [beginPC,callPC,prefixSize] at capacity;omega
        rw [pc2,Arithmetic.encode_nat_toNat .x64 _ small]
        apply StringStack.native_encoding .x64
        rw [secondEffect,StackWindows.word_window .x64 _ (returnField .x64 start) (jumpPC .x64 start+7+8) _ _ (Or.inl (by omega)),
          StackWindows.word_window .x64 _ (stptr .x64 start) (jumpPC .x64 start+7+8) _ _ (Or.inl (by omega))]
        exact cPacket
      exact .step fetched (.step fetched2 (.step fetched3 (.step callFetched (.nil _))))
  exact StringStack.trace_append mode (Listing4StackInitTrace.trace mode start state entry stackFits stackCurrent) localTrace

theorem initialized_trace (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : start+size mode < 2^(8*mode.wordBytes)) :
    StringStack.Trace mode (initial mode start seed) (forms mode start)
      (Listing4JumpEffects.finish mode start (initial mode start seed)) :=
  trace mode start _ rfl fits (initial_current mode start seed)
theorem instruction_count (mode : Mode) (start : Nat) : (forms mode start).length = (if mode=.x86 then 3 else 8) := by cases mode <;> rfl
end SmcTuring.Appendix.Listing4Boot
