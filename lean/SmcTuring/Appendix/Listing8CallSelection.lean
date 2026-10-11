module
public import SmcTuring.Appendix.Listing8HeadValues

public section
namespace SmcTuring.Appendix.Listing8CallSelection
open Native
@[expose] def failPC (callPC : Nat) := callPC+5
@[expose] def displacement (callPC begin : Nat) := Relocation.relative32 (failPC callPC) begin
@[expose] def toggled (callPC begin : Nat) (exit : Bool) :=
  displacement callPC begin ^^^ (displacement callPC begin &&& InputUpdate.mask exit)

/-- Listing 4 emits a five-byte near CALL at exitcall. Listing 8 places
JUMPTARGET(fail) immediately after it, so the printed difference is exactly
the original backedge displacement. This geometric equality is essential. -/
theorem printed_expression (dollar : Int) (callPC begin : Nat) :
    (dollar-(failPC callPC : Int))-(dollar-(begin : Int)) = Relocation.delta (failPC callPC) begin := by
  unfold Relocation.delta
  omega

theorem toggle_selection (old : BitVec 32) (exit : Bool) :
    old ^^^ (old &&& InputUpdate.mask exit) = if exit then 0 else old := by
  cases exit with
  | false => simp [InputUpdate.mask]
  | true =>
    change old ^^^ (old &&& BitVec.allOnes 32) = 0
    rw [BitVec.and_allOnes,BitVec.xor_self]
    rfl

theorem displacement_selection (callPC begin : Nat) (exit : Bool) :
    toggled callPC begin exit = if exit then 0 else displacement callPC begin :=
  toggle_selection _ exit

/-- Patching only the four CALL operand bytes preserves its opcode and
derives the complete later packet from its initial live image. -/
theorem operand_current (mode : Mode) (memory : ByteMemory.Memory) (callPC : Nat) (old fresh : BitVec 32)
    (initial : ByteMemory.bytesAt memory callPC 5 = Native.encode mode (.callRelative old)) :
    ByteMemory.bytesAt (DwordCode.put memory (callPC+1) fresh) callPC 5 = Native.encode mode (.callRelative fresh) := by
  have patched := BytePatch.current memory callPC [0xE8] (LittleEndian.wordEncode 4 old)
    (LittleEndian.wordEncode 4 fresh) [] (by simp only [LittleEndian.word_encode_length])
    (by simpa only [Native.encode,List.append_nil,List.length_append,List.length_cons,List.length_nil,
      LittleEndian.word_encode_length] using initial)
  simpa only [DwordCode.put,List.length_cons,List.length_nil,Nat.add_zero,Nat.zero_add,
    List.append_nil,List.length_append,LittleEndian.word_encode_length,Native.encode] using patched

theorem patched_fetch (mode : Mode) (memory : ByteMemory.Memory) (callPC begin : Nat) (exit : Bool)
    (initial : ByteMemory.bytesAt memory callPC 5 = Native.encode mode (.callRelative (displacement callPC begin))) :
    StringDword.fetch mode (DwordCode.put memory (callPC+1) (toggled callPC begin exit)) callPC =
      some (StringDwordCopy.native mode (.callRelative (if exit then 0 else displacement callPC begin))) := by
  rw [←displacement_selection]
  exact StringDwordCopy.native_encoding mode (.callRelative (toggled callPC begin exit)) _ callPC
    (operand_current mode memory callPC _ _ initial)

theorem call_target (mode : Mode) (callPC begin : Nat) (exit : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode callPC)
    (reach : Relocation.SignedDelta (failPC callPC) begin) :
    (Execution.execute mode (.callRelative (toggled callPC begin exit)) state).pc =
      if exit then Arithmetic.encodeNat mode (failPC callPC) else Arithmetic.encodeNat mode begin := by
  rw [displacement_selection]
  cases exit with
  | false => exact Relocation.relative_call_pc mode callPC begin state entry reach
  | true =>
    change Execution.nextPC mode (.callRelative 0) state + Execution.displacementWord mode 0 = _
    rw [Relocation.next_pc mode state (.callRelative 0) callPC entry]
    cases mode with
    | x86 =>
      change Arithmetic.encodeNat .x86 (callPC+5)+(0 : Word .x86) = Arithmetic.encodeNat .x86 (callPC+5)
      exact BitVec.add_zero _
    | x64 =>
      change Arithmetic.encodeNat .x64 (callPC+5)+(0 : Word .x64) = Arithmetic.encodeNat .x64 (callPC+5)
      exact BitVec.add_zero _

theorem call_return_word (mode : Mode) (callPC begin : Nat) (exit : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode callPC) :
    ByteMemory.readWord mode (Execution.execute mode (.callRelative (toggled callPC begin exit)) state).memory
      (state.stack-Arithmetic.encodeNat mode mode.wordBytes).toNat = some (Arithmetic.encodeNat mode (failPC callPC)) := by
  change ByteMemory.readWord mode
    (ByteMemory.putWord mode state.memory (state.stack-Arithmetic.encodeNat mode mode.wordBytes).toNat
      (Execution.nextPC mode (.callRelative (toggled callPC begin exit)) state)) _ = _
  rw [ByteMemory.read_put_word,Relocation.next_pc mode state _ callPC entry]
  rfl

theorem reset_fetch (mode : Mode) (memory : ByteMemory.Memory) (callPC begin : Nat) (old : BitVec 32)
    (current : ByteMemory.bytesAt memory callPC 5 = Native.encode mode (.callRelative old)) :
    StringDword.fetch mode (DwordCode.put memory (callPC+1) (displacement callPC begin)) callPC =
      some (StringDwordCopy.native mode (.callRelative (displacement callPC begin))) :=
  StringDwordCopy.native_encoding mode (.callRelative (displacement callPC begin)) _ callPC
    (operand_current mode memory callPC old _ current)

end SmcTuring.Appendix.Listing8CallSelection
