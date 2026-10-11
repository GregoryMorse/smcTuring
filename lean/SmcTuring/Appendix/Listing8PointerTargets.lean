module
public import SmcTuring.Native.DwordRetarget
public import SmcTuring.Native.BytePatch

public section
namespace SmcTuring.Appendix.Listing8PointerTargets
open Native
abbrev Dword := BitVec 32

/-- OP64 expands pending XOR into one/two ten-byte DATAOP packets. Its
immediates are at +6/+16; the actual pointer halves are four bytes apart. -/
theorem slots : (6 : Nat)+10 = 16 ∧ (4 : Nat) < 10 ∧ (0 : Nat)+6 = 6 := by decide

theorem opcode_copy_counterexample :
    let memory := ByteMemory.putBytes (fun _ => 0) 4096 (DwordArithmetic.encode (.bitXor 0 0x80000000))
    DwordArithmetic.fetch (DwordCode.put memory 4096 0) 4096 = none := by decide

theorem immediate_patch (memory : ByteMemory.Memory) (pc : Nat) (disp old fresh : Dword)
    (current : ByteMemory.bytesAt memory pc 10 = DwordArithmetic.encode (.bitXor disp old)) :
    ByteMemory.bytesAt (DwordCode.put memory (pc+6) fresh) pc 10 = DwordArithmetic.encode (.bitXor disp fresh) := by
  exact BytePatch.current memory pc ([0x81,0x35] ++ LittleEndian.wordEncode 4 disp)
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 fresh) []
    (by simp only [LittleEndian.word_encode_length]) (by simpa [DwordArithmetic.encode,List.append_assoc] using current)

theorem pointer_half_effect (mode : Mode) (pc pointerHalf : Nat) (delta : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+10) pointerHalf)
    (fits : pointerHalf < 2^(8*mode.wordBytes)) :
    DwordArithmetic.execute mode (DwordArithmetic.located mode (.bitXor 0 delta) pc pointerHalf) state =
      { state with
        pc := Arithmetic.encodeNat mode (pc+10)
        carry := false
        memory := DwordCode.put state.memory pointerHalf (DwordCode.get state.memory pointerHalf ^^^ delta) } :=
  DwordArithmetic.located_effect mode (.bitXor 0 delta) pc pointerHalf state rfl entry range fits

theorem half_selected (old fresh : Dword) (chosen : Bool) :
    old ^^^ ((old ^^^ fresh) &&& (if chosen then BitVec.allOnes 32 else 0)) = if chosen then fresh else old := by
  cases chosen
  · simp
  · change old ^^^ ((old ^^^ fresh) &&& BitVec.allOnes 32) = fresh
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc]
    simp

end SmcTuring.Appendix.Listing8PointerTargets
