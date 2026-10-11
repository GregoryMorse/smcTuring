module
public import SmcTuring.Appendix.DivisionAlgebra
public import SmcTuring.Appendix.MultiplyWords
public import SmcTuring.Appendix.ByteControl

public section
namespace SmcTuring.Appendix.DivisionRepairs

open Machine32

/-- The corrected signed-prefix copy writes the divisor's own MOV immediate.
Its later sign normalization uses this same field, rather than lbl11's temporary. -/
theorem divisor_copy (source divisorField : Nat) (state : State)
    (separate : divisorField ≠ source) :
    (MultiplyWords.run (MultiplyWords.copyProgram divisorField source) state).memory divisorField =
      state.memory source := by
  rw [MultiplyWords.copy_effect _ _ _ separate]
  simp [put, write]

theorem divisor_copy_register (source divisorField : Nat) (state : State)
    (separate : divisorField ≠ source) :
    (MultiplyWords.run (MultiplyWords.copyProgram divisorField source) state).accumulator =
      state.accumulator := by
  rw [MultiplyWords.copy_effect _ _ _ separate]
  rfl

/-- Listing 12 has the same eight-instruction zero-test as Listing 11,
with counter, delta, mask and displacement occupying its corresponding fields. -/
theorem exit_selection (fields : MultiplyWords.Fields) (state : State)
    (separate : MultiplyWords.Separate fields) (callPC exitPC : Word)
    (initial : state.memory (fields .displacement) = 0) :
    callPC + 5 +
      (MultiplyWords.run
        (MultiplyWords.guard fields (exitPC - callPC - 5)) state).memory (fields .displacement) =
      if state.memory (fields .multiplier) = 0 then exitPC else callPC + 5 := by
  have delta : exitPC - callPC - 5 = exitPC - (callPC + 5) := by ring
  rw [delta]
  exact MultiplyWords.guard_target _ _ _ _ separate initial

theorem exit_delta (callPC exitPC : Word) :
    callPC + 5 + (exitPC - callPC - 5) = exitPC := by ring

/-- The new continuation name denotes the existing fall-through address.
It differs from the CALL's own label and introduces no new instruction. -/
theorem body_continuation (callPC : Nat) : callPC + 1 + 4 = callPC + 5 ∧
    callPC + 5 ≠ callPC := by omega

theorem reset_owned_field (callPC : Nat) (old : Word) :
    (ByteImage.Entry.mk callPC (.relative old)).fields = [callPC + 1] := rfl

/-- A full DWORD store at lbl10+OPSZ1 preserves E8 and resets its rel32 operand. -/
theorem reset_packet (memory : Native.ByteMemory.Memory) (callPC : Nat) (old : Word) :
    Native.ByteMemory.putWord .x86
      (Native.ByteMemory.putBytes memory callPC (ByteCode.encode (.callRelative old)))
      (callPC + 1) 0 =
    Native.ByteMemory.putBytes memory callPC (ByteCode.encode (.callRelative 0)) :=
  ByteCode.call_patch memory callPC old 0

theorem reset_fetch (memory : Native.ByteMemory.Memory) (callPC : Nat) (old : Word)
    (current : Native.ByteMemory.bytesAt memory callPC
      (ByteCode.encode (.callRelative old)).length = ByteCode.encode (.callRelative old)) :
    ByteCode.fetch
      (Native.ByteMemory.putWord .x86 memory (callPC + 1) 0) callPC =
        some (.callRelative 0) :=
  ByteCode.fetch_patched_current_call memory callPC old 0 current

end SmcTuring.Appendix.DivisionRepairs
