module
public import SmcTuring.Appendix.Listing8JumpWrites

public section
namespace SmcTuring.Native.StackFieldWrites

theorem memory (mode : Mode) (operation : MemoryOp) (noncall : operation≠.callIndirect) (codeStart codeEnd pc target : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+Native.instructionLength mode (.memory operation 0)) target)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode target)) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringStack.native mode
      (.memory operation (Relocation.instructionDisp mode operation pc target))) state := by
  have hit:=Relocation.instruction_memory_hits mode operation pc target state.principal entry range
  apply Appendix.Listing8JumpWrites.native_write mode codeStart codeEnd _ state
  cases operation <;> simp_all only [Writes.address,ne_eq,not_true_eq_false]

theorem add (mode : Mode) (codeStart codeEnd pc target : Nat) (value : BitVec 8) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+WordAddImmediate.length mode) target)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode target)) :
    StringWrites.CodeWrite mode codeStart codeEnd (.addSmall (Relocation.memoryDisp mode (pc+WordAddImmediate.length mode) target) value) state := by
  have next : WordAddImmediate.next mode state.principal=Arithmetic.encodeNat mode (pc+WordAddImmediate.length mode) := by
    rw [WordAddImmediate.next,entry];exact BitVec.ofNat_add_ofNat _ _
  have hit : WordAddImmediate.address mode (Relocation.memoryDisp mode (pc+WordAddImmediate.length mode) target) state.principal=
      Arithmetic.encodeNat mode target := by
    rw [WordAddImmediate.address,next];exact Relocation.memory_hits mode _ _ range
  have length : (StringWrites.packet mode (.addSmall (Relocation.memoryDisp mode (pc+WordAddImmediate.length mode) target) value) state).bytes.length=mode.wordBytes :=
    LittleEndian.word_encode_length _ _
  have address : (StringWrites.packet mode (.addSmall (Relocation.memoryDisp mode (pc+WordAddImmediate.length mode) target) value) state).address=
      (Arithmetic.encodeNat mode target).toNat := congrArg BitVec.toNat hit
  unfold StringWrites.CodeWrite
  rw [length,address]
  exact ⟨by cases mode <;> decide,owned⟩

/-- Append ownership using the state equality proved by the actual first trace. -/
theorem owned_append (mode : Mode) (codeStart codeEnd : Nat) (first second : List (StringStack.Form mode))
    (initial reached : StringExecution.State mode)
    (executed : StringStack.Trace mode initial first reached)
    (firstOwned : StringWrites.OwnedRun mode codeStart codeEnd first initial)
    (secondOwned : StringWrites.OwnedRun mode codeStart codeEnd second reached) :
    StringWrites.OwnedRun mode codeStart codeEnd (first++second) initial := by
  apply (StringWrites.owned_run_append mode codeStart codeEnd first second initial).mpr
  refine ⟨firstOwned,?_⟩
  rw [StringWrites.trace_run_eq mode executed]
  exact secondOwned

end SmcTuring.Native.StackFieldWrites
