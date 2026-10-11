module
public import SmcTuring.SMC.Primitives

public section

namespace SmcTuring.SMC

@[expose] def copyProgram (label destination : Int) : List Header :=
  readProgram label ++ [.store (.fixed destination)]

theorem copy_correct (wordBytes label destination : Int) (s : State) :
    run wordBytes (copyProgram label destination) s =
      { s with
        acc := s.memory (s.memory label)
        memory := write s.memory destination (s.memory (s.memory label))
        pc := s.pc + 5 } := by
  rw [copyProgram, run_append, read_correct]
  simp [run, decode, Address.eval, execute, Int.add_assoc]

theorem copy_pure (codeField : Int → Prop) (wordBytes label destination : Int) (s : State)
    (hl : codeField label) (hp : codeField (s.memory label)) (hd : codeField destination) :
    PureRun codeField wordBytes (copyProgram label destination) s := by
  rw [copyProgram, pure_append]
  exact ⟨read_pure codeField wordBytes label s hl hp, by
    simp [PureRun, WritesCode, footprint, decode, Address.eval, hd]⟩

/-- The accumulator read preserves the incoming borrow. SBB then records it
as the all-zero or all-one integer mask in a code word. -/
@[expose] def borrowMaskProgram (zeroLabel mask : Int) : List Header :=
  copyProgram zeroLabel mask ++ [.subtractBorrowZero mask]

theorem borrow_mask_correct (wordBytes zeroLabel mask : Int) (s : State)
    (zero : s.memory (s.memory zeroLabel) = 0) :
    run wordBytes (borrowMaskProgram zeroLabel mask) s =
      { s with
        acc := 0
        memory := write s.memory mask (if s.carry then -1 else 0)
        pc := s.pc + 6 } := by
  rw [borrowMaskProgram, run_append, copy_correct]
  cases s.carry <;>
    simp [run, decode, execute, zero, borrowWord, Int.add_assoc]

theorem borrow_mask_pure (codeField : Int → Prop) (wordBytes zeroLabel mask : Int) (s : State)
    (hl : codeField zeroLabel) (hp : codeField (s.memory zeroLabel)) (hm : codeField mask) :
    PureRun codeField wordBytes (borrowMaskProgram zeroLabel mask) s := by
  rw [borrowMaskProgram, pure_append]
  exact ⟨copy_pure codeField wordBytes zeroLabel mask s hl hp hm, by
    simp [PureRun, WritesCode, footprint, decode, hm]⟩

/-- Copy a word through DEFADDR and apply one memory-destination operation.
No register-source read instruction is hidden in this macro. -/
@[expose] def xorProgram (label destination : Int) : List Header :=
  readProgram label ++ [.bitXor destination]

@[expose] def andProgram (label destination : Int) : List Header :=
  readProgram label ++ [.bitAnd destination]

theorem xor_program_correct (wordBytes label destination : Int) (s : State) :
    run wordBytes (xorProgram label destination) s =
      { s with
        acc := s.memory (s.memory label)
        memory := write s.memory destination (xorWord (s.memory destination) (s.memory (s.memory label)))
        carry := false
        pc := s.pc + 5 } := by
  rw [xorProgram, run_append, read_correct]
  simp [run, decode, execute, Int.add_assoc]

theorem and_program_correct (wordBytes label destination : Int) (s : State) :
    run wordBytes (andProgram label destination) s =
      { s with
        acc := s.memory (s.memory label)
        memory := write s.memory destination (andWord (s.memory destination) (s.memory (s.memory label)))
        carry := false
        pc := s.pc + 5 } := by
  rw [andProgram, run_append, read_correct]
  simp [run, decode, execute, Int.add_assoc]

theorem xor_program_pure (codeField : Int → Prop) (wordBytes label destination : Int) (s : State)
    (hl : codeField label) (hp : codeField (s.memory label)) (hd : codeField destination) :
    PureRun codeField wordBytes (xorProgram label destination) s := by
  rw [xorProgram, pure_append]
  exact ⟨read_pure codeField wordBytes label s hl hp, by
    simp [PureRun, WritesCode, footprint, decode, hd]⟩

theorem and_program_pure (codeField : Int → Prop) (wordBytes label destination : Int) (s : State)
    (hl : codeField label) (hp : codeField (s.memory label)) (hd : codeField destination) :
    PureRun codeField wordBytes (andProgram label destination) s := by
  rw [andProgram, pure_append]
  exact ⟨read_pure codeField wordBytes label s hl hp, by
    simp [PureRun, WritesCode, footprint, decode, hd]⟩

end SmcTuring.SMC
