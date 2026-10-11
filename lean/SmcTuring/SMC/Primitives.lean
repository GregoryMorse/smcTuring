module
public import SmcTuring.SMC.Machine

public section

namespace SmcTuring.SMC

@[expose] def readProgram (label : Int) : List Header :=
  [.exchange (.fixed label), .store (.fixed label), .exchange .accumulator, .store (.operand label)]

theorem read_correct (wordBytes label : Int) (s : State) :
    run wordBytes (readProgram label) s =
      { s with acc := s.memory (s.memory label), pc := s.pc + 4 } := by
  by_cases h : s.memory label = label
  · have same : write s.memory label label = s.memory := by simpa [h] using write_back s.memory label
    simp [readProgram, run, decode, Address.eval, execute, h, same, Int.add_assoc]
  · simp [readProgram, run, decode, Address.eval, execute, Ne.symm h, Int.add_assoc]

theorem read_pure (codeField : Int → Prop) (wordBytes label : Int) (s : State)
    (hl : codeField label) (hp : codeField (s.memory label)) :
    PureRun codeField wordBytes (readProgram label) s := by
  by_cases h : s.memory label = label
  · simp [PureRun, WritesCode, readProgram, footprint, decode, Address.eval, execute, write, h, hl]
  · simp [PureRun, WritesCode, readProgram, footprint, decode, Address.eval, execute, write, Ne.symm h, hl, hp]

@[expose] def stackResetProgram (field : Int) : List Header := [.exchangeStack field, .storeStack field]

theorem stack_reset_correct (wordBytes field : Int) (s : State) :
    run wordBytes (stackResetProgram field) s = { s with stack := s.memory field, pc := s.pc + 2 } := by
  simp [stackResetProgram, run, decode, execute, Int.add_assoc]

theorem stack_reset_pure (codeField : Int → Prop) (wordBytes field : Int) (s : State)
    (code : codeField field) : PureRun codeField wordBytes (stackResetProgram field) s := by
  simp [PureRun, stackResetProgram, WritesCode, footprint, decode, code]

theorem call_correct (wordBytes target next : Int) (s : State) :
    execute wordBytes (.call target) next s =
      { s with
        stack := s.stack - wordBytes
        pc := target
        memory := write s.memory (s.stack - wordBytes) next } := rfl

theorem call_pure (codeField : Int → Prop) (wordBytes target : Int) (s : State)
    (code : codeField (s.stack - wordBytes)) : WritesCode codeField wordBytes (.call target) s := by
  simp [WritesCode, footprint, code]

/-- Reset and one CALL write the return address to the designated code field.
The accumulator and carry survive both the reset and the control transfer. -/
theorem reset_call_correct (wordBytes constant stackField target : Int) (s : State)
    (top : s.memory constant = stackField + wordBytes) :
    run wordBytes (stackResetProgram constant ++ [.call (.fixed target)]) s =
      { s with
        stack := stackField
        pc := target
        memory := write s.memory stackField (s.pc + 3) } := by
  rw [run_append, stack_reset_correct]
  simp [run, decode, Address.eval, execute, top, Int.add_assoc]

theorem reset_call_pure (codeField : Int → Prop) (wordBytes constant stackField target : Int) (s : State)
    (top : s.memory constant = stackField + wordBytes)
    (hc : codeField constant) (hs : codeField stackField) :
    PureRun codeField wordBytes (stackResetProgram constant ++ [.call (.fixed target)]) s := by
  rw [pure_append]
  constructor
  · exact stack_reset_pure codeField wordBytes constant s hc
  · rw [stack_reset_correct]
    simp [PureRun, WritesCode, footprint, decode, Address.eval, top]
    exact hs

theorem reset_call_operand_correct (wordBytes constant stackField targetField : Int) (s : State)
    (top : s.memory constant = stackField + wordBytes) :
    run wordBytes (stackResetProgram constant ++ [.call (.operand targetField)]) s =
      { s with
        stack := stackField
        pc := s.memory targetField
        memory := write s.memory stackField (s.pc + 3) } := by
  rw [run_append, stack_reset_correct]
  simp [run, decode, Address.eval, execute, top, Int.add_assoc]

theorem reset_call_operand_pure (codeField : Int → Prop)
    (wordBytes constant stackField targetField : Int) (s : State)
    (top : s.memory constant = stackField + wordBytes)
    (hc : codeField constant) (hs : codeField stackField) :
    PureRun codeField wordBytes (stackResetProgram constant ++ [.call (.operand targetField)]) s := by
  rw [pure_append]
  constructor
  · exact stack_reset_pure codeField wordBytes constant s hc
  · rw [stack_reset_correct]
    simp [PureRun, WritesCode, footprint, decode, top]
    exact hs

end SmcTuring.SMC
