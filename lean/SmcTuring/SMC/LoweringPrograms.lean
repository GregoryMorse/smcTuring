module
public import SmcTuring.SMC.OperandLayout

public section

namespace SmcTuring.SMC.Lowering

open Dolan

/-- Effect blocks for the three source MOV forms. Accesses require a valid
typed source address. A separate control guard must be inserted before an
indirect access when composing fault/terminal behavior. -/
@[expose] def addressProgram (layout : OperandLayout) (base offset : Four.Register) : List Header :=
  copyProgram (layout.registerLabel base) layout.pointer ++
    readProgram (layout.registerLabel offset) ++ [.add layout.pointer]

@[expose] def addressResult (layout : OperandLayout) (source : Four.State) (target : State)
    (base offset : Four.Register) : State :=
  { target with
    acc := encodeWord layout.data (source.registers offset)
    memory := write target.memory layout.pointer
      (encodeWord layout.data (source.registers base) + encodeWord layout.data (source.registers offset))
    carry := false
    pc := target.pc + 10 }

theorem address_program_correct (layout : OperandLayout) (wordBytes : Int)
    (source : Four.State) (target : State) (base offset : Four.Register) (rep : Rep layout source target) :
    run wordBytes (addressProgram layout base offset) target = addressResult layout source target base offset := by
  have label := layout.pointerRegisterLabel offset
  have register := data_field_separate layout.data _ _ layout.pointerOutside (register_is_code layout.data offset)
  simp only [addressProgram, run_append, copy_correct, read_correct]
  simp [addressResult, run, decode, execute, write, label, register,
    rep.2.1 base, rep.2.1 offset, rep.1.1 base, rep.1.1 offset, Int.add_assoc]

theorem address_result_rep (layout : OperandLayout) (source : Four.State) (target : State)
    (base offset : Four.Register) (rep : Rep layout source target) :
    Rep layout source (addressResult layout source target base offset) := by
  simpa only [addressResult, Rep, NumericRep, StaticRep] using
    pointer_rep layout source target
      (encodeWord layout.data (source.registers base) + encodeWord layout.data (source.registers offset)) rep

theorem address_program_pure (layout : OperandLayout) (wordBytes : Int)
    (source : Four.State) (target : State) (base offset : Four.Register) (rep : Rep layout source target) :
    PureRun (Code layout) wordBytes (addressProgram layout base offset) target := by
  simp only [addressProgram, pure_append, run_append, copy_correct, read_correct]
  refine ⟨⟨copy_pure (Code layout) wordBytes _ _ target (register_label_code layout base) ?_
    (pointer_code layout), ?_⟩, ?_⟩
  · rw [rep.2.1 base]
    exact data_code layout _ (register_is_code layout.data base)
  · apply read_pure
    · exact register_label_code layout offset
    · have label := layout.pointerRegisterLabel offset
      simp only [read_write_other _ _ _ _ label, rep.2.1 offset]
      exact data_code layout _ (register_is_code layout.data offset)
  · simp [PureRun, WritesCode, footprint, decode, pointer_code layout]

@[expose] def compileInstruction (layout : OperandLayout) : Four.Instruction → List Header
  | .immediate destination value =>
    copyProgram (layout.constantLabel value) (registerField layout.data destination)
  | .load destination base offset =>
    addressProgram layout base offset ++ copyProgram layout.pointer (registerField layout.data destination)
  | .store base offset source =>
    addressProgram layout base offset ++ readProgram (layout.registerLabel source) ++ [.store (.operand layout.pointer)]

theorem immediate_correct (layout : OperandLayout) (wordBytes : Int)
    (source : Four.State) (target : State) (destination : Four.Register) (value : Mov.Word)
    (rep : Rep layout source target) :
    Rep layout { source with registers := write source.registers destination value }
      (run wordBytes (compileInstruction layout (.immediate destination value)) target) ∧
    PureRun (Code layout) wordBytes (compileInstruction layout (.immediate destination value)) target := by
  constructor
  · rw [compileInstruction, copy_correct, rep.2.2.1 value, rep.2.2.2 value]
    simpa only [Rep, NumericRep, StaticRep] using register_rep layout source target destination value rep
  · apply copy_pure
    · exact constant_label_code layout value
    · rw [rep.2.2.1 value]
      exact constant_field_code layout value
    · exact data_code layout _ (register_is_code layout.data destination)

end SmcTuring.SMC.Lowering
