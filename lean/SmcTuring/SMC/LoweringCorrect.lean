module
public import SmcTuring.SMC.LoweringPrograms

public section

namespace SmcTuring.SMC.Lowering

open Dolan

theorem load_correct (layout : OperandLayout) (wordBytes : Int)
    (source : Four.State) (target : State) (destination base offset : Four.Register)
    (cell : Nat) (choice : Bool) (rep : Rep layout source target)
    (baseValue : source.registers base = .address cell)
    (offsetValue : source.registers offset = .offset choice) :
    Rep layout { source with registers := write source.registers destination (source.memory (cell, choice)) }
      (run wordBytes (compileInstruction layout (.load destination base offset)) target) ∧
    PureRun (Code layout) wordBytes (compileInstruction layout (.load destination base offset)) target := by
  let middle := addressResult layout source target base offset
  have middleRep := address_result_rep layout source target base offset rep
  have pointer : middle.memory layout.pointer = heapField layout.data (cell, choice) := by
    simp only [middle, addressResult, read_write_same, baseValue, offsetValue, indexed_address_correct]
  have value : middle.memory (heapField layout.data (cell, choice)) =
      encodeWord layout.data (source.memory (cell, choice)) := middleRep.1.2 (cell, choice)
  constructor
  · rw [compileInstruction, run_append, address_program_correct layout wordBytes source target base offset rep]
    change Rep layout _ (run wordBytes (copyProgram layout.pointer _) middle)
    rw [copy_correct, pointer, value]
    simpa only [Rep, NumericRep, StaticRep] using
      register_rep layout source middle destination (source.memory (cell, choice)) middleRep
  · rw [compileInstruction, pure_append]
    refine ⟨address_program_pure layout wordBytes source target base offset rep, ?_⟩
    rw [address_program_correct layout wordBytes source target base offset rep]
    apply copy_pure
    · exact pointer_code layout
    · change Code layout (middle.memory layout.pointer)
      rw [pointer]
      exact data_code layout _ (heap_is_code layout.data (cell, choice))
    · exact data_code layout _ (register_is_code layout.data destination)

theorem store_correct (layout : OperandLayout) (wordBytes : Int)
    (source : Four.State) (target : State) (base offset valueRegister : Four.Register)
    (cell : Nat) (choice : Bool) (rep : Rep layout source target)
    (baseValue : source.registers base = .address cell)
    (offsetValue : source.registers offset = .offset choice) :
    Rep layout { source with memory := write source.memory (cell, choice) (source.registers valueRegister) }
      (run wordBytes (compileInstruction layout (.store base offset valueRegister)) target) ∧
    PureRun (Code layout) wordBytes (compileInstruction layout (.store base offset valueRegister)) target := by
  let middle := addressResult layout source target base offset
  have middleRep := address_result_rep layout source target base offset rep
  have pointer : middle.memory layout.pointer = heapField layout.data (cell, choice) := by
    simp only [middle, addressResult, read_write_same, baseValue, offsetValue, indexed_address_correct]
  have label : middle.memory (layout.registerLabel valueRegister) = registerField layout.data valueRegister := middleRep.2.1 valueRegister
  have value : middle.memory (registerField layout.data valueRegister) =
      encodeWord layout.data (source.registers valueRegister) := middleRep.1.1 valueRegister
  constructor
  · simp only [compileInstruction, run_append]
    rw [address_program_correct layout wordBytes source target base offset rep]
    change Rep layout _ (run wordBytes [.store (.operand layout.pointer)]
      (run wordBytes (readProgram (layout.registerLabel valueRegister)) middle))
    rw [read_correct]
    simp only [run, decode, Address.eval, execute, pointer, label, value]
    simpa only [Rep, NumericRep, StaticRep] using
      heap_rep layout source middle (cell, choice) (source.registers valueRegister) middleRep
  · simp only [compileInstruction, pure_append, run_append]
    refine ⟨⟨address_program_pure layout wordBytes source target base offset rep, ?_⟩, ?_⟩
    · rw [address_program_correct layout wordBytes source target base offset rep]
      apply read_pure
      · exact register_label_code layout valueRegister
      · change Code layout (middle.memory (layout.registerLabel valueRegister))
        rw [label]
        exact data_code layout _ (register_is_code layout.data valueRegister)
    · rw [address_program_correct layout wordBytes source target base offset rep, read_correct]
      change PureRun (Code layout) wordBytes [.store (.operand layout.pointer)] _
      have code : Code layout (middle.memory layout.pointer) := by
        rw [pointer]
        exact data_code layout _ (heap_is_code layout.data (cell, choice))
      simpa [PureRun, WritesCode, footprint, decode, Address.eval] using code

theorem address_components (source : Four.State) (base offset : Four.Register) (p : Nat × Bool)
    (valid : Four.address source base offset = some p) :
    source.registers base = .address p.1 ∧ source.registers offset = .offset p.2 := by
  cases hb : source.registers base with
  | offset choice => simp [Four.address, hb] at valid
  | address cell =>
    cases ho : source.registers offset with
    | address other => simp [Four.address, hb, ho] at valid
    | offset choice =>
      have equal : (cell, choice) = p := by simpa [Four.address, hb, ho] using valid
      cases equal
      exact ⟨rfl, rfl⟩

/-- Every successful source MOV is implemented by a pure effect block.
This result is deliberately conditional on source success; fault reflection
requires the separate control guard and offset-safety proof. -/
theorem instruction_correct (layout : OperandLayout) (wordBytes : Int)
    (instruction : Four.Instruction) (source next : Four.State) (target : State)
    (rep : Rep layout source target) (success : Four.execute instruction source = some next) :
    Rep layout next (run wordBytes (compileInstruction layout instruction) target) ∧
    PureRun (Code layout) wordBytes (compileInstruction layout instruction) target := by
  cases instruction with
  | immediate destination value =>
    simp only [Four.execute, Option.some.injEq] at success
    subst next
    exact immediate_correct layout wordBytes source target destination value rep
  | load destination base offset =>
    cases valid : Four.address source base offset with
    | none => simp [Four.execute, valid] at success
    | some p =>
      simp only [Four.execute, valid, Option.some.injEq] at success
      subst next
      have parts := address_components source base offset p valid
      exact load_correct layout wordBytes source target destination base offset p.1 p.2 rep parts.1 parts.2
  | store base offset valueRegister =>
    cases valid : Four.address source base offset with
    | none => simp [Four.execute, valid] at success
    | some p =>
      simp only [Four.execute, valid, Option.some.injEq] at success
      subst next
      have parts := address_components source base offset p valid
      exact store_correct layout wordBytes source target base offset valueRegister p.1 p.2 rep parts.1 parts.2

@[expose] def compile (layout : OperandLayout) (program : List Four.Instruction) : List Header :=
  program.flatMap (compileInstruction layout)

theorem compile_run (layout : OperandLayout) (wordBytes : Int) (program : List Four.Instruction)
    (source next : Four.State) (target : State) (rep : Rep layout source target)
    (success : Four.run program source = some next) :
    Rep layout next (run wordBytes (compile layout program) target) ∧
    PureRun (Code layout) wordBytes (compile layout program) target := by
  induction program generalizing source target with
  | nil =>
    simp only [Four.run, Option.some.injEq] at success
    subst next
    exact ⟨rep, trivial⟩
  | cons instruction rest ih =>
    cases first : Four.execute instruction source with
    | none => simp [Four.run, first] at success
    | some middle =>
      have firstProof := instruction_correct layout wordBytes instruction source middle target rep first
      have restSuccess : Four.run rest middle = some next := by simpa [Four.run, first] using success
      have restProof := ih middle (run wordBytes (compileInstruction layout instruction) target) firstProof.1 restSuccess
      simp only [compile, List.flatMap_cons, run_append, pure_append]
      exact ⟨restProof.1, firstProof.2, restProof.2⟩

end SmcTuring.SMC.Lowering
