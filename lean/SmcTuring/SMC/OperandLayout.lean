module
public import SmcTuring.SMC.NumericEncoding
public import SmcTuring.SMC.Control

public section

namespace SmcTuring.SMC.Lowering

open Dolan

/-- Active read labels and constant operands are separate from the uniform
source-data template pool. The address operand is mutable scratch. -/
structure OperandLayout where
  data : Layout
  registerLabel : Four.Register → Int
  constantLabel : Mov.Word → Int
  constantField : Mov.Word → Int
  pointer : Int
  registerLabelOutside : ∀ r, ¬ codeField data (registerLabel r)
  constantLabelOutside : ∀ value, ¬ codeField data (constantLabel value)
  constantFieldOutside : ∀ value, ¬ codeField data (constantField value)
  pointerOutside : ¬ codeField data pointer
  pointerRegisterLabel : ∀ r, registerLabel r ≠ pointer
  pointerConstantLabel : ∀ value, constantLabel value ≠ pointer
  pointerConstantField : ∀ value, constantField value ≠ pointer

@[expose] def Code (layout : OperandLayout) (field : Int) : Prop :=
  codeField layout.data field ∨ field = layout.pointer ∨
    (∃ r, field = layout.registerLabel r) ∨
    (∃ value, field = layout.constantLabel value ∨ field = layout.constantField value)

theorem data_code (layout : OperandLayout) (field : Int) (code : codeField layout.data field) :
    Code layout field := Or.inl code

theorem pointer_code (layout : OperandLayout) : Code layout layout.pointer := Or.inr (Or.inl rfl)

theorem register_label_code (layout : OperandLayout) (r : Four.Register) : Code layout (layout.registerLabel r) :=
  Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))

theorem constant_label_code (layout : OperandLayout) (value : Mov.Word) : Code layout (layout.constantLabel value) :=
  Or.inr (Or.inr (Or.inr ⟨value, Or.inl rfl⟩))

theorem constant_field_code (layout : OperandLayout) (value : Mov.Word) : Code layout (layout.constantField value) :=
  Or.inr (Or.inr (Or.inr ⟨value, Or.inr rfl⟩))

@[expose] def StaticRep (layout : OperandLayout) (target : State) : Prop :=
  (∀ r, target.memory (layout.registerLabel r) = registerField layout.data r) ∧
  (∀ value, target.memory (layout.constantLabel value) = layout.constantField value) ∧
  (∀ value, target.memory (layout.constantField value) = encodeWord layout.data value)

@[expose] def Rep (layout : OperandLayout) (source : Four.State) (target : State) : Prop :=
  NumericRep layout.data source target ∧ StaticRep layout target

theorem static_write_frame (layout : OperandLayout) (target : State) (field value : Int)
    (rep : StaticRep layout target)
    (registerLabels : ∀ r, layout.registerLabel r ≠ field)
    (constantLabels : ∀ word, layout.constantLabel word ≠ field)
    (constantFields : ∀ word, layout.constantField word ≠ field) :
    StaticRep layout { target with memory := write target.memory field value } := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa [write, registerLabels r] using rep.1 r
  · intro word
    simpa [write, constantLabels word] using rep.2.1 word
  · intro word
    simpa [write, constantFields word] using rep.2.2 word

theorem static_data_write (layout : OperandLayout) (target : State) (field value : Int)
    (rep : StaticRep layout target) (data : codeField layout.data field) :
    StaticRep layout { target with memory := write target.memory field value } := by
  apply static_write_frame layout target field value rep
  · intro r
    exact Ne.symm (data_field_separate layout.data _ _ (layout.registerLabelOutside r) data)
  · intro word
    exact Ne.symm (data_field_separate layout.data _ _ (layout.constantLabelOutside word) data)
  · intro word
    exact Ne.symm (data_field_separate layout.data _ _ (layout.constantFieldOutside word) data)

theorem pointer_rep (layout : OperandLayout) (source : Four.State) (target : State) (value : Int)
    (rep : Rep layout source target) :
    Rep layout source { target with memory := write target.memory layout.pointer value } := by
  constructor
  · apply metadata_write_frame layout.data source target layout.pointer value rep.1
    · intro r
      exact data_field_separate layout.data _ _ layout.pointerOutside (register_is_code layout.data r)
    · intro p
      exact data_field_separate layout.data _ _ layout.pointerOutside (heap_is_code layout.data p)
  · exact static_write_frame layout target layout.pointer value rep.2
      layout.pointerRegisterLabel layout.pointerConstantLabel layout.pointerConstantField

theorem register_rep (layout : OperandLayout) (source : Four.State) (target : State)
    (r : Four.Register) (word : Mov.Word) (rep : Rep layout source target) :
    Rep layout { source with registers := write source.registers r word }
      { target with memory := write target.memory (registerField layout.data r) (encodeWord layout.data word) } :=
  ⟨register_write_rep layout.data source target r word rep.1,
   static_data_write layout target _ _ rep.2 (register_is_code layout.data r)⟩

theorem heap_rep (layout : OperandLayout) (source : Four.State) (target : State)
    (p : Nat × Bool) (word : Mov.Word) (rep : Rep layout source target) :
    Rep layout { source with memory := write source.memory p word }
      { target with memory := write target.memory (heapField layout.data p) (encodeWord layout.data word) } :=
  ⟨heap_write_rep layout.data source target p word rep.1,
   static_data_write layout target _ _ rep.2 (heap_is_code layout.data p)⟩

end SmcTuring.SMC.Lowering
