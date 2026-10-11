module
public import SmcTuring.Native.DwordPacketTemplateRuns
public import SmcTuring.Native.StringDwordSequence

public section
namespace SmcTuring.Native.MixedSequenceTemplateRuns

theorem forms (mode : Mode) (layouts : List DwordLayout.Layout) :
    ((DwordMixedSequence.program mode layouts).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)=
      (StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode) := by
  induction layouts with
  | nil => rfl
  | cons layout rest ih =>
    simp only [DwordMixedSequence.program,StringDwordSequence.program,List.flatMap_cons,List.map_append] at ih ⊢
    rw [ih]
    cases mode <;> rfl

theorem all_states (mode : Mode) (templates : List DwordTemplateCollection.Template)
    (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : DwordMixedSequence.Contiguous mode start layouts)
    (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (fields : ∀ layout∈layouts,DwordTemplateCollection.CompatibleAll templates layout.source 4 ∧
      DwordTemplateCollection.CompatibleAll templates layout.destination 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (intact : DwordTemplateCollection.All templates state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => DwordTemplateCollection.All templates reached.principal.memory)
      ((StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  have actual := DwordTemplateCollection.all_states mode templates (DwordMixedSequence.program mode layouts) state intact
    (MixedFieldOwnership.sequence mode layouts start chain valid _ fields state.principal entry)
  rw [forms] at actual
  exact actual

theorem fixed_states (mode : Mode) (templates : List (MixedFixedTemplates.Entry mode))
    (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : DwordMixedSequence.Contiguous mode start layouts)
    (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (fields : ∀ layout∈layouts,MixedFixedTemplates.OutsideAll mode templates layout.source 4 ∧
      MixedFixedTemplates.OutsideAll mode templates layout.destination 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (intact : MixedFixedTemplates.All mode templates state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => MixedFixedTemplates.All mode templates reached.principal.memory)
      ((StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  have actual := MixedFixedTemplates.all_states mode templates (DwordMixedSequence.program mode layouts) state intact
    (MixedFieldOwnership.sequence mode layouts start chain valid _ fields state.principal entry)
  rw [forms] at actual
  exact actual

end SmcTuring.Native.MixedSequenceTemplateRuns
