module
public import SmcTuring.Appendix.Listing8HeadExecutableTemplates

public section
namespace SmcTuring.Appendix.Listing8DirectionTemplateFields
open Native Listing8DirectionLayout Listing8HeadTailBounds

@[expose] def sites (mode : Mode) (layout : Layout) :=
  Listing8DirectionLayout.arithmetic mode layout++masks mode layout++heads mode layout
@[expose] def templates (mode : Mode) (layout : Layout) := (sites mode layout).map DwordPacketTemplateRuns.template
@[expose] def fixed (mode : Mode) (layout : Layout) := (helpers mode layout).flatMap (MixedFixedTemplates.copyEntries mode)
@[expose] def Allowed (mode : Mode) (layout : Layout) (address : Nat) : Prop :=
  address+4≤layout.start ∨ address=combinedPC mode layout+6 ∨ (mode=.x64 ∧ address=combinedPC mode layout+16) ∨
    address=directionPC mode layout+6 ∨ (mode=.x64 ∧ address=directionPC mode layout+16)

theorem template_bounds (mode : Mode) (layout : Layout) (descriptor : DwordTemplateCollection.Template)
    (member : descriptor∈templates mode layout) :
    layout.start≤DwordTemplateCollection.start descriptor ∧
      DwordTemplateCollection.start descriptor+DwordTemplateCollection.span descriptor≤endPC mode layout := by
  cases mode
  all_goals simp only [templates,sites,Listing8DirectionLayout.arithmetic,masks,heads,group,List.map_append,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.start,DwordTemplateCollection.span,
    DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,endPC,directionPC,maskPC,
    selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem fixed_bounds (mode : Mode) (layout : Layout) (descriptor : MixedFixedTemplates.Entry mode)
    (member : descriptor∈fixed mode layout) :
    layout.start≤descriptor.pc ∧ descriptor.pc+MixedFixedTemplates.span mode descriptor≤backPC mode layout := by
  rcases List.mem_flatMap.mp member with ⟨helper,inside,packet⟩
  have range := MixedFixedTemplates.copy_bounds mode helper descriptor packet
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at inside
  all_goals rcases inside with rfl | rfl | rfl
  all_goals simp [backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,
    DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize] at range ⊢;omega

theorem compatible (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    DwordTemplateCollection.CompatibleAll (templates mode layout) address 4 := by
  intro descriptor member
  have before_case (before : address+4≤layout.start) : DwordTemplateCollection.Compatible descriptor address 4 :=
    Or.inr (Or.inl (by have range := template_bounds mode layout descriptor member;omega))
  cases mode
  · simp only [Allowed,reduceCtorEq,false_and,or_false,false_or] at allowed
    rcases allowed with before | rfl | rfl
    · exact before_case before
    all_goals simp only [templates,sites,Listing8DirectionLayout.arithmetic,masks,heads,group,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
      DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,DwordUnaryTemplates.span,
      DwordUnaryTemplates.field,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,directionPC,maskPC,selectionEnd,
      combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize]
  · simp only [Allowed,true_and] at allowed
    rcases allowed with before | rfl | rfl | rfl | rfl
    · exact before_case before
    all_goals simp only [templates,sites,Listing8DirectionLayout.arithmetic,masks,heads,group,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
      DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,DwordUnaryTemplates.span,
      DwordUnaryTemplates.field,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,directionPC,maskPC,selectionEnd,
      combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize]

theorem fixed_frames (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    MixedFixedTemplates.OutsideAll mode (fixed mode layout) address 4 := by
  intro descriptor member
  have range := fixed_bounds mode layout descriptor member
  rcases allowed with before | rfl | ⟨long,rfl⟩ | rfl | ⟨long,rfl⟩
  · exact Or.inl (by omega)
  all_goals right
  all_goals simp only [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC] at *
  all_goals omega

theorem xor_frames (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    DwordXorTemplates.OutsideAll (xorLayouts mode layout) address 4 := by
  intro helper member
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp only [Allowed,reduceCtorEq,false_and,true_and,or_false,false_or] at allowed
  all_goals rcases allowed with before | rfl | rfl | rfl | rfl
  · left
    simp only [selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart] at *
    omega
  all_goals simp [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]
  all_goals omega

theorem helper_fields (mode : Mode) (layout : Layout) :
    ∀ helper∈helpers mode layout,Allowed mode layout helper.source ∧ Allowed mode layout helper.destination := by
  intro helper member
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp [Allowed]

theorem packet_fields (mode : Mode) (layout : Layout) (bounds : Bounds mode layout) :
    ∀ site∈sites mode layout,Allowed mode layout site.target := by
  intro site member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [sites,Listing8DirectionLayout.arithmetic,masks,heads,group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Allowed,Mode.wordBytes] at before ⊢
  all_goals omega

theorem xor_fields (mode : Mode) (layout : Layout) (bounds : Bounds mode layout) :
    ∀ helper∈xorLayouts mode layout,Allowed mode layout helper.source ∧ Allowed mode layout helper.destination := by
  intro helper member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Allowed,Mode.wordBytes] at before ⊢
  all_goals omega

end SmcTuring.Appendix.Listing8DirectionTemplateFields
