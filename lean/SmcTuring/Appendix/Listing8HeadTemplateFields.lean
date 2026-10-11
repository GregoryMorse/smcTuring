module
public import SmcTuring.Native.DwordXorTemplates
public import SmcTuring.Appendix.Listing8HeadTailTrace

public section
namespace SmcTuring.Appendix.Listing8HeadTemplateFields
open Native Listing8DirectionLayout Listing8HeadTailBounds

@[expose] def sites (mode : Mode) (layout : Layout) := masks mode layout++heads mode layout
@[expose] def arithmetic (mode : Mode) (layout : Layout) := (sites mode layout).map DwordPacketTemplateRuns.template
@[expose] def Allowed (mode : Mode) (layout : Layout) (address : Nat) : Prop :=
  address+4≤layout.start ∨ address=directionPC mode layout+6 ∨ (mode=.x64 ∧ address=directionPC mode layout+16)

theorem arithmetic_bounds (mode : Mode) (layout : Layout) (descriptor : DwordTemplateCollection.Template)
    (member : descriptor∈arithmetic mode layout) :
    layout.start≤DwordTemplateCollection.start descriptor ∧
      DwordTemplateCollection.start descriptor+DwordTemplateCollection.span descriptor≤endPC mode layout := by
  cases mode
  all_goals simp only [arithmetic,sites,masks,heads,group,List.map_append,List.map_cons,List.map_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.start,DwordTemplateCollection.span,
    endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize];omega

theorem xor_bounds (mode : Mode) (layout : Layout) (helper : DwordXorHelper.Layout)
    (member : helper∈xorLayouts mode layout) :
    layout.start≤helper.start ∧ helper.start+18≤maskPC mode layout := by
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize];omega

theorem compatible (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    DwordTemplateCollection.CompatibleAll (arithmetic mode layout) address 4 := by
  intro descriptor member
  rcases allowed with before | rfl | ⟨long,rfl⟩
  · have range := arithmetic_bounds mode layout descriptor member
    exact Or.inr (Or.inl (by omega))
  · cases mode
    all_goals simp only [arithmetic,sites,masks,heads,group,List.map_append,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
      DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,directionPC,
      maskPC,halves,Listing8PointerCopies.halfCount]
  · subst mode
    simp only [arithmetic,sites,masks,heads,group,List.map_append,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
        DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,directionPC,
        maskPC,halves,Listing8PointerCopies.halfCount]

theorem frames (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    DwordXorTemplates.OutsideAll (xorLayouts mode layout) address 4 := by
  intro helper member
  have range := xor_bounds mode layout helper member
  rcases allowed with before | rfl | ⟨long,rfl⟩
  · exact Or.inl (by omega)
  · right
    simp only [directionPC] at *
    omega
  · right
    simp only [directionPC] at *
    omega

theorem helper_fields (mode : Mode) (layout : Layout) (bounds : Bounds mode layout) :
    ∀ helper∈xorLayouts mode layout,Allowed mode layout helper.source ∧ Allowed mode layout helper.destination := by
  intro helper member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Allowed,Mode.wordBytes] at before ⊢
  all_goals omega

theorem packet_fields (mode : Mode) (layout : Layout) (bounds : Bounds mode layout) :
    ∀ site∈sites mode layout,Allowed mode layout site.target := by
  intro site member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [sites,masks,heads,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Allowed,Mode.wordBytes] at before ⊢
  all_goals omega

end SmcTuring.Appendix.Listing8HeadTemplateFields
