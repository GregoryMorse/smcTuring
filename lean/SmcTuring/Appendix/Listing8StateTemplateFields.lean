module
public import SmcTuring.Native.MixedSequenceTemplateRuns
public import SmcTuring.Appendix.Listing8StateTrace

public section
namespace SmcTuring.Appendix.Listing8StateTemplateFields
open Native Listing8StateLayout

@[expose] def arithmetic (mode : Mode) (layout : Layout) := (packets mode layout).map DwordPacketTemplateRuns.template
@[expose] def fixed (mode : Mode) (layout : Layout) := (helpers mode layout).flatMap (MixedFixedTemplates.copyEntries mode)
@[expose] def Allowed (mode : Mode) (layout : Layout) (address : Nat) : Prop :=
  address+4≤layout.start ∨ address=updatePC mode layout+6 ∨ (mode=.x64 ∧ address=updatePC mode layout+16)

theorem arithmetic_bounds (mode : Mode) (layout : Layout) (descriptor : DwordTemplateCollection.Template)
    (member : descriptor∈arithmetic mode layout) :
    layout.start≤DwordTemplateCollection.start descriptor ∧
      DwordTemplateCollection.start descriptor+DwordTemplateCollection.span descriptor≤endPC mode layout := by
  cases mode
  all_goals simp only [arithmetic,packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.map_append,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.start,DwordTemplateCollection.span,
    endPC,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem fixed_bounds (mode : Mode) (layout : Layout) (descriptor : MixedFixedTemplates.Entry mode)
    (member : descriptor∈fixed mode layout) :
    layout.start≤descriptor.pc ∧ descriptor.pc+MixedFixedTemplates.span mode descriptor≤newPC mode layout := by
  rcases List.mem_flatMap.mp member with ⟨helper,inside,packet⟩
  have range := MixedFixedTemplates.copy_bounds mode helper descriptor packet
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at inside
  all_goals rcases inside with rfl | rfl
  all_goals simp [newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,DwordLayout.thirdPC,
    DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize] at range ⊢;omega

theorem compatible (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    DwordTemplateCollection.CompatibleAll (arithmetic mode layout) address 4 := by
  intro descriptor member
  rcases allowed with before | rfl | ⟨long,rfl⟩
  · have range := arithmetic_bounds mode layout descriptor member
    exact Or.inr (Or.inl (by omega))
  · cases mode
    all_goals simp only [arithmetic,packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
      DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,
      updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]
  · subst mode
    simp only [arithmetic,packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
        DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,
        updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]

theorem frames (mode : Mode) (layout : Layout) (address : Nat) (allowed : Allowed mode layout address) :
    MixedFixedTemplates.OutsideAll mode (fixed mode layout) address 4 := by
  intro descriptor member
  have range := fixed_bounds mode layout descriptor member
  rcases allowed with before | rfl | ⟨long,rfl⟩
  · exact Or.inl (by omega)
  · right
    simp only [updatePC,maskPC] at *
    omega
  · right
    simp only [updatePC,maskPC] at *
    omega

theorem helper_fields (mode : Mode) (layout : Layout) (bounds : Listing8StateBounds.Bounds mode layout) :
    ∀ helper∈helpers mode layout,Allowed mode layout helper.source ∧ Allowed mode layout helper.destination := by
  intro helper member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Allowed,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,
    DwordLayout.storeSize,Mode.wordBytes] at before ⊢
  all_goals omega

theorem packet_fields (mode : Mode) (layout : Layout) (bounds : Listing8StateBounds.Bounds mode layout) :
    ∀ site∈packets mode layout,Allowed mode layout site.target := by
  intro site member
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Allowed,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,
    DwordLayout.storeSize,Mode.wordBytes] at before ⊢
  all_goals omega

end SmcTuring.Appendix.Listing8StateTemplateFields
