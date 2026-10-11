module
public import SmcTuring.Appendix.Listing8RetargetOwnerFields
public import SmcTuring.Native.CopyStoreRegions

public section
namespace SmcTuring.Appendix.Listing8RetargetPointerFields
open Native Listing8CopyImage Listing8Prototypes DwordTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets

theorem before_patch (mode : Mode) (l : Layout) (address count : Nat) (before : address+count≤patchStart mode l) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  intro template member
  have bound:=Listing8RetargetExecutableTemplates.bounds mode (patchLayout mode l) template member
  exact Or.inr (Or.inl (before.trans bound.1))

theorem word_fields (mode : Mode) (l : Layout) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) (Listing8PointerCopies.word mode l).source mode.wordBytes ∧
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) (Listing8PointerCopies.word mode l).destination mode.wordBytes := by
  constructor
  · intro template member
    cases mode <;>
      simp only [Listing8RetargetExecutableTemplates.templates,Listing8ModeOffsets.sites,List.map_cons,List.map_nil,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals simp only [Compatible,field,width,start,span,Listing8PointerCopies.word,pointerField,
      transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
      currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan,pointerSpan,
      ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
    all_goals omega
  · exact before_patch mode l _ _ (Listing8PointerCopies.cursor_before_patch mode l)

theorem dword_sources (mode : Mode) (l : Layout) (t : Targets) (lay : DwordLayout.Layout)
    (member : lay∈Listing8PointerCopies.layouts mode l t) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) lay.source 4 := by
  cases mode <;> simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  · rcases member with rfl | rfl | rfl
    all_goals intro template inside
    all_goals simp only [Listing8RetargetExecutableTemplates.templates,Listing8ModeOffsets.sites,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inside
    all_goals rcases inside with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals simp only [Compatible,field,width,start,span,pointerField,nodeParams,transitionParams,patchLayout,
      Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,backEntry,forwardEntry,stateEntry,currentEntry,newEntry,
      directionEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset]
    all_goals omega
  · rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals intro template inside
    all_goals simp only [Listing8RetargetExecutableTemplates.templates,Listing8ModeOffsets.sites,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inside
    all_goals rcases inside with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals simp only [Compatible,field,width,start,span,pointerField,nodeParams,transitionParams,patchLayout,
      Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,backEntry,forwardEntry,stateEntry,currentEntry,newEntry,
      directionEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset]
    all_goals omega

theorem dword_fields (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t) :
    ∀ lay∈Listing8PointerCopies.layouts mode l t,
      CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) lay.source 4 ∧
      CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) lay.destination 4 := by
  intro lay member
  have lower:=Listing8PointerCopies.destination_after mode l t bounds lay member
  have size:=(Listing8PointerCopies.sizes mode l t).2.1
  exact ⟨dword_sources mode l t lay member,Listing8RetargetOwnerFields.after_code mode l _ _ (by omega)⟩

theorem regions (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)))
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=word_fields mode l
  have first:=CopyStoreRegions.word mode _ (Listing8PointerCopies.word mode l) bounds.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) bounds.wordValid state.principal entry];rfl
  have last:=CopyStoreRegions.sequence mode _ (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t)
    bounds.dwordValid (dword_fields mode l t bounds) _ next
  rw [Listing8PointerCopies.program,List.map_append,StringStoreRegions.append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8RetargetPointerFields
