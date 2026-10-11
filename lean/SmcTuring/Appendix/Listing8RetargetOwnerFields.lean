module
public import SmcTuring.Appendix.Listing8OwnerStoreRegions
public import SmcTuring.Appendix.Listing8RetargetTapeTemplates
public import SmcTuring.Appendix.Listing8GlobalMainOwnerRegions

public section
namespace SmcTuring.Appendix.Listing8RetargetOwnerFields
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes DwordTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets

theorem after_code (mode : Mode) (l : Layout) (address count : Nat) (after : codeEnd mode l≤address) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  intro template member
  have bound:=Listing8RetargetExecutableTemplates.bounds mode (patchLayout mode l) template member
  exact Or.inr (Or.inr (bound.2.trans after))

theorem copied_self_x64 (l : Layout) (v : Values .x64) (source copied : Nat) (value : Word .x64)
    (member : Listing8OwnerSequence.Owner.pointer source copied value∈Listing8OwnerImage.owners .x64 l v) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates .x64 (patchLayout .x64 l))
      (Listing8CopiedPointer.selfField .x64 source copied) Mode.x64.wordBytes := by
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h <;> cases h
  all_goals intro template inside
  all_goals simp only [Listing8RetargetExecutableTemplates.templates,Listing8ModeOffsets.sites,List.map_cons,List.map_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inside
  all_goals rcases inside with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  all_goals simp only [Compatible,field,width,start,span,Listing8CopiedPointer.selfField,Listing8CopiedPointer.origin,pointerField,
    nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
    backEntry,forwardEntry,stateEntry,currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan,pointerSpan,
    ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes,reduceCtorEq,ite_false]
  all_goals omega

theorem self (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (source copied : Nat) (value : Word mode)
    (member : Listing8OwnerSequence.Owner.pointer source copied value∈Listing8OwnerImage.owners mode l (values mode origin g node rule)) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))
      (Listing8CopiedPointer.selfField mode source copied) mode.wordBytes := by
  cases mode with
  | x64 => exact copied_self_x64 l _ source copied value member
  | x86 =>
    have originals:=Listing8GlobalMainBounds.originals .x86 origin l t g node rule ctx
    have main:=Listing8GlobalMainBounds.copy .x86 origin l t g node rule ctx
    have ordered:=Listing8GlobalControlLayout.ordered .x86 origin
    simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h <;> cases h
    all_goals apply after_code
    all_goals simp only [Listing8CopiedPointer.selfField,Listing8CopiedPointer.origin,pointerField,backEntry,forwardEntry,stateEntry,
      pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset,currentEntry,newEntry,directionEntry,ite_true]
    all_goals omega

theorem target_words (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (word : Word mode) (member : word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) word.toNat mode.wordBytes := by
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have late : StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin)
      (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) word := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).back ctx.native
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).forward ctx.native
    · exact Listing8LateGraphFieldBounds.next_word mode origin g rule ctx.native
    · exact Listing8LateGraphFieldBounds.state_word mode origin g (g.rules rule).destination ctx.native
  apply after_code
  have lower:=late.1
  omega

theorem scalar_targets (mode : Mode) (l : Layout) (t : Targets)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (resources : Resources mode l) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) (Listing8LiteralInput.scalarField mode l.input) 4 ∧
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) (Listing8LiteralInput.updateStart mode l.input+6) 4 ∧
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) (l.direction+6) 4 := by
  have before:=resources.inputAfter
  have input:=Listing8LiteralInput.positions mode l.input
  have direction:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
  have located:=bounds.direction
  have ending:=input.2.2.2.2.2.2.2
  change Listing8LiteralInput.endPC mode l.input=_ at ending
  have directionAt:=direction.2.2.2.2.2.2.1
  change Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)=Listing8LiteralInput.endPC mode l.input+_ at directionAt
  refine ⟨after_code mode l _ _ ?_,after_code mode l _ _ ?_,after_code mode l _ _ ?_⟩
  · rw [input.2.1];omega
  · rw [input.2.2.2.2.1];omega
  · rw [located,directionAt];cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega

theorem placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),
      Listing8OwnerStoreRegions.Placement mode (CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))) owner := by
  intro owner member
  have fields:=scalar_targets mode l t ctx.body.state.head ctx.resources
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨self mode origin l t g node rule ctx _ _ (values mode origin g node rule).back (by simp [Listing8OwnerImage.owners]),target_words mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨self mode origin l t g node rule ctx _ _ (values mode origin g node rule).forward (by simp [Listing8OwnerImage.owners]),target_words mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨self mode origin l t g node rule ctx _ _ (values mode origin g node rule).next (by simp [Listing8OwnerImage.owners]),target_words mode origin l t g node rule ctx _ (by simp)⟩
  · exact fields.1
  · exact fields.2.1
  · exact fields.2.2
  · exact ⟨self mode origin l t g node rule ctx _ _ (values mode origin g node rule).newState (by simp [Listing8OwnerImage.owners]),target_words mode origin l t g node rule ctx _ (by simp)⟩

end SmcTuring.Appendix.Listing8RetargetOwnerFields
