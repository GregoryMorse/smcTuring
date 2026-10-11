module
public import SmcTuring.Appendix.Listing8FailureReuseImage
public import SmcTuring.Native.StringStoreTemplateRuns
public import SmcTuring.Native.DwordXorRegionRuns
public import SmcTuring.Native.RelativeCallTemplate

public section
namespace SmcTuring.Appendix.Listing8FailureTemplateFields
open Native Listing8FailureLayout

@[expose] def arithmetic (mode : Mode) (l : Layout) : List DwordTemplateCollection.Template :=
  .binary .store l.start::(post mode l).map DwordPacketTemplateRuns.template
@[expose] def Allowed (mode : Mode) (l : Layout) (address count : Nat) : Prop :=
  address+count≤l.start ∨ callPC mode l+5≤address ∨
    (source mode l≤address ∧ address+count≤source mode l+mode.wordBytes) ∨
    (mask mode l≤address ∧ address+count≤mask mode l+4) ∨
    (andPC mode l+6≤address ∧ address+count≤andPC mode l+10) ∨
    (callPC mode l+1≤address ∧ address+count≤callPC mode l+5)

theorem arithmetic_bounds (mode : Mode) (l : Layout) (descriptor : DwordTemplateCollection.Template)
    (member : descriptor∈arithmetic mode l) :
    l.start≤DwordTemplateCollection.start descriptor ∧
      DwordTemplateCollection.start descriptor+DwordTemplateCollection.span descriptor≤endPC mode l := by
  simp only [arithmetic,post,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.start,DwordTemplateCollection.span,
    DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,
    endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix]
  all_goals omega

theorem compatible (mode : Mode) (l : Layout) (address count : Nat) (allowed : Allowed mode l address count) :
    DwordTemplateCollection.CompatibleAll (arithmetic mode l) address count := by
  intro descriptor member
  rcases allowed with before | after | owner | maskField | andField | callField
  · exact Or.inr (Or.inl (by have h:=arithmetic_bounds mode l descriptor member;omega))
  · exact Or.inr (Or.inr (by
      have h:=arithmetic_bounds mode l descriptor member
      simp only [callPC,stackSpan] at after
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at after <;> omega))
  all_goals simp only [arithmetic,post,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
    DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,
    DwordUnaryTemplates.span,DwordUnaryTemplates.field,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,
    source,StringInit.field,StringCodec.fieldOffset,mask,endPC,callPC,stackSpan,xorPC,andPC,storePC,notPC,comparisonPC,
    ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Mode.wordBytes] at *
  all_goals omega

theorem comparison_bounds (mode : Mode) (l : Layout) (site : ControlPackets.Site)
    (member : site∈Listing8FailComparison.sites mode (comparison mode l)) :
    comparisonPC mode l≤site.pc ∧ site.pc+ControlPackets.size mode site≤notPC mode l := by
  simp only [Listing8FailComparison.sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [Listing8FailComparison.site,Listing8FailComparison.offset,Listing8FailComparison.operation,
    comparison,ControlPackets.size,WordMemoryArithmetic.size,WordNegation.length,DwordArithmetic.length,wordPrefix,notPC]

theorem comparison_frames (mode : Mode) (l : Layout) (address count : Nat) (allowed : Allowed mode l address count)
    (site : ControlPackets.Site) (member : site∈Listing8FailComparison.sites mode (comparison mode l)) :
    address+count≤site.pc ∨ site.pc+ControlPackets.size mode site≤address := by
  have h:=comparison_bounds mode l site member
  have endpoint:=source_end mode l
  rcases allowed with before | after | owner | maskField | andField | callField
  all_goals cases mode
  all_goals simp [source,StringInit.field,StringCodec.fieldOffset,mask,endPC,callPC,stackSpan,xorPC,andPC,storePC,
    notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Mode.wordBytes] at *
  all_goals omega

theorem owner_frames (mode : Mode) (l : Layout) (address count : Nat) (allowed : Allowed mode l address count) :
    address+count≤ownerPC l ∨ StringInit.field mode (ownerPC l)≤address := by
  rcases allowed with before | after | owner | maskField | andField | callField
  all_goals cases mode
  all_goals simp [source,StringInit.field,StringCodec.fieldOffset,mask,endPC,callPC,stackSpan,xorPC,andPC,storePC,
    notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Mode.wordBytes] at *
  all_goals omega

theorem call_frames (mode : Mode) (l : Layout) (address count : Nat) (allowed : Allowed mode l address count) :
    address+count≤callPC mode l ∨ callPC mode l+1≤address := by
  rcases allowed with before | after | owner | maskField | andField | callField
  all_goals cases mode
  all_goals simp [source,StringInit.field,StringCodec.fieldOffset,mask,endPC,callPC,stackSpan,xorPC,andPC,storePC,
    notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Mode.wordBytes] at *
  all_goals omega

theorem comparison_fields (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l) :
    ∀ site∈Listing8FailComparison.sites mode (comparison mode l),Allowed mode l site.target (ControlPackets.width mode site) := by
  have before:=bounds.cursorBefore
  intro site member
  simp only [Listing8FailComparison.sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [Allowed,Listing8FailComparison.site,Listing8FailComparison.target,Listing8FailComparison.operation,
    comparison,ControlPackets.width,Mode.wordBytes] at before ⊢
  all_goals omega

theorem post_fields (mode : Mode) (l : Layout) : ∀ site∈post mode l,Allowed mode l site.target 4 := by
  intro site member
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Allowed]

end SmcTuring.Appendix.Listing8FailureTemplateFields
