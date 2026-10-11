module
public import SmcTuring.Appendix.Listing8InputStoreFields
public import SmcTuring.Appendix.Listing8OwnerPointerFrames

public section
namespace SmcTuring.Appendix.Listing8InputCrossCatalogFields
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem cursor_before_second (mode : Mode) (l : Layout) :
    StringCodec.sourceField mode l.start+mode.wordBytes≤secondStart mode l := by
  have fields:=StringMacroLayout.field_coordinates mode (nodeParams mode l)
  change l.start≤StringCodec.sourceField mode l.start ∧
    StringCodec.sourceField mode l.start+mode.wordBytes≤StringCodec.destinationField mode l.start ∧ _ at fields
  have destinationEnd:=fields.2.2.1
  change StringCodec.destinationField mode l.start+mode.wordBytes≤_ at destinationEnd
  change StringCodec.sourceField mode l.start+mode.wordBytes≤StringMacroLayout.endpoint mode (nodeParams mode l)
  omega

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8InputStoreFields.Allowed mode origin l address count) :
    DwordTemplateCollection.CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  rcases allowed with body | ⟨rfl,small⟩ | ⟨rfl,small⟩
  · exact Listing8RetargetOwnerFields.after_code mode l _ _ body.1
  · apply Listing8RetargetPointerFields.before_patch
    have before:=cursor_before_second mode l
    have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change secondStart mode l≤patchStart mode l at second
    omega
  · exact Listing8RetargetOwnerFields.after_code mode l _ _ (by omega)

theorem macros_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8MacroPointerFrames.Property mode l memory)
    (allowed : Listing8InputStoreFields.Allowed mode origin l address packet.length) :
    Listing8MacroPointerFrames.Property mode l (ByteMemory.putBytes memory address packet) := by
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have ending:=(coordinates mode l).2.2
  have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  rcases allowed with body | ⟨rfl,small⟩ | ⟨rfl,small⟩
  · apply Listing8MacroPointerFrames.store mode l memory address packet initial
    exact Or.inl (by omega)
  · exact ⟨StringMacroTemplates.operand_store mode _ memory _ packet initial.1
      (Or.inl ⟨Nat.le_refl _,by change StringCodec.sourceField mode l.start+packet.length≤StringCodec.sourceField mode l.start+mode.wordBytes;omega⟩),
      StringMacroTemplates.frame mode _ memory _ packet initial.2 (Or.inl (by
        change StringCodec.sourceField mode l.start+packet.length≤secondStart mode l
        have before:=cursor_before_second mode l;omega))⟩
  · apply Listing8MacroPointerFrames.store mode l memory _ packet initial
    exact Or.inl (by omega)

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8InputStoreFields.Allowed mode origin l address count) :
    Listing8OwnerPointerFrames.CompatibleAll mode
      (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) address count := by
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  rcases allowed with body | ⟨rfl,small⟩ | ⟨rfl,small⟩
  · intro template member
    have bounds:=Listing8OwnerPointerFrames.ranges mode origin l t g node rule ctx template member
    right
    rcases bounds with before | after
    · right;omega
    · left;omega
  · intro template member
    have bounds:=Listing8OwnerPointerFrames.ranges mode origin l t g node rule ctx template member
    have cursor:=cursor_before_second mode l
    have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change secondStart mode l≤patchStart mode l at second
    have ending:=(coordinates mode l).2.2
    have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
    right;left
    rcases bounds with before | after <;> omega
  · have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
    have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
    have nodeAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤l.sourceNode := by
      change codeEnd mode l≤l.sourceNode;omega
    have ruleBefore : l.sourceTransition+transitionSpan mode≤l.sourceNode := by
      rw [ctx.nodeLocated,ctx.ruleLocated]
      exact Listing8GraphLayout.table_node_apart mode origin g.transitions rule.val node.val rule.isLt
    intro template member
    simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
      List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
    all_goals cases mode
    all_goals simp only [Listing8OwnerPointerFrames.Compatible,Listing8OwnerTemplateCollection.field,
      Listing8OwnerTemplateCollection.width,Listing8OwnerTemplateCollection.start,Listing8OwnerTemplateCollection.span,
      pointerField,nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
      backEntry,forwardEntry,stateEntry,currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan,pointerSpan,
      ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
    all_goals simp only [nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at nodeAfter ruleBefore
    all_goals omega

end SmcTuring.Appendix.Listing8InputCrossCatalogFields
