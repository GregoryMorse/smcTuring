module
public import SmcTuring.Appendix.Listing8HeadCrossCatalogFields

public section
namespace SmcTuring.Appendix.Listing8MainCatalogTransport
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def Allowed (mode : Mode) (origin : Nat) (l : Layout) (address count : Nat) : Prop :=
  address+count≤l.start ∨
    (codeEnd mode l≤address ∧ address+count≤Listing8FullTableImage.start mode origin) ∨
    (StringCodec.sourceField mode l.start≤address ∧ address+count≤StringCodec.sourceField mode l.start+mode.wordBytes) ∨
    (StringCodec.sourceField mode (secondStart mode l)≤address ∧ address+count≤StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes)

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (address count : Nat)
    (allowed : Allowed mode origin l address count) :
    DwordTemplateCollection.CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have cursor:=Listing8InputCrossCatalogFields.cursor_before_second mode l
  have last:=Listing8PointerCopies.cursor_before_patch mode l
  change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l at last
  rcases allowed with early | body | firstCursor | secondCursor
  · exact Listing8RetargetPointerFields.before_patch mode l _ _ (by omega)
  · exact Listing8RetargetOwnerFields.after_code mode l _ _ body.1
  · exact Listing8RetargetPointerFields.before_patch mode l _ _ (by omega)
  · exact Listing8RetargetPointerFields.before_patch mode l _ _ (secondCursor.2.trans last)

theorem macros_store (mode : Mode) (origin : Nat) (l : Layout) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (initial : Listing8MacroPointerFrames.Property mode l memory)
    (allowed : Allowed mode origin l address packet.length) :
    Listing8MacroPointerFrames.Property mode l (ByteMemory.putBytes memory address packet) := by
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have ending:=(coordinates mode l).2.2
  rcases allowed with early | body | firstCursor | secondCursor
  · exact ⟨StringMacroTemplates.frame mode _ memory address packet initial.1 (Or.inl early),
      StringMacroTemplates.frame mode _ memory address packet initial.2 (Or.inl (early.trans first))⟩
  · apply Listing8MacroPointerFrames.store mode l memory address packet initial
    exact Or.inl (by omega)
  · exact ⟨StringMacroTemplates.operand_store mode _ memory address packet initial.1 (Or.inl firstCursor),
      StringMacroTemplates.frame mode _ memory address packet initial.2
        (Or.inl (firstCursor.2.trans (Listing8InputCrossCatalogFields.cursor_before_second mode l)))⟩
  · have after : secondStart mode l≤address := by
      have bound : secondStart mode l≤StringCodec.sourceField mode (secondStart mode l) := by unfold StringCodec.sourceField;omega
      exact bound.trans secondCursor.1
    exact ⟨StringMacroTemplates.frame mode _ memory address packet initial.1 (Or.inr after),
      StringMacroTemplates.operand_store mode _ memory address packet initial.2 (Or.inl secondCursor)⟩

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Allowed mode origin l address count) :
    Listing8OwnerPointerFrames.CompatibleAll mode
      (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) address count := by
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have cursor:=Listing8InputCrossCatalogFields.cursor_before_second mode l
  have last:=Listing8PointerCopies.cursor_before_patch mode l
  change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l at last
  have ending:=(coordinates mode l).2.2
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  intro template member
  have bounds:=Listing8OwnerPointerFrames.ranges mode origin l t g node rule ctx template member
  rcases allowed with early | body | firstCursor | secondCursor
  · right;left;rcases bounds with localBounds | later <;> omega
  · right;rcases bounds with before | after
    · right;omega
    · left;exact body.2.trans after
  · right;left;rcases bounds with localBounds | later <;> omega
  · right;left;rcases bounds with localBounds | later <;> omega

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) memory)
    (allowed : Allowed mode origin l address packet.length) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) (ByteMemory.putBytes memory address packet) :=
  ⟨DwordTemplateCollection.store_all _ memory address packet initial.1 (retarget mode origin l address packet.length allowed),
    macros_store mode origin l memory address packet initial.2.1 allowed,
    Listing8OwnerPointerFrames.store mode _ memory address packet initial.2.2 (owners mode origin l t g node rule ctx address packet.length allowed)⟩

end SmcTuring.Appendix.Listing8MainCatalogTransport
