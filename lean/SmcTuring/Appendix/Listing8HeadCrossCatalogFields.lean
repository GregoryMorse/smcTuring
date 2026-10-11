module
public import SmcTuring.Appendix.Listing8HeadStoreFields
public import SmcTuring.Appendix.Listing8InputCatalogInitial

public section
namespace SmcTuring.Appendix.Listing8HeadCrossCatalogFields
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (_ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8HeadStoreFields.Allowed mode origin l address count) :
    DwordTemplateCollection.CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  rcases allowed with body | cursor
  · exact Listing8RetargetOwnerFields.after_code mode l _ _ body.1
  · apply Listing8RetargetPointerFields.before_patch
    have before:=Listing8InputCrossCatalogFields.cursor_before_second mode l
    have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change secondStart mode l≤patchStart mode l at second
    omega

theorem macros_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8MacroPointerFrames.Property mode l memory)
    (allowed : Listing8HeadStoreFields.Allowed mode origin l address packet.length) :
    Listing8MacroPointerFrames.Property mode l (ByteMemory.putBytes memory address packet) := by
  rcases allowed with body | cursor
  · exact Listing8InputCrossCatalogFields.macros_store mode origin l t g node rule ctx memory address packet initial (Or.inl body)
  · exact ⟨StringMacroTemplates.operand_store mode _ memory address packet initial.1 (Or.inl cursor),
      StringMacroTemplates.frame mode _ memory address packet initial.2 (Or.inl (cursor.2.trans (Listing8InputCrossCatalogFields.cursor_before_second mode l)))⟩

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8HeadStoreFields.Allowed mode origin l address count) :
    Listing8OwnerPointerFrames.CompatibleAll mode
      (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) address count := by
  rcases allowed with body | cursor
  · exact Listing8InputCrossCatalogFields.owners mode origin l t g node rule ctx address count (Or.inl body)
  · have ordering:=Listing8GlobalControlLayout.ordered mode origin
    have before:=Listing8InputCrossCatalogFields.cursor_before_second mode l
    have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change secondStart mode l≤patchStart mode l at second
    have ending:=(coordinates mode l).2.2
    have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
    intro template member
    have bounds:=Listing8OwnerPointerFrames.ranges mode origin l t g node rule ctx template member
    right;left
    rcases bounds with localBounds | later <;> omega

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) memory)
    (allowed : Listing8HeadStoreFields.Allowed mode origin l address packet.length) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) (ByteMemory.putBytes memory address packet) :=
  ⟨DwordTemplateCollection.store_all _ memory address packet initial.1 (retarget mode origin l t g node rule ctx address packet.length allowed),
    macros_store mode origin l t g node rule ctx memory address packet initial.2.1 allowed,
    Listing8OwnerPointerFrames.store mode _ memory address packet initial.2.2 (owners mode origin l t g node rule ctx address packet.length allowed)⟩

end SmcTuring.Appendix.Listing8HeadCrossCatalogFields
