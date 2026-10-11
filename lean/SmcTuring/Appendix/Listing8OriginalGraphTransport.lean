module
public import SmcTuring.Appendix.Listing8JointOriginalGraphInput

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphTransport
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets

theorem compatible (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8MainCatalogTransport.Allowed mode origin l address count) :
    Listing8OwnerPointerFrames.CompatibleAll mode (Listing8OriginalGraphCatalog.catalog mode origin g) address count := by
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have ending:=(coordinates mode l).2.2
  have before:=Listing8InputCrossCatalogFields.cursor_before_second mode l
  have last:=Listing8PointerCopies.cursor_before_patch mode l
  change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l at last
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have order:=Listing8GlobalControlLayout.ordered mode origin
  intro template member
  have late:=Listing8OriginalGraphInputFields.lower mode origin g template member
  right;left
  rcases allowed with early | body | firstCursor | secondCursor <;> omega

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory)
    (allowed : Listing8MainCatalogTransport.Allowed mode origin l address packet.length) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (ByteMemory.putBytes memory address packet) :=
  Listing8OwnerPointerFrames.store mode _ memory address packet initial
    (compatible mode origin l t g node rule ctx address packet.length allowed)

theorem head_allowed (mode : Mode) (origin : Nat) (l : Layout) (address count : Nat)
    (allowed : Listing8HeadStoreFields.Allowed mode origin l address count) :
    Listing8MainCatalogTransport.Allowed mode origin l address count := by
  have order:=Listing8GlobalControlLayout.ordered mode origin
  rcases allowed with body | cursor
  · exact Or.inr (Or.inl ⟨body.1,by omega⟩)
  · exact Or.inr (Or.inr (Or.inl cursor))

end SmcTuring.Appendix.Listing8OriginalGraphTransport
