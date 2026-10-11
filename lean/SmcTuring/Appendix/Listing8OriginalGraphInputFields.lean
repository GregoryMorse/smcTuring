module
public import SmcTuring.Appendix.Listing8OriginalGraphCatalog

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphInputFields
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets

theorem lower (mode : Mode) (origin : Nat) (g : Graph) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.catalog mode origin g) :
    Listing8FullTableImage.start mode origin≤start mode template := by
  simp only [Listing8OriginalGraphCatalog.catalog,List.mem_append,List.mem_flatten] at member
  rcases member with ⟨items,inside,selected⟩ | ⟨items,inside,selected⟩
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    have range:=Listing8OriginalGraphCatalog.node_bounds mode _ template selected
    have n:=Listing8GraphLayout.node_lower mode origin g.transitions query.val
    have t:=Listing8GraphLayout.table_before_input mode origin g.transitions
    have first:=Listing8GraphLayout.transition_lower mode origin g.transitions
    change Listing8FullTableImage.start mode origin≤Listing8GraphLayout.reset mode origin g.transitions at first
    change Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g query at n
    omega
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    exact (Listing8GraphLayout.transition_lower mode origin query.val).trans
      (Listing8OriginalGraphCatalog.rule_bounds mode _ template selected).1

theorem node_symbol (mode : Mode) (origin : Nat) (g : Graph) (writer query : Fin g.nodes)
    (count : Nat) (small : count≤4) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.nodeTemplates mode (nodePC mode origin g query)) :
    Listing8OwnerPointerFrames.Compatible mode template (nodePC mode origin g writer+6) count := by
  have range:=Listing8OriginalGraphCatalog.node_bounds mode _ template member
  rcases Nat.lt_trichotomy writer.val query.val with before | same | after
  · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions writer.val query.val before
    change nodePC mode origin g writer+nodeSpan mode≤nodePC mode origin g query at apart
    have span : 10≤nodeSpan mode := by cases mode <;> decide
    right;left;omega
  · have equal : writer=query := Fin.ext same
    subst query
    simp only [Listing8OriginalGraphCatalog.nodeTemplates,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals cases mode <;> simp only [Listing8OwnerPointerFrames.Compatible,field,width,start,span,backEntry,forwardEntry,pointerField,ReaderImage.labelOffset,Mode.wordBytes,pointerSpan,ReaderImage.totalSize] <;> omega
  · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions query.val writer.val after
    change nodePC mode origin g query+nodeSpan mode≤nodePC mode origin g writer at apart
    right;right;omega

theorem symbol (mode : Mode) (origin : Nat) (g : Graph) (writer : Fin g.nodes) (count : Nat) (small : count≤4) :
    Listing8OwnerPointerFrames.CompatibleAll mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (nodePC mode origin g writer+6) count := by
  intro template member
  simp only [Listing8OriginalGraphCatalog.catalog,List.mem_append,List.mem_flatten] at member
  rcases member with ⟨items,inside,selected⟩ | ⟨items,inside,selected⟩
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    exact node_symbol mode origin g writer query count small template selected
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    have range:=Listing8OriginalGraphCatalog.rule_bounds mode _ template selected
    have apart:=Listing8GraphLayout.table_node_apart mode origin g.transitions query.val writer.val query.isLt
    change rulePC mode origin g query+transitionSpan mode≤nodePC mode origin g writer at apart
    right;right;omega

theorem allowed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (stores : Listing8InputStoreFields.Allowed mode origin l address count) :
    Listing8OwnerPointerFrames.CompatibleAll mode (Listing8OriginalGraphCatalog.catalog mode origin g) address count := by
  rcases stores with body | cursor | tape
  · intro template member;right;left
    have after:=lower mode origin g template member
    have order:=Listing8GlobalControlLayout.ordered mode origin
    omega
  · intro template member;right;left
    have after:=lower mode origin g template member
    have before:=Listing8InputCrossCatalogFields.cursor_before_second mode l
    have next:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
    change secondStart mode l≤patchStart mode l at next
    have endAt:=(coordinates mode l).2.2
    have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
    have order:=Listing8GlobalControlLayout.ordered mode origin
    rcases cursor with ⟨rfl,small⟩
    omega
  · rw [ctx.nodeLocated] at tape
    rcases tape with ⟨rfl,small⟩
    exact symbol mode origin g node count small

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory)
    (stores : Listing8InputStoreFields.Allowed mode origin l address packet.length) :
    All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (ByteMemory.putBytes memory address packet) :=
  Listing8OwnerPointerFrames.store mode _ memory address packet initial
    (allowed mode origin l t g node rule ctx address packet.length stores)

end SmcTuring.Appendix.Listing8OriginalGraphInputFields
