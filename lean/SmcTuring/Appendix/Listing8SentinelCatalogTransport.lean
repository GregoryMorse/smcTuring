module
public import SmcTuring.Appendix.Listing8MainCatalogTransport
public import SmcTuring.Appendix.Listing8GlobalFailureRegions

public section
namespace SmcTuring.Appendix.Listing8SentinelCatalogTransport
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

theorem late (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    codeEnd mode l≤nodePC mode origin g g.halt := by
  have last:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).sentinelLater
  change Listing8FullTableImage.start mode origin≤nodePC mode origin g g.halt at last
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  omega

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (count : Nat) (small : count≤mode.wordBytes) :
    Listing8OwnerPointerFrames.CompatibleAll mode
      (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)))
      (nodePC mode origin g g.halt) count := by
  have after:=late mode origin l t g node rule ctx
  have copiedAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤nodePC mode origin g g.halt := by
    change codeEnd mode l≤nodePC mode origin g g.halt;exact after
  have ruleBefore : l.sourceTransition+transitionSpan mode≤nodePC mode origin g g.halt := by
    rw [ctx.ruleLocated]
    exact Listing8GraphLayout.table_node_apart mode origin g.transitions rule.val g.halt.val rule.isLt
  have apart : nodePC mode origin g g.halt+nodeSpan mode≤l.sourceNode ∨
      nodePC mode origin g g.halt=l.sourceNode ∨ l.sourceNode+nodeSpan mode≤nodePC mode origin g g.halt := by
    rw [ctx.nodeLocated]
    rcases Nat.lt_trichotomy g.halt.val node.val with before | equal | later
    · exact Or.inl (Listing8GraphLayout.nodes_apart mode origin g.transitions g.halt.val node.val before)
    · right;left;unfold nodePC;rw [equal]
    · exact Or.inr (Or.inr (Listing8GraphLayout.nodes_apart mode origin g.transitions node.val g.halt.val later))
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
  all_goals simp only [nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Mode.wordBytes] at copiedAfter ruleBefore apart small
  all_goals rcases apart with before | equal | later <;> omega

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (packet : List LittleEndian.Byte)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) memory)
    (small : packet.length≤mode.wordBytes) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (ByteMemory.putBytes memory (nodePC mode origin g g.halt) packet) := by
  have after:=late mode origin l t g node rule ctx
  have ending:=(coordinates mode l).2.2
  exact ⟨DwordTemplateCollection.store_all _ memory _ packet initial.1
      (Listing8RetargetOwnerFields.after_code mode l _ _ after),
    Listing8MacroPointerFrames.store mode l memory _ packet initial.2.1 (Or.inl (by omega)),
    Listing8OwnerPointerFrames.store mode _ memory _ packet initial.2.2 (owners mode origin l t g node rule ctx packet.length small)⟩

end SmcTuring.Appendix.Listing8SentinelCatalogTransport
