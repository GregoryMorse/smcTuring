module
public import SmcTuring.Appendix.Listing8JointInitializerCatalog

public section
namespace SmcTuring.Appendix.Listing8JointObserverGeometry
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerTemplateCollection Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000

theorem node_member (mode : Mode) (origin : Nat) (g : Graph) (query : Fin g.nodes) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.nodeTemplates mode (nodePC mode origin g query)) :
    template∈Listing8OriginalGraphCatalog.catalog mode origin g :=
  List.mem_append_left _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨query,rfl⟩,member⟩)

theorem rule_member (mode : Mode) (origin : Nat) (g : Graph) (query : Fin g.transitions) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.ruleTemplates mode (rulePC mode origin g query)) :
    template∈Listing8OriginalGraphCatalog.catalog mode origin g :=
  List.mem_append_right _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨query,rfl⟩,member⟩)

theorem copied_classification (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (template : Template mode)
    (member : template∈Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) :
    (patchStart mode l≤start mode template ∧ start mode template+span mode template≤codeEnd mode l) ∨
    template∈Listing8OriginalGraphCatalog.catalog mode origin g := by
  simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
    List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
  all_goals solve
  | (right;rw [ctx.nodeLocated];apply node_member mode origin g node;simp [Listing8OriginalGraphCatalog.nodeTemplates])
  | (right;rw [ctx.ruleLocated];apply rule_member mode origin g rule;simp [Listing8OriginalGraphCatalog.ruleTemplates])
  | (left;cases mode <;>
      dsimp only [start,span,nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,
        Listing8ModeOffsets.transitionEntry,codeEnd,Listing8ModeOffsets.endPC,backEntry,forwardEntry,stateEntry,
        currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan] <;> omega)

theorem graph_gap (mode : Mode) (origin : Nat) (g : Graph) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.catalog mode origin g) :
    start mode template+span mode template≤Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g) ∨
    Listing8GraphLayout.input mode origin g.transitions≤start mode template := by
  have tail : Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)=
      Listing8GraphLayout.reset mode origin g.transitions := by
    rw [Listing8TransitionTable.endPC,table_length];rfl
  simp only [Listing8OriginalGraphCatalog.catalog,List.mem_append,List.mem_flatten] at member
  rcases member with ⟨items,selected,inside⟩ | ⟨items,selected,inside⟩
  · obtain ⟨query,rfl⟩ := List.mem_ofFn.mp selected
    right
    have bound := (Listing8OriginalGraphCatalog.node_bounds mode _ template inside).1
    have lower : Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g query :=
      Listing8GraphLayout.node_lower mode origin g.transitions query.val
    exact lower.trans bound
  · obtain ⟨query,rfl⟩ := List.mem_ofFn.mp selected
    left
    have upper := (Listing8OriginalGraphCatalog.rule_bounds mode _ template inside).2
    have lower : rulePC mode origin g query+transitionSpan mode≤Listing8GraphLayout.reset mode origin g.transitions :=
      Listing8GraphLayout.transition_upper mode origin g.transitions query.val query.isLt
    exact (upper.trans lower).trans (le_of_eq tail.symm)

/-- Writes in the two early operand regions or inside the exact reset gap
avoid EVERY source/copied graph observer. No broad whole-code exception. -/
theorem outside (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (packet : StringWrites.Packet)
    (placed : packet.address+packet.bytes.length≤patchStart mode l ∨
      (codeEnd mode l≤packet.address ∧ packet.address+packet.bytes.length≤Listing8FullTableImage.start mode origin) ∨
      (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤packet.address ∧
        packet.address+packet.bytes.length≤Listing8GraphLayout.input mode origin g.transitions)) :
    ∀ template∈Listing8JointDeclarationCatalog.Owners mode origin l (values mode origin g node rule) g,Outside mode template packet := by
  intro template member
  have codeBefore := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have patchBefore : patchStart mode l≤codeEnd mode l := by
    have dest := destinations mode l
    have n : patchStart mode l+40≤codeEnd mode l := by change (nodeParams mode l).destination≤codeEnd mode l;omega
    omega
  have tableBefore : Listing8FullTableImage.start mode origin≤Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g) := by
    unfold Listing8TransitionTable.endPC;omega
  have original : template∈Listing8OriginalGraphCatalog.catalog mode origin g → Outside mode template packet := by
    intro inGraph
    have lower := Listing8OriginalGraphInputFields.lower mode origin g template inGraph
    rcases placed with early | middle | gap
    · exact Or.inl (early.trans (patchBefore.trans (codeBefore.trans lower)))
    · exact Or.inl (middle.2.trans lower)
    · rcases graph_gap mode origin g template inGraph with first | last
      · exact Or.inr (first.trans gap.1)
      · exact Or.inl (gap.2.trans last)
  rcases List.mem_append.mp member with copied | inGraph
  · rcases copied_classification mode origin l t g node rule ctx template copied with localBounds | inGraph
    · rcases placed with early | middle | gap
      · exact Or.inl (early.trans localBounds.1)
      · exact Or.inr (localBounds.2.trans middle.1)
      · exact Or.inr (localBounds.2.trans (codeBefore.trans (tableBefore.trans gap.1)))
    · exact original inGraph
  · exact original inGraph

end SmcTuring.Appendix.Listing8JointObserverGeometry
