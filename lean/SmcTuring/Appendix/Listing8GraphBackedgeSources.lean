module
public import SmcTuring.Appendix.Listing8GraphBackedge

public section
namespace SmcTuring.Appendix.Listing8GraphBackedgeSources
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphBackedge
abbrev Targets:=Listing8PointerCopies.Targets

/-- Every source-node packet is derived on the actual returned memory,
including the selected symbol update and both unchanged neighbor readers. -/
theorem node_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory
      (nodePC mode origin (Listing8GraphStep.updated g node rule) query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin (Listing8GraphStep.updated g node rule) query)
        (Listing8GraphNodeImage.value mode origin (Listing8GraphStep.updated g node rule) query) := by
  rw [effect mode origin l t g node rule ctx memory seed,Listing8GraphStep.node_label,Listing8GraphStep.node_value]
  exact Listing8GraphBodyNodes.current mode origin l t g node rule ctx memory seed query
theorem nodes_initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (finish mode origin l t g node rule memory seed).principal.memory := by
  apply Listing8LiveNodePacket.initial_from_packets
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [Listing8GraphNodeImage.length] at small
    exact small
  have actual:=Listing8GraphNodeImage.lookup mode origin (Listing8GraphStep.updated g node rule) ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact node_current mode origin l t g node rule ctx memory seed ⟨index,within⟩

/-- The actual body and restoring begin continuation retain the complete
original rule table; no future initialized table is a premise. -/
theorem table_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (finish mode origin l t g node rule memory seed).principal.memory := by
  rw [effect mode origin l t g node rule ctx memory seed]
  exact Listing8FullTableImage.body_current mode origin l t (values mode origin g node rule) _
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
    (Listing8GraphTableBounds.table_bounds mode origin g node l ctx.nodeLocated ctx.native)
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
      (Listing8GraphNodeImage.image mode origin g memory)) seed
theorem rule_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.transitions) (head : Fin g.nodes) :
    let v:=values mode origin (Listing8GraphStep.updated g node rule) head query
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory (rulePC mode origin g query) (transitionSpan mode)=
      transitionBytes mode (rulePC mode origin g query) v.next v.newState v.rule v.fresh v.direction := by
  dsimp only
  rw [Listing8GraphStep.transition_bytes]
  exact Listing8TransitionTable.selected_current mode (Listing8FullTableImage.start mode origin) (table mode origin g)
    query.val _ (lookup mode origin g query) _ (table_current mode origin l t g node rule ctx memory seed)

end SmcTuring.Appendix.Listing8GraphBackedgeSources
