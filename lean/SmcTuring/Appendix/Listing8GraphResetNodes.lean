module
public import SmcTuring.Appendix.Listing8GraphBodyNodes

public section
namespace SmcTuring.Appendix.Listing8GraphResetNodes
open Native Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphBodyNodes

/-- Every original input node packet in the actual reset result is derived
from the updated body image and the exact table/reset frames. -/
theorem current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    ByteMemory.bytesAt (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory
      (nodePC mode origin g query) (nodeSpan mode)=Listing8NodeBlock.bytes mode (nodePC mode origin g query)
        (value mode origin g node rule query) := by
  have after : Listing8ResetLayout.endPC mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt)
      (table mode origin g))≤nodePC mode origin g query := by
    rw [Listing8GraphReset.actual_region mode origin l t _ (table mode origin g) ctx.boot ctx.body,
      Listing8GraphReset.endpoint,table_length]
    exact Listing8GraphLayout.node_lower mode origin g.transitions query.val
  rw [Listing8GraphRun.finish,Listing8FullTableNodeFrames.window mode origin l t (values mode origin g node rule) _
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx)
    (Listing8GraphNodeImage.image mode origin g memory) seed _ _ after]
  exact Listing8GraphBodyNodes.current mode origin l t g node rule ctx memory seed query

/-- Joining the derived current packets proves the complete live table.
There is no replacement with an initialized memory snapshot. -/
theorem initial (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (declarations mode origin g node rule) (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory := by
  apply Listing8LiveNodePacket.initial_from_packets
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [length] at small
    exact small
  have actual:=lookup mode origin g node rule ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact current mode origin l t g node rule ctx memory seed ⟨index,within⟩

theorem node_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (query : Fin g.nodes)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8NodeBlock.Bounds mode (nodePC mode origin g query) (value mode origin g node rule query) := by
  have original:=Listing8GraphNodeImage.node_bounds mode origin g query bounds
  exact ⟨original.capacity,original.backOutside,original.forwardOutside⟩
theorem valid (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8NodeTable.Valid mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g node rule) := by
  apply Listing8GraphNodeImage.valid_from_lookup
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [length] at small
    exact small
  have actual:=lookup mode origin g node rule ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact node_bounds mode origin g node rule ⟨index,within⟩ bounds

theorem fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    DwordCode.get (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query+6)=
      symbol g node rule query ∧
    MixedMemory.getWord mode (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory
      (pointerField mode (backEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back) ∧
    MixedMemory.getWord mode (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory
      (pointerField mode (forwardEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward) := by
  apply node_values
  rw [node_length]
  exact current mode origin l t g node rule ctx memory seed query
end SmcTuring.Appendix.Listing8GraphResetNodes
