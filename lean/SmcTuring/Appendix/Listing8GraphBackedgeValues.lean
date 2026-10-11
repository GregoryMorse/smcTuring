module
public import SmcTuring.Appendix.Listing8GraphBackedgeSources

public section
namespace SmcTuring.Appendix.Listing8GraphBackedgeValues
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphBackedge
abbrev Targets:=Listing8PointerCopies.Targets

theorem head_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  rw [effect mode origin l t g node rule ctx memory seed]
  have current:=Listing8GlobalBootValues.head mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (Listing8JumpImage.backing mode origin (backing mode origin l g memory)) seed (g.rules rule).takeBack rfl
  rw [ctx.nodeLocated] at current
  rw [Listing8GraphStep.head_pointer] at current
  exact current
theorem rule_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule g node rule)) := by
  rw [effect mode origin l t g node rule ctx memory seed]
  have current:=Listing8GlobalBootValues.transition mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (Listing8JumpImage.backing mode origin (backing mode origin l g memory)) seed
  rw [Listing8GraphStep.rule_pointer] at current
  exact current
theorem live_membership (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    ∃ target : Fin g.transitions,Listing8GraphStep.nextRule g node rule=some target ∧
      MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory l.input.cursor=
        Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) ∧
      MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
        Arithmetic.encodeNat mode (rulePC mode origin g target) := by
  obtain ⟨target,current⟩:=Listing8GraphLabels.nonhalt_rule g node rule nonhalt
  refine ⟨target,current,head_cursor mode origin l t g node rule ctx memory seed,?_⟩
  rw [rule_cursor mode origin l t g node rule ctx memory seed,current]
  rfl
theorem node_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    let updated:=Listing8GraphStep.updated g node rule
    DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query+6)=(updated.tape query).symbol ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (pointerField mode (backEntry mode (nodePC mode origin g query)))=
      Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (pointerField mode (forwardEntry mode (nodePC mode origin g query)))=
      Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward) := by
  apply node_values
  rw [node_length]
  exact Listing8GraphBackedgeSources.node_current mode origin l t g node rule ctx memory seed query

theorem rule_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.transitions) (head : Fin g.nodes) :
    let v:=values mode origin (Listing8GraphStep.updated g node rule) head query
    let state:=finish mode origin l t g node rule memory seed
    MixedMemory.getWord mode state.principal.memory (pointerField mode (rulePC mode origin g query))=v.next ∧
    DwordCode.get state.principal.memory (currentEntry mode (rulePC mode origin g query)+6)=v.rule ∧
    DwordCode.get state.principal.memory (newEntry mode (rulePC mode origin g query)+6)=v.fresh ∧
    DwordCode.get state.principal.memory (directionEntry mode (rulePC mode origin g query)+6)=v.direction ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (stateEntry mode (rulePC mode origin g query)))=v.newState := by
  apply transition_values
  rw [transition_length]
  exact Listing8GraphBackedgeSources.rule_current mode origin l t g node rule ctx memory seed query head

end SmcTuring.Appendix.Listing8GraphBackedgeValues
