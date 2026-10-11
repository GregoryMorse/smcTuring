module
public import SmcTuring.Appendix.Listing8GraphNextInputNodes
public import SmcTuring.Appendix.Listing8DirectionWindows

public section
namespace SmcTuring.Appendix.Listing8GraphNextDirectionBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem direction_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)≤Listing8FullTableImage.start mode origin := by
  change (Listing8StateGeometry.region mode l).start≤Listing8FullTableImage.start mode origin
  rw [(Listing8StateGeometry.positions mode l t ctx.body.state).1,ctx.boot.packed,Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega

theorem call_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤
      Listing8FullTableImage.start mode origin := by
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤Listing8FullTableImage.start mode origin
  rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body]
  dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC]
  omega

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8DirectionGeometry.Bounds mode (nextLayout mode origin l g node rule target) t := by
  have old:=ctx.body.state.head
  have before:=direction_before_table mode origin l t g node rule ctx
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  refine ⟨⟨Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx,old.input.joined,old.input.targetsAfter,?_⟩,
    old.capacity,old.direction,old.back,old.forward,old.mask,old.transitionMaskAfter,old.stateAfter,Or.inr ?_,Or.inr ?_⟩
  · intro helper member
    left
    exact Nat.le_trans (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body _
      (Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx) helper member) nodeAfter
  · exact Nat.le_trans before nodeAfter
  · exact Nat.le_trans before ruleAfter

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8StateGeometry.Bounds mode (nextLayout mode origin l g node rule target) t := by
  have old:=ctx.body.state
  have before:=Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  refine ⟨direction mode origin l t g node rule target ctx,old.capacity,old.state,old.mask,Or.inr ?_,Or.inr ?_⟩
  · exact Nat.le_trans before nodeAfter
  · exact Nat.le_trans before ruleAfter

theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8FailureGeometry.Bounds mode (nextLayout mode origin l g node rule target) t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) := by
  have before:=call_before_table mode origin l t g node rule ctx
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  refine ⟨state mode origin l t g node rule target ctx,ctx.body.capacity,ctx.body.sentinelFits,ctx.body.sentinelOutside,Or.inr ?_,Or.inr ?_⟩
  · exact Nat.le_trans before nodeAfter
  · exact Nat.le_trans before ruleAfter

end SmcTuring.Appendix.Listing8GraphNextDirectionBounds
