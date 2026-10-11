module
public import SmcTuring.Appendix.Listing8LoopOriginalInterpreter

public section
namespace SmcTuring.Appendix.Listing8LoopTailGeometry
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem input_before_end (mode : Mode) (origin : Nat) (g : Graph) :
    Listing8GraphLayout.input mode origin g.transitions≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes :=
  Listing8GraphLayout.node_lower mode origin g.transitions g.nodes

theorem call_before_end (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8JumpLayout.callPC mode origin+5≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have before:=Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤_ at before
  rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body] at before
  exact Nat.le_trans before (input_before_end mode origin g)

theorem source_node_before_end (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    l.sourceNode+Listing8Prototypes.nodeSpan mode≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  rw [ctx.nodeLocated]
  exact Listing8GraphLayout.node_upper mode origin g.transitions g.nodes node.val node.isLt

theorem source_rule_before_end (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    l.sourceTransition+Listing8Prototypes.transitionSpan mode≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  rw [ctx.ruleLocated]
  exact Nat.le_trans (Listing8GraphLayout.transition_upper mode origin g.transitions rule.val rule.isLt)
    (Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions) (input_before_end mode origin g))

end SmcTuring.Appendix.Listing8LoopTailGeometry
