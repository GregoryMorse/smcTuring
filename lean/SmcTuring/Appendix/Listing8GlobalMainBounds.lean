module
public import SmcTuring.Appendix.Listing8GlobalFailureRegions
public import SmcTuring.Appendix.Listing8LateGraphFieldBounds

public section
namespace SmcTuring.Appendix.Listing8GlobalMainBounds
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem copy (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤l.start ∧ codeEnd mode l≤Listing8JumpLayout.jumpPC mode origin := by
  have input:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have failure:=Listing8FailureGeometry.positions mode l t _ _ ctx.body
  have ending:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  have before:=ctx.resources.inputAfter
  refine ⟨by rw [ctx.boot.packed],?_⟩
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input failure <;> omega

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤Listing8JumpLayout.jumpPC mode origin := by
  have lower:=(copy mode origin l t g node rule ctx).1
  have positions:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have failure:=Listing8FailureGeometry.positions mode l t _ _ ctx.body
  have ending:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions failure <;> constructor <;> omega

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤(Listing8DirectionGeometry.region mode l).start ∧
      Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)≤Listing8JumpLayout.jumpPC mode origin := by
  have lower:=(Listing8DirectionGeometry.positions mode l t ctx.body.state.head).1
  have start:=(copy mode origin l t g node rule ctx).1
  have positions:=Listing8StateGeometry.positions mode l t ctx.body.state
  have failure:=Listing8FailureGeometry.positions mode l t _ _ ctx.body
  have ending:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  have directionEnd:=positions.1
  change Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)=_ at directionEnd
  refine ⟨start.trans lower,?_⟩
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions failure directionEnd <;> omega

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤(Listing8StateGeometry.region mode l).start ∧
      Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)≤Listing8JumpLayout.jumpPC mode origin := by
  have lower:=(copy mode origin l t g node rule ctx).1
  have positions:=Listing8StateGeometry.positions mode l t ctx.body.state
  have failure:=Listing8FailureGeometry.positions mode l t _ _ ctx.body
  have ending:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions failure <;> constructor <;> omega

theorem cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤l.input.cursor ∧ l.input.cursor+mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin := by
  have code:=copy mode origin l t g node rule ctx
  have bounds:=Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  exact ⟨code.1.trans bounds.1,bounds.2.1.trans code.2⟩

theorem state_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing4EntryLayout.mainPC mode origin≤(Listing8StateGeometry.region mode l).cursor ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin := by
  have located:=congrArg Listing8ResetLayout.Layout.transitionCursor
    (Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) [] ctx.boot ctx.body)
  change (Listing8StateGeometry.region mode l).cursor=origin+(if mode=.x86 then 129 else 230) at located
  rw [located]
  cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size,Listing8JumpLayout.jumpPC,Mode.wordBytes]

theorem originals (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8FullTableImage.start mode origin≤l.sourceNode ∧ Listing8FullTableImage.start mode origin≤l.sourceTransition := by
  rw [ctx.nodeLocated,ctx.ruleLocated]
  exact ⟨(Listing8GraphLayout.transition_lower mode origin g.transitions).trans
    ((Listing8GraphLayout.table_before_input mode origin g.transitions).trans
      (Listing8GraphLayout.node_lower mode origin g.transitions node.val)),Listing8GraphLayout.transition_lower mode origin rule.val⟩

end SmcTuring.Appendix.Listing8GlobalMainBounds
