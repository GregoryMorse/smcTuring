module
public import SmcTuring.Appendix.Listing8CopyWriteBounds
public import SmcTuring.Appendix.Listing9EarlyImage
public import SmcTuring.Appendix.Listing8LoopTailGeometry

public section
namespace SmcTuring.Appendix.Listing8GraphCopyWriteBounds
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem lower (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤l.start ∧ origin≤l.sourceNode ∧ origin≤l.sourceTransition := by
  have sites:=Listing9EarlyImage.sites_after_origin mode origin l t g node rule ctx
  exact ⟨sites ⟨l.start,codeBytes mode l⟩ (by simp [Listing8BootImage.sites]),
    sites ⟨l.sourceNode,sourceNodeBytes mode l (values mode origin g node rule)⟩ (by simp [Listing8BootImage.sites]),
    sites ⟨l.sourceTransition,sourceTransitionBytes mode l (values mode origin g node rule)⟩ (by simp [Listing8BootImage.sites])⟩

theorem copy_before_call (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    codeEnd mode l≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l
      (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5 := by
  have before:=ctx.resources.inputAfter
  have input:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input body <;> omega

/-- Complete copy and both original source buffers lie inside the actual
emitted graph code. All placement follows from the static input context. -/
theorem placement (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8CopyWriteBounds.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) l := by
  have bounds:=lower mode origin l t g node rule ctx
  refine ⟨⟨bounds.1,?_⟩,⟨bounds.2.1,Listing8LoopTailGeometry.source_node_before_end mode origin l t g node rule ctx⟩,
    ⟨bounds.2.2,Listing8LoopTailGeometry.source_rule_before_end mode origin l t g node rule ctx⟩⟩
  exact Nat.le_trans (copy_before_call mode origin l t g node rule ctx)
    (Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
      (Listing8LoopTailGeometry.input_before_end mode origin g))

end SmcTuring.Appendix.Listing8GraphCopyWriteBounds
