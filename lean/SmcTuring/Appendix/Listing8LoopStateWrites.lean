module
public import SmcTuring.Appendix.Listing8LoopHeadWrites
public import SmcTuring.Appendix.Listing8LoopGraphState
public import SmcTuring.Appendix.Listing8GraphStateWrites

public section
namespace SmcTuring.Appendix.Listing8LoopStateWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput
abbrev Current := Listing8LoopGraphState.Current

/-- Repeated state selection owns both pointer halves and every live
arithmetic store; the reached state and current fragments are derived. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds := Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image := Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  rw [Listing8LoopState.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8LoopHead.finish mode l t (values mode origin g node rule) state)
  · exact (Listing8LoopHeadWrites.execute mode origin l t g node rule ctx old state current.head).1
  · exact Listing8LoopHeadWrites.owned mode origin l t g node rule ctx old state current.head
  · exact Listing8StateWrites.owned mode origin _ (Listing8StateGeometry.region mode l)
      (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state)
      (Listing8GraphStateWrites.region_bounds mode origin l t g node rule ctx)
      (Listing8GraphStateWrites.cursor_bounds mode origin l t g node rule ctx) _
      (Listing8LoopHead.endpoint mode l t _ old bounds.head state current.head.graph.entry current.head.graph.forward image.head)

set_option maxHeartbeats 1000000 in
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state :=
  ⟨StringDwordWritesBridge.trace mode (Listing8LoopState.trace mode l t _ old
      (Listing8LoopGraphState.bounds mode origin l t g node rule ctx) state current.head.graph.entry current.head.graph.forward
      (Listing8LoopGraphState.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current)),
    owned mode origin l t g node rule ctx old state current⟩

end SmcTuring.Appendix.Listing8LoopStateWrites
