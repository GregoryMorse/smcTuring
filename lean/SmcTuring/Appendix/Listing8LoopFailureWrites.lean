module
public import SmcTuring.Appendix.Listing8LoopStateWrites
public import SmcTuring.Appendix.Listing8FailureReuseWrites
public import SmcTuring.Appendix.Listing8LoopGraphFailure
public import SmcTuring.Appendix.Listing8GraphFailureWrites

public section
namespace SmcTuring.Appendix.Listing8LoopFailureWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput
abbrev Current := Listing8LoopGraphFailure.Current

theorem failure_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8FailureTrace.program mode
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
        (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have bounds := Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image := Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  exact Listing8FailureReuseWrites.owned mode origin _ _
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
    (Listing8GraphFailureWrites.placement mode origin l t g node rule ctx) _
    (Listing8LoopState.endpoint mode l t _ old bounds.state state current.state.head.graph.entry current.state.head.graph.forward image.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ bounds
      state current.state.head.graph.entry current.state.head.graph.forward image)

/-- The complete repeated body reaches its CALL operand with every one of
its 132/173 stores nonempty and wholly inside emitted graph code. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous) state := by
  rw [Listing8LoopFailure.program,List.map_append,List.map_map]
  change StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++_) state
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8LoopState.finish mode l t (values mode origin g node rule) state)
  · exact (Listing8LoopStateWrites.execute mode origin l t g node rule ctx old state current.state).1
  · exact Listing8LoopStateWrites.owned mode origin l t g node rule ctx old state current.state
  · exact failure_owned mode origin l t g node rule ctx old state current

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous)
      (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous) state :=
  ⟨Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) current,
    owned mode origin l t g node rule ctx old state current⟩

end SmcTuring.Appendix.Listing8LoopFailureWrites
