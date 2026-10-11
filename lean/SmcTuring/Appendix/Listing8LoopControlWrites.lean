module
public import SmcTuring.Appendix.Listing8LoopFailureWrites
public import SmcTuring.Appendix.Listing8LoopReturnWrites

public section
namespace SmcTuring.Appendix.Listing8LoopControlWrites
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput
abbrev Current := Listing8LoopControl.Current

/-- The repeated main body, actual stack prefix/CALL and selected return
own all 139/182 stores. The only dynamic contract is at this present entry. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  rw [Listing8LoopControl.program]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8LoopControl.failureEnd mode origin l t g node rule state)
  · exact Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) current.body
  · exact Listing8LoopFailureWrites.owned mode origin l t g node rule ctx old state current.body
  · exact Listing8LoopReturnWrites.owned mode origin l t g node rule ctx old state current

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state (Listing8LoopControl.program mode origin l t g node rule state)
      (Listing8LoopControl.finish mode origin l t g node rule state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8LoopControl.program mode origin l t g node rule state) state :=
  ⟨Listing8LoopControl.trace mode origin l t g node rule ctx old state current,
    owned mode origin l t g node rule ctx old state current⟩

end SmcTuring.Appendix.Listing8LoopControlWrites
