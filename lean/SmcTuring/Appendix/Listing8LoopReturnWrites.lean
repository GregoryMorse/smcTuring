module
public import SmcTuring.Appendix.Listing8LoopControl
public import SmcTuring.Appendix.Listing8JumpReturnWrites
public import SmcTuring.Appendix.Listing8GraphJumpWrites

public section
namespace SmcTuring.Appendix.Listing8LoopReturnWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- The loop invariant supplies present images; actual predecessor execution
constructs the stack/CALL/return entry and every complete code-owned store. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  Listing8JumpReturnWrites.owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) origin
    (Listing8LoopControl.failed mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state)
    (Listing8LoopControl.entry mode origin l t g node rule ctx old state image)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    ⟨Nat.le_refl _,Listing8GraphJumpWrites.stack_inside mode origin l t g node rule ctx⟩
    (Listing8LoopControl.current mode origin l t g node rule ctx old state image)

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)) (Listing8LoopControl.finish mode origin l t g node rule state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  ⟨Listing8LoopControl.return_trace mode origin l t g node rule ctx old state image,
    owned mode origin l t g node rule ctx old state image⟩

end SmcTuring.Appendix.Listing8LoopReturnWrites
