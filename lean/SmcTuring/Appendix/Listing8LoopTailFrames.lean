module
public import SmcTuring.Appendix.Listing8LoopTailGeometry

public section
namespace SmcTuring.Appendix.Listing8LoopTailFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Every later reserved window survives actual generic body/CALL/return.
No value or future image of that window is a premise. -/
theorem control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have call:=Nat.le_trans (Listing8LoopTailGeometry.call_before_end mode origin l t g node rule ctx) after
  have afterCall : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤observed := by
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤observed
    rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body]
    exact call
  have outside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6 := by
    left
    have upper:=Listing8LoopTailGeometry.source_node_before_end mode origin l t g node rule ctx
    have large : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
    omega
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.control.body
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image.control]
  exact Listing8LoopLateFrames.failure_window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state
    image.control.body.state.head.graph.entry image.control.body.state.head.graph.forward current observed count afterCall outside

theorem terminal (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule)
    (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (Listing8LoopTerminal.finish mode origin l t g node rule state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [(Listing8LoopTerminal.result mode origin l t g node rule ctx old state image halted).2.1,
    Listing8LoopReset.window mode origin l t g node rule ctx old state image halted observed count (Nat.le_trans (Listing8LoopTailGeometry.call_before_end mode origin l t g node rule ctx) after),
    (Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
  exact control mode origin l t g node rule ctx old state image observed count after

end SmcTuring.Appendix.Listing8LoopTailFrames
