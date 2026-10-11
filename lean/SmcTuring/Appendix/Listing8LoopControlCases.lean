module
public import SmcTuring.Appendix.Listing8LoopControlFrames

public section
namespace SmcTuring.Appendix.Listing8LoopControlCases
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem nonfailure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    Listing8LoopControl.failed mode origin l t g node rule state=false := by
  cases result : Listing8LoopControl.failed mode origin l t g node rule state
  · rfl
  · exact False.elim (nonhalt ((Listing8LoopControl.failed_iff mode origin l t g node rule ctx old state image).mp result))

theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8LoopControl.failed mode origin l t g node rule state=true := (Listing8LoopControl.failed_iff mode origin l t g node rule ctx old state image).mpr halted

theorem nonhalt_effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    Listing8LoopControl.finish mode origin l t g node rule state={Listing8LoopControl.failureEnd mode origin l t g node rule state with principal:={(Listing8LoopControl.failureEnd mode origin l t g node rule state).principal with pc:=Arithmetic.encodeNat mode l.start,carry:=false}} := by
  rw [Listing8LoopControl.effect mode origin l t g node rule ctx old state image,nonfailure mode origin l t g node rule ctx old state image nonhalt]
  simp only [Bool.false_eq_true,ite_false]

theorem halt_effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8LoopControl.finish mode origin l t g node rule state={Listing8LoopControl.failureEnd mode origin l t g node rule state with principal:={(Listing8LoopControl.failureEnd mode origin l t g node rule state).principal with pc:=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin),carry:=false}} := by
  rw [Listing8LoopControl.effect mode origin l t g node rule ctx old state image,failure mode origin l t g node rule ctx old state image halted]
  simp only [ite_true]

theorem halt_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [Listing8LoopControlFrames.logical_transition mode origin l t g node rule ctx old state image,(Listing8GraphStep.halted_iff g node rule).mpr halted]
  rfl

end SmcTuring.Appendix.Listing8LoopControlCases
