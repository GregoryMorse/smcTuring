module
public import SmcTuring.Appendix.Listing8LoopFailure

public section
namespace SmcTuring.Appendix.Listing8LoopFailureFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailure.Bounds
abbrev Current:=Listing8LoopFailure.Current

theorem before_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤(Listing8FailureGeometry.region mode l sentinel begin).start) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count := by
  apply Listing8FailureReuseEffects.prefix_window mode _
    (Listing8FailureGeometry.local_bounds mode l t sentinel begin b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)
  have later:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l sentinel begin)
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at later <;> omega

theorem direction_fragments (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l)
      (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory :=
  Listing8LoopDirectionImage.transport mode _ _ _ (Listing8LoopStateFrames.direction_fragments mode l t v old b.state state entry forward current.state)
    (fun w member => before_window mode l t v sentinel begin old b state entry forward current w.1 w.2
      (Nat.le_trans (Listing8DirectionWindows.window_span mode _ w member).2 (Listing8FailureFrames.state_before mode l sentinel begin)))

theorem state_fragments (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l)
      (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory :=
  Listing8LoopStateImage.transport mode _ _ _ (Listing8LoopState.current_after mode l t v old b.state state entry forward current.state)
    (fun w member => before_window mode l t v sentinel begin old b state entry forward current w.1 w.2
      (Listing8StateGeometry.window_span mode _ w member).2)

end SmcTuring.Appendix.Listing8LoopFailureFrames
