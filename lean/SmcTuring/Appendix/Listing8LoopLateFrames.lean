module
public import SmcTuring.Appendix.Listing8LoopFailureFrames
public import SmcTuring.Appendix.Listing8LateFrames

public section
namespace SmcTuring.Appendix.Listing8LoopLateFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailure.Bounds
abbrev Current:=Listing8LoopFailure.Current

theorem state_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (after : (Listing8FailureGeometry.region mode l sentinel begin).start≤observed)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8LoopStateFrames.window mode l t v old b.state state entry forward current.state observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_helpers_before mode l sentinel begin writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_packets_before mode l t sentinel begin b.state.head.input.input.prefixBounds.resources b.failure writer member) after)),
    Listing8LoopStatePrefix.head_window mode l t v old b.state state entry forward current.state observed count
      (Nat.le_trans (Listing8FailureFrames.state_before mode l sentinel begin) after),
    Listing8MainInputFrames.input_window mode l t v old b.state.head.input state entry forward current.state.head.input observed count
      (Listing8LateFrames.input_outside mode l t sentinel begin b.failure observed count after tapeOutside)]
  exact Listing8LoopFailurePrefix.prefix_window mode l t v old sentinel begin b state entry forward current observed count after

theorem failure_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5≤observed)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  let region:=Listing8FailureGeometry.region mode l sentinel begin
  change Listing8FailureLayout.callPC mode region+5≤observed at after
  have coords:=Listing8FailureLayout.positions mode region
  have lower : region.start≤observed := by
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords after ⊢ <;> omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤observed := by
    have maskBefore:=coords.2.2.1
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords maskBefore after ⊢ <;> omega
  have maskBefore : Listing8FailureLayout.mask mode region+4≤observed := by
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords after ⊢ <;> omega
  rw [Listing8LoopFailure.window mode l t v sentinel begin old b state entry forward current observed count
    (Or.inl andBefore) (Or.inl maskBefore) (Or.inl after)]
  exact state_window mode l t v sentinel begin old b state entry forward current observed count lower tapeOutside

end SmcTuring.Appendix.Listing8LoopLateFrames
