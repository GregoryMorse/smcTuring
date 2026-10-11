module
public import SmcTuring.Appendix.Listing8FailureGeometry

public section
namespace SmcTuring.Appendix.Listing8FailureFrames
open Native Listing8CopyImage Listing8FailureGeometry
abbrev Targets:=Listing8PointerCopies.Targets

theorem state_before (mode : Mode) (l : Layout) (sentinel begin : Nat) :
    (Listing8StateGeometry.region mode l).start ≤ (region mode l sentinel begin).start := by
  cases mode <;> simp [region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,
    Listing8StateLayout.maskPC,Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8PointerCopies.halfCount] <;> omega

/-- Every already executed stage preserves a later bounded window. No byte
image or fetch at the future failure entry is a premise. -/
theorem after_state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (region mode l sentinel begin).start ≤ observed)
    (upper : observed+count ≤ Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8StateImage.memory mode l t v extra) observed count := by
  have afterHead:=Nat.le_trans (state_before mode l sentinel begin) after
  rw [Listing8GlobalState.finish,Listing8StateTrace.window mode (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t r bounds.state) _ (Listing8GlobalState.entry mode l t v r owners copies bounds.state extra seed)
    observed count
    (fun writer member => Or.inl (Nat.le_trans (state_helpers_before mode l sentinel begin writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (state_packets_before mode l t sentinel begin r bounds writer member) after))]
  change ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v (Listing8StateImage.backing mode l extra) seed).principal.memory observed count= _
  rw [Listing8StateFrames.after_head mode l t v r owners copies bounds.state (Listing8StateImage.backing mode l extra) seed observed count afterHead]
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v
    (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal.memory observed count= _
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.state.head.input _ seed observed count
    (input_outside mode l t sentinel begin bounds observed count after upper),Listing8GlobalInput.entryState]
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    have coords:=positions mode l t sentinel begin bounds
    have input:=Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  rw [Listing8GlobalWindows.pointers mode l t v r owners copies _ seed observed count inputBefore
    (Or.inl (Listing8StateGeometry.direction_outside mode l t bounds.state observed afterHead))
    (fun writer member => Or.inl (pointer_outside mode l t sentinel begin bounds observed after writer member))]
  rfl

end SmcTuring.Appendix.Listing8FailureFrames
