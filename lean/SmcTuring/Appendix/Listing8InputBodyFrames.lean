module
public import SmcTuring.Appendix.Listing8InputLateGeometry

public section
namespace SmcTuring.Appendix.Listing8InputBodyFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def inputState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l
    (Listing8StateImage.backing mode l (Listing8FailureGlobalImage.backing mode l sentinel begin extra))) seed

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory observed count := by
  rw [Listing8GlobalDirection.finish,Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) bounds.capacity _
    (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8InputLateGeometry.direction_helpers mode l t bounds writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8InputLateGeometry.direction_packets mode l t bounds writer member)))]
  rfl

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory observed count := by
  rw [Listing8GlobalHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t bounds) _ (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8InputLateGeometry.tail_xors mode l t bounds writer member)))
    (fun writer member => Listing8InputLateGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_left _ member))
    (fun writer member => Listing8InputLateGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_right _ member))]
  exact direction mode l t v r owners copies bounds extra seed observed count before

theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8StateGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v
        (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal.memory observed count := by
  rw [Listing8GlobalState.finish,Listing8StateTrace.window mode (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t r bounds) _ (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed)
    observed count (fun writer member => Or.inr (Nat.le_trans before (Listing8InputLateGeometry.state_helpers mode l t bounds writer member)))
    (fun writer member => Listing8InputLateGeometry.state_packets mode l t bounds observed count before secondOutside writer member)]
  exact head mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed observed count before firstOutside

theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory observed count=
      ByteMemory.bytesAt (inputState mode l t v sentinel begin extra seed).principal.memory observed count := by
  have inputBefore : Listing8LiteralInput.endPC mode l.input≤(Listing8FailureGeometry.region mode l sentinel begin).start := by
    have coords:=(Listing8FailureGeometry.positions mode l t sentinel begin bounds).1
    have input:=(Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined).2.1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  rw [Listing8FailureGlobalValues.before_window mode l t v sentinel begin r owners copies bounds extra seed observed count (Nat.le_trans before inputBefore)]
  exact state mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed observed count before secondOutside firstOutside

end SmcTuring.Appendix.Listing8InputBodyFrames
