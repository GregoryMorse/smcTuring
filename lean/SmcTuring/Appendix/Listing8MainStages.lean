module
public import SmcTuring.Appendix.Listing8MainGeometry

public section
namespace SmcTuring.Appendix.Listing8MainStages
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l)
    (bounds : Listing8GlobalInput.Bounds mode l t) (observed count : Nat) (before : observed+count ≤ patchStart mode l+40)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    Listing8InputWindows.Outside mode l.input observed count := by
  have input:=Listing8MainOwners.input_after mode l r
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have endInput : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have loc:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at loc <;> omega
  refine ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),?_,?_⟩
  · rw [bounds.fields.headLabel];exact tape
  · intro helper member
    have lower:=bounds.fields.masksAfter helper member
    exact Or.inr (by omega)

theorem input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8GlobalInput.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ patchStart mode l+40)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (image mode l v (Listing8PointerImage.backing mode l t extra)) observed count := by
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds extra seed observed count (input_outside mode l t r bounds observed count before tape)]
  exact Listing8MainOwners.pointers mode l t v r owners copies extra seed observed count before secondOutside
    (Listing8MainGeometry.pointer_targets mode l t copies)

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ patchStart mode l+40)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra) observed count := by
  rw [Listing8GlobalDirection.finish,Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) bounds.capacity _
    (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8MainGeometry.direction_helpers mode l t bounds writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8MainGeometry.direction_packets mode l t bounds writer member)))]
  exact input mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed observed count before secondOutside tape

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ patchStart mode l+40)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra) observed count := by
  rw [Listing8GlobalHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t bounds) _ (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8MainGeometry.tail_xors mode l t bounds writer member)))
    (fun writer member => Listing8MainGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_left _ member))
    (fun writer member => Listing8MainGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_right _ member))]
  exact direction mode l t v r owners copies bounds extra seed observed count before secondOutside tape
end SmcTuring.Appendix.Listing8MainStages
