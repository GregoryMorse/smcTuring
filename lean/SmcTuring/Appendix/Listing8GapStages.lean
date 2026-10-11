module
public import SmcTuring.Appendix.Listing8GapGeometry

public section
namespace SmcTuring.Appendix.Listing8GapStages
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l)
    (bounds : Listing8GlobalInput.Bounds mode l t) (observed count : Nat) (lower : codeEnd mode l≤observed) (before : observed+count ≤ l.input.start)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    Listing8InputWindows.Outside mode l.input observed count := by
  have input : l.input.start≤l.input.start := Nat.le_refl _
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
    (observed count : Nat) (lower : codeEnd mode l≤observed) (before : observed+count ≤ l.input.start)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (image mode l v (Listing8PointerImage.backing mode l t extra)) observed count := by
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds extra seed observed count (input_outside mode l t r bounds observed count lower before tape)]
  exact Listing8GapOwners.pointers mode l t v r owners copies bounds.joined extra seed observed count lower before

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (lower : codeEnd mode l≤observed) (before : observed+count ≤ l.input.start)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra) observed count := by
  rw [Listing8GlobalDirection.finish,Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) bounds.capacity _
    (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8GapGeometry.direction_helpers mode l t bounds writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8GapGeometry.direction_packets mode l t bounds writer member)))]
  exact input mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed observed count lower before secondOutside tape

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (lower : codeEnd mode l≤observed) (before : observed+count ≤ l.input.start)
    (secondOutside : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra) observed count := by
  rw [Listing8GlobalHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t bounds) _ (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8GapGeometry.tail_xors mode l t bounds writer member)))
    (fun writer member => Listing8GapGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_left _ member))
    (fun writer member => Listing8GapGeometry.tail_packets mode l t bounds observed count before firstOutside writer (List.mem_append_right _ member))]
  exact direction mode l t v r owners copies bounds extra seed observed count lower before secondOutside tape
end SmcTuring.Appendix.Listing8GapStages
