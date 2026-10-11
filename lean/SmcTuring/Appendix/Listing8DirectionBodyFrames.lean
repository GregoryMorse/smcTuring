module
public import SmcTuring.Appendix.Listing8DirectionWindows

public section
namespace SmcTuring.Appendix.Listing8DirectionBodyFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

theorem state_helpers_outside (mode : Mode) (l : Layout) (w : Nat × Nat)
    (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l))
    (writer : DwordLayout.Layout) (writerMember : writer∈Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l)) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  have upper:=(Listing8DirectionWindows.window_span mode _ w member).2
  change w.1+w.2≤(Listing8StateGeometry.region mode l).start at upper
  cases mode
  all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals right
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount] at upper ⊢ <;> omega

theorem state_packets_outside (mode : Mode) (l : Layout) (r : Resources mode l) (w : Nat × Nat)
    (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l))
    (writer : DwordPackets.Site) (writerMember : writer∈Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l)) :
    writer.target+4≤w.1 ∨ w.1+w.2≤writer.target := by
  have spans:=Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member
  have before:=Listing8PointerCopies.cursor_before mode l
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤codeEnd mode l at before
  have after:=r.inputAfter
  have input:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have lower:=spans.1
  change Listing8LiteralInput.endPC mode l.input≤w.1 at lower
  have upper : w.1+w.2≤(Listing8StateGeometry.region mode l).start := spans.2
  cases mode
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
    Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at before input
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount] at upper ⊢ <;> omega

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory w.1 w.2 := by
  exact Listing8DirectionTrace.window mode _ bounds.capacity _
    (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed) _ _
    (Listing8DirectionWindows.helper_outside mode _ w member)
    (Listing8DirectionWindows.packet_outside mode _ w member)

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8DirectionGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory w.1 w.2 := by
  rw [Listing8GlobalHead.finish,Listing8HeadTailTrace.window mode _ (Listing8HeadGeometry.tail_bounds mode l t bounds) _
    (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed) _ _
    (Listing8DirectionWindows.xor_outside mode _ w member)
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t bounds).cursorBefore w member writer (List.mem_append_left _ writerMember))
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t bounds).cursorBefore w member writer (List.mem_append_right _ writerMember))]
  exact direction mode l t v r owners copies bounds extra seed w member

theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8StateGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v (Listing8StateImage.backing mode l extra) seed).principal.memory w.1 w.2 := by
  rw [Listing8GlobalState.finish,Listing8StateTrace.window mode _ (Listing8StateGeometry.local_bounds mode l t r bounds) _
    (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed) _ _
    (state_helpers_outside mode l w member) (state_packets_outside mode l r w member)]
  exact head mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed w member

theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v (Listing8StateImage.backing mode l
        (Listing8FailureGlobalImage.backing mode l sentinel begin extra)) seed).principal.memory w.1 w.2 := by
  have upper:=(Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member).2
  have later:=(Listing8StateLayout.positions mode (Listing8StateGeometry.region mode l)).2.2.2
  have before : w.1+w.2≤(Listing8FailureGeometry.region mode l sentinel begin).start := by
    change w.1+w.2≤Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)
    change w.1+w.2≤(Listing8StateGeometry.region mode l).start at upper
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at later <;> omega
  rw [Listing8FailureGlobalValues.before_window mode l t v sentinel begin r owners copies bounds extra seed _ _ before]
  exact state mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed w member

end SmcTuring.Appendix.Listing8DirectionBodyFrames
