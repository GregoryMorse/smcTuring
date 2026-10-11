module
public import SmcTuring.Appendix.Listing8GraphNextHeadFrames

public section
namespace SmcTuring.Appendix.Listing8StateReuseFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

theorem helper_outside (mode : Mode) (l : Listing8StateLayout.Layout) (w : Nat × Nat)
    (member : w∈Listing8StateGeometry.windows mode l) (writer : DwordLayout.Layout)
    (writerMember : writer∈Listing8StateLayout.helpers mode l) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  cases mode
  all_goals simp only [Listing8StateGeometry.windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem packet_outside (mode : Mode) (l : Listing8StateLayout.Layout) (bounds : Listing8StateBounds.Bounds mode l)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode l) (writer : DwordPackets.Site)
    (writerMember : writer∈Listing8StateLayout.packets mode l) :
    writer.target+4≤w.1 ∨ w.1+w.2≤writer.target := by
  have before:=bounds.cursorBefore
  cases mode
  all_goals simp only [Listing8StateGeometry.windows,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
    Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Mode.wordBytes] at before
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8StateGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalState.entryState mode l t v extra seed).principal.memory w.1 w.2 :=
  Listing8StateTrace.window mode _ (Listing8StateGeometry.local_bounds mode l t r bounds) _
    (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed) _ _
    (helper_outside mode _ w member) (packet_outside mode _ (Listing8StateGeometry.local_bounds mode l t r bounds) w member)

theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GlobalState.entryState mode l t v (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed).principal.memory w.1 w.2 := by
  have before:=(Listing8StateGeometry.window_span mode (Listing8StateGeometry.region mode l) w member).2
  change w.1+w.2≤(Listing8FailureGeometry.region mode l sentinel begin).start at before
  rw [Listing8FailureGlobalValues.before_window mode l t v sentinel begin r owners copies bounds extra seed _ _ before]
  exact state mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed w member

end SmcTuring.Appendix.Listing8StateReuseFrames
