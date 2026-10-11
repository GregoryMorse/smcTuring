module
public import SmcTuring.Appendix.Listing8StateGeometry

public section
namespace SmcTuring.Appendix.Listing8StateFrames
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets

theorem direction_helpers (mode : Mode) (l : Layout) (writer : DwordLayout.Layout)
    (member : writer ∈ Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l)) :
    writer.destination+4 ≤ (region mode l).start := by
  cases mode
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp [region,Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem direction_packets (mode : Mode) (l : Layout) (writer : DwordPackets.Site)
    (member : writer ∈ Listing8DirectionLayout.arithmetic mode (Listing8DirectionGeometry.region mode l)) :
    writer.target+4 ≤ (region mode l).start := by
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [region,Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem tail_xors (mode : Mode) (l : Layout) (writer : DwordXorHelper.Layout)
    (member : writer ∈ Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l)) :
    writer.destination+4 ≤ (region mode l).start := by
  cases mode
  all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [region,Listing8DirectionLayout.endPC,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] <;> omega

theorem tail_packets (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) (writer : DwordPackets.Site)
    (member : writer ∈ Listing8DirectionLayout.masks mode (Listing8DirectionGeometry.region mode l) ++
      Listing8DirectionLayout.heads mode (Listing8DirectionGeometry.region mode l)) :
    writer.target+4 ≤ (region mode l).start := by
  have before := (Listing8HeadGeometry.tail_bounds mode l t bounds.head).cursorBefore
  have coord := (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2
  cases mode
  all_goals simp only [Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,Listing8DirectionLayout.group,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [region,Listing8DirectionLayout.endPC,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
    Mode.wordBytes] at before coord ⊢ <;> omega

/-- Selection and actual head update preserve every later state-region
window. Their temporary source exchanges have already been restored. -/
theorem after_head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (region mode l).start ≤ observed) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v extra seed).principal.memory observed count =
      ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory observed count := by
  have tail := Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t bounds.head) (Listing8GlobalHead.entryState mode l t v extra seed)
    (Listing8GlobalHead.entry mode l t v r owners copies bounds.head extra seed) observed count
    (fun writer member => Or.inl (Nat.le_trans (tail_xors mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (tail_packets mode l t bounds writer (List.mem_append_left _ member)) after))
    (fun writer member => Or.inl (Nat.le_trans (tail_packets mode l t bounds writer (List.mem_append_right _ member)) after))
  have selection := Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) bounds.head.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds.head extra seed)
    observed count (fun writer member => Or.inl (Nat.le_trans (direction_helpers mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (direction_packets mode l writer member) after))
  exact tail.trans selection

end SmcTuring.Appendix.Listing8StateFrames
