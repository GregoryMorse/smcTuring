module
public import SmcTuring.Appendix.Listing8HeadGeometry

public section
namespace SmcTuring.Appendix.Listing8HeadImage
open Native Listing8CopyImage Listing8DirectionGeometry Listing8HeadGeometry
abbrev Targets := Listing8PointerCopies.Targets

/-- All prefix effects preserve the specified literal XOR/header windows.
Every separation fact is obtained from initial coordinates. -/
theorem current_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory w.1 w.2 =
      ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra) w.1 w.2 := by
  have spans := window_span mode (region mode l) w member
  rw [Listing8GlobalDirection.finish,Listing8DirectionTrace.window mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)
    w.1 w.2 (helper_outside mode (region mode l) w member) (packet_outside mode (region mode l) w member)]
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory _ _ = _
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.input _ seed w.1 w.2
    (input_outside mode l t bounds w member),Listing8GlobalInput.entryState,
    Listing8GlobalWindows.pointers mode l t v r owners copies (Listing8DirectionImage.backing mode l extra) seed
      w.1 w.2 spans.1 (direction_outside mode l t bounds w member) (pointer_outside mode l t bounds w member)]
  rfl

theorem initial_xor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (Listing8DirectionImage.memory mode l t v extra)
      (Listing8DirectionLayout.selectionEnd mode (region mode l))
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l))).length =
      DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l)) := by
  have body := ByteWindow.packet (Listing8DirectionImage.memory mode l t v extra) (region mode l).start
    (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.arithmetic mode (region mode l)))
    (Listing8DirectionLayout.differences mode (region mode l))
    (Listing8DirectionLayout.packets mode (Listing8DirectionLayout.masks mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.heads mode (region mode l)))
    (by simpa only [Listing8DirectionLayout.bytes,List.append_assoc] using Listing8DirectionImage.initial_region mode l t v r bounds extra)
  rw [Listing8HeadTailFrames.selection_span,←Listing8HeadTailBounds.xor_bytes] at body
  exact body

theorem xor_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.selectionEnd mode (region mode l))
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l))).length =
      DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l)) := by
  have member : (Listing8DirectionLayout.selectionEnd mode (region mode l),
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l))).length) ∈ windows mode (region mode l) := by
    rw [Listing8HeadTailFrames.xor_length]
    cases mode <;> simp [windows]
  rw [current_window mode l t v r owners copies bounds extra seed _ member]
  exact initial_xor mode l t v r bounds extra

theorem initial_headers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    DwordPackets.Intact mode (Listing8DirectionLayout.masks mode (region mode l) ++ Listing8DirectionLayout.heads mode (region mode l))
      (Listing8DirectionImage.memory mode l t v extra) := by
  have body := ByteWindow.packet (Listing8DirectionImage.memory mode l t v extra) (region mode l).start
    (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.arithmetic mode (region mode l)) ++
      Listing8DirectionLayout.differences mode (region mode l))
    (Listing8DirectionLayout.packets mode (Listing8DirectionLayout.masks mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.heads mode (region mode l))) []
    (by simpa only [Listing8DirectionLayout.bytes,List.append_assoc,List.append_nil] using Listing8DirectionImage.initial_region mode l t v r bounds extra)
  rw [Listing8HeadTailFrames.prefix_span] at body
  apply DwordPackets.initial_headers mode _ _ Listing8DirectionLayout.force
    (Listing8HeadTailFrames.headers_chain mode (region mode l))
  simpa only [Listing8DirectionLayout.packets,DwordPackets.bytes,List.flatMap_append] using body

theorem header_member (mode : Mode) (l : Listing8DirectionLayout.Layout) (reader : DwordPackets.Site)
    (member : reader ∈ Listing8DirectionLayout.masks mode l ++ Listing8DirectionLayout.heads mode l) :
    (reader.pc,6) ∈ windows mode l := by
  cases mode
  all_goals simp only [Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,Listing8DirectionLayout.group,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [windows]

theorem headers_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.masks mode (region mode l) ++ Listing8DirectionLayout.heads mode (region mode l))
      (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,current_window mode l t v r owners copies bounds extra seed (reader.pc,6)
    (header_member mode (region mode l) reader member)]
  exact initial_headers mode l t v r bounds extra reader member

end SmcTuring.Appendix.Listing8HeadImage
