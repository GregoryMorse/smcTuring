module
public import SmcTuring.Appendix.Listing8StateFrames

public section
namespace SmcTuring.Appendix.Listing8StateImage
open Native Listing8CopyImage Listing8Prototypes Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (l : Layout) (extra : ByteMemory.Memory) :=
  ByteMemory.putBytes extra (region mode l).start (Listing8StateLayout.bytes mode (region mode l))
@[expose] def memory (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (extra : ByteMemory.Memory) :=
  Listing8DirectionImage.memory mode l t v (backing mode l extra)

theorem initial_region (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode l t v extra) (region mode l).start (Listing8StateLayout.bytes mode (region mode l)).length =
      Listing8StateLayout.bytes mode (region mode l) := by
  have coords := positions mode l t bounds
  have endState : (region mode l).start+(Listing8StateLayout.bytes mode (region mode l)).length =
      Listing8StateLayout.endPC mode (region mode l) := by
    rw [Listing8StateLayout.bytes_length,(Listing8StateLayout.positions mode (region mode l)).2.2.2]
  have nodeLen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have transitionLen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have sourceNodeOutside : l.sourceNode+(sourceNodeBytes mode l v).length ≤ (region mode l).start ∨
      (region mode l).start+(Listing8StateLayout.bytes mode (region mode l)).length ≤ l.sourceNode := by
    rw [nodeLen,endState]
    rcases bounds.nodeOutside with early | late
    · left;cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
    · exact Or.inr late
  have sourceTransitionOutside : l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ (region mode l).start ∨
      (region mode l).start+(Listing8StateLayout.bytes mode (region mode l)).length ≤ l.sourceTransition := by
    rw [transitionLen,endState]
    rcases bounds.transitionOutside with early | late
    · left;cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
    · exact Or.inr late
  have directionEnd : (Listing8DirectionGeometry.region mode l).start+
      (Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)).length = (region mode l).start := by
    rw [Listing8DirectionLayout.bytes_length]
    exact (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2.symm
  have inputEnd := Listing8InputMask.bytes_length mode l.input 0 force force force force
  change l.input.start+(inputBytes mode l).length = Listing8LiteralInput.endPC mode l.input at inputEnd
  have inputPositions := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
  have codeEnd := code_length mode l
  have inputAfter := r.inputAfter
  have copyEnd := Listing8PointerCopies.bytes_length mode l t
  rw [←bounds.head.input.joined] at copyEnd
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ (region mode l).start := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords inputPositions <;> omega
  rw [memory,Listing8DirectionImage.memory,image,byte_frame _ _ _ _ _ sourceTransitionOutside,
    byte_frame _ _ _ _ _ sourceNodeOutside,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    byte_frame _ _ _ _ _ (Or.inl (by omega)),Listing8PointerImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8DirectionImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),backing]
  exact ByteMemory.bytes_at_put _ _ _

theorem initial_helpers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode l t v extra) (region mode l).start
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l))).length =
      DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l)) :=
  ByteWindow.packet _ (region mode l).start [] _ _
    (by simpa only [Listing8StateLayout.bytes,List.nil_append] using initial_region mode l t v r bounds extra)

theorem initial_headers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    DwordPackets.Intact mode (Listing8StateLayout.packets mode (region mode l)) (memory mode l t v extra) := by
  have packetBytes := ByteWindow.packet (memory mode l t v extra) (region mode l).start
    (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l)))
    (DwordPackets.bytes mode (Listing8StateLayout.packets mode (region mode l)) Listing8DirectionLayout.force) []
    (by simpa only [Listing8StateLayout.bytes,List.append_nil] using initial_region mode l t v r bounds extra)
  rw [Listing8StateLayout.helper_span] at packetBytes
  exact DwordPackets.initial_headers mode _ _ _ (Listing8StateLayout.packet_chain mode (region mode l)) _
    (by simpa only [List.append_nil] using packetBytes)

theorem current_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w ∈ windows mode (region mode l)) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v (backing mode l extra) seed).principal.memory w.1 w.2 =
      ByteMemory.bytesAt (memory mode l t v extra) w.1 w.2 := by
  have spans := window_span mode (region mode l) w member
  rw [Listing8StateFrames.after_head mode l t v r owners copies bounds _ seed w.1 w.2 spans.1]
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l (backing mode l extra)) seed).principal.memory _ _ = _
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.head.input _ seed w.1 w.2
    (input_outside mode l t bounds w member),Listing8GlobalInput.entryState]
  have before : Listing8LiteralInput.endPC mode l.input ≤ w.1 := by
    have pos := positions mode l t bounds
    have inp := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at pos inp <;> omega
  rw [Listing8GlobalWindows.pointers mode l t v r owners copies _ seed w.1 w.2 before
    (Or.inl (direction_outside mode l t bounds w.1 spans.1)) (pointer_outside mode l t bounds w member)]
  rfl

theorem helper_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v (backing mode l extra) seed).principal.memory (region mode l).start
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l))).length =
      DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l)) := by
  have member : ((region mode l).start,(DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (region mode l))).length) ∈ windows mode (region mode l) := by
    cases mode <;> simp [windows,DwordMixedSequence.bytes,Listing8StateLayout.helpers,Listing8PointerCopies.split,
      DwordMixedImage.bytes_length,DwordLayout.span,DwordLayout.storeSize]
  rw [current_window mode l t v r owners copies bounds extra seed _ member]
  exact initial_helpers mode l t v r bounds extra

theorem header_member (mode : Mode) (l : Listing8StateLayout.Layout) (reader : DwordPackets.Site)
    (member : reader ∈ Listing8StateLayout.packets mode l) : (reader.pc,6) ∈ windows mode l := by
  cases mode
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
    Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [windows]

theorem headers_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8StateLayout.packets mode (region mode l))
      (Listing8GlobalHead.finish mode l t v (backing mode l extra) seed).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,current_window mode l t v r owners copies bounds extra seed (reader.pc,6)
    (header_member mode (region mode l) reader member)]
  exact initial_headers mode l t v r bounds extra reader member

end SmcTuring.Appendix.Listing8StateImage
