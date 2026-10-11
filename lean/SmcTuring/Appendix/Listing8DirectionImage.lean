module
public import SmcTuring.Appendix.Listing8DirectionGeometry

public section
namespace SmcTuring.Appendix.Listing8DirectionImage
open Native Listing8CopyImage Listing8Prototypes Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (l : Layout) (extra : ByteMemory.Memory) :=
  ByteMemory.putBytes extra (region mode l).start (Listing8DirectionLayout.bytes mode (region mode l))
@[expose] def memory (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (extra : ByteMemory.Memory) :=
  image mode l v (Listing8PointerImage.backing mode l t (backing mode l extra))

/-- The complete literal direction region, including later XOR/mask/head
headers, belongs to the one global initial image. -/
theorem initial_region (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode l t v extra) (region mode l).start
      (Listing8DirectionLayout.bytes mode (region mode l)).length = Listing8DirectionLayout.bytes mode (region mode l) := by
  have span := positions mode l t bounds
  have coords := Listing8DirectionLayout.positions mode (region mode l)
  have ending : (region mode l).start+(Listing8DirectionLayout.bytes mode (region mode l)).length =
      Listing8DirectionLayout.endPC mode (region mode l) := by
    rw [Listing8DirectionLayout.bytes_length,coords.2.2.2.2.2.2.2]
  have nodeLength : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have transitionLength : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have sourceNodeOutside : l.sourceNode+(sourceNodeBytes mode l v).length ≤ (region mode l).start ∨
      (region mode l).start+(Listing8DirectionLayout.bytes mode (region mode l)).length ≤ l.sourceNode := by
    rw [nodeLength,ending]
    rcases bounds.nodeOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr late
  have sourceTransitionOutside : l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ (region mode l).start ∨
      (region mode l).start+(Listing8DirectionLayout.bytes mode (region mode l)).length ≤ l.sourceTransition := by
    rw [transitionLength,ending]
    rcases bounds.transitionOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr late
  have inputEnd := Listing8InputMask.bytes_length mode l.input 0 force force force force
  change l.input.start+(inputBytes mode l).length = (region mode l).start at inputEnd
  have codeEnd := code_length mode l
  have inputAfter := r.inputAfter
  have inputBefore : l.input.start ≤ (region mode l).start := by
    change l.input.start ≤ Listing8LiteralInput.endPC mode l.input
    have input := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  have helperEnd := Listing8PointerCopies.bytes_length mode l t
  rw [←bounds.input.joined] at helperEnd
  rw [memory,image,byte_frame _ _ _ _ _ sourceTransitionOutside,byte_frame _ _ _ _ _ sourceNodeOutside,
    byte_frame _ _ _ _ _ (Or.inl (by omega)),byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8PointerImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),backing]
  exact ByteMemory.bytes_at_put _ _ _

theorem initial_helpers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode l t v extra) (region mode l).start
      (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length =
      DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l)) := by
  exact ByteWindow.packet _ (region mode l).start [] _
    (Listing8DirectionLayout.packets mode (Listing8DirectionLayout.arithmetic mode (region mode l)) ++
      Listing8DirectionLayout.differences mode (region mode l) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.masks mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.heads mode (region mode l)))
    (by simpa only [Listing8DirectionLayout.bytes,List.append_assoc,List.nil_append] using initial_region mode l t v r bounds extra)

theorem initial_headers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) :
    DwordPackets.Intact mode (Listing8DirectionLayout.arithmetic mode (region mode l)) (memory mode l t v extra) := by
  have arithmetic := ByteWindow.packet (memory mode l t v extra) (region mode l).start
    (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l)))
    (Listing8DirectionLayout.packets mode (Listing8DirectionLayout.arithmetic mode (region mode l)))
    (Listing8DirectionLayout.differences mode (region mode l) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.masks mode (region mode l)) ++
      Listing8DirectionLayout.packets mode (Listing8DirectionLayout.heads mode (region mode l)))
    (by simpa only [Listing8DirectionLayout.bytes,List.append_assoc] using initial_region mode l t v r bounds extra)
  rw [helper_bytes] at arithmetic
  exact DwordPackets.initial_headers mode _ _ Listing8DirectionLayout.force
    (Listing8DirectionLayout.arithmetic_chain mode (region mode l)) _ arithmetic

end SmcTuring.Appendix.Listing8DirectionImage
