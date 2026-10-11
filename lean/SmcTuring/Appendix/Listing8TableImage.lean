module
public import SmcTuring.Appendix.Listing8TableTrace
public import SmcTuring.Appendix.Listing8ResetImage

public section
namespace SmcTuring.Appendix.Listing8TableImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def withoutSource (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) :=
  ByteMemory.putBytes (ByteMemory.putBytes (ByteMemory.putBytes
    (Listing8PointerImage.backing mode l t (Listing8DirectionImage.backing mode l
      (Listing8StateImage.backing mode l (Listing8FailureGlobalImage.backing mode l sentinel begin extra))))
    l.input.start (inputBytes mode l)) l.start (codeBytes mode l)) l.sourceNode (sourceNodeBytes mode l v)

theorem source_overlay (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (extra : ByteMemory.Memory) :
    Listing8FailureGlobalImage.memory mode l t v sentinel begin extra=
      ByteMemory.putBytes (withoutSource mode l t v sentinel begin extra) l.sourceTransition (sourceTransitionBytes mode l v) := rfl

/-- All preceding initializers preserve a later table window before the
selected transition overlay. No future table currentness is assumed. -/
theorem before_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (r : Resources mode l) (body : Listing8FailureGeometry.Bounds mode l t sentinel begin)
    (extra : ByteMemory.Memory) (observed count : Nat)
    (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5≤observed)
    (nodeOutside : l.sourceNode+nodeSpan mode≤observed ∨ observed+count≤l.sourceNode) :
    ByteMemory.bytesAt (withoutSource mode l t v sentinel begin extra) observed count=ByteMemory.bytesAt extra observed count := by
  have coords:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l sentinel begin)
  have lower : (Listing8FailureGeometry.region mode l sentinel begin).start≤observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have stateEnd : (Listing8StateGeometry.region mode l).start+
      (Listing8StateLayout.bytes mode (Listing8StateGeometry.region mode l)).length=(Listing8FailureGeometry.region mode l sentinel begin).start := by
    rw [Listing8StateLayout.bytes_length]
    exact (Listing8StateLayout.positions mode (Listing8StateGeometry.region mode l)).2.2.2.symm
  have directionEnd : (Listing8DirectionGeometry.region mode l).start+
      (Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)).length=(Listing8StateGeometry.region mode l).start := by
    rw [Listing8DirectionLayout.bytes_length]
    exact (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2.symm
  have directionBefore : (Listing8DirectionGeometry.region mode l).start+
      (Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)).length≤observed := by
    rw [directionEnd]
    exact Nat.le_trans (Listing8FailureFrames.state_before mode l sentinel begin) lower
  have input:=Listing8InputBounds.positions mode l t body.state.head.input.fields body.state.head.input.joined
  have failure:=Listing8FailureGeometry.positions mode l t sentinel begin body
  have inputBefore : Listing8LiteralInput.endPC mode l.input≤observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input failure <;> omega
  have inputEnd:=Listing8InputMask.bytes_length mode l.input 0 force force force force
  change l.input.start+(inputBytes mode l).length=Listing8LiteralInput.endPC mode l.input at inputEnd
  have codeEnd:=code_length mode l
  have pointerEnd:=Listing8PointerCopies.bytes_length mode l t
  rw [←body.state.head.input.joined] at pointerEnd
  have codeBefore:=code_to_input mode l r
  have nodeSep : l.sourceNode+(sourceNodeBytes mode l v).length≤observed ∨ observed+count≤l.sourceNode := by
    have length : (sourceNodeBytes mode l v).length=nodeSpan mode := node_length mode _ _ _ _
    rw [length]
    exact nodeOutside
  rw [withoutSource,byte_frame _ _ _ _ _ nodeSep,
    byte_frame _ _ _ _ _ (Or.inl (by omega)),byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8PointerImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8DirectionImage.backing,byte_frame _ _ _ _ _ (Or.inl directionBefore),
    Listing8StateImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8FailureGlobalImage.region_end]
      dsimp only [Listing8FailureLayout.callPC] at after
      omega)),byte_frame _ _ _ _ _ (Or.inl after)]

/-- The selected source initialization is an identity on the original table
because its exact packet already occurs at the selected initialized index. -/
theorem current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin start : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode start index)
    (r : Resources mode l) (body : Listing8FailureGeometry.Bounds mode l t sentinel begin)
    (extra : ByteMemory.Memory)
    (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5≤start)
    (nodeOutside : l.sourceNode+nodeSpan mode≤start ∨ Listing8TransitionTable.endPC mode start table≤l.sourceNode)
    (initial : Listing8TransitionTable.Initial mode start table extra) :
    Listing8TransitionTable.Initial mode start table (Listing8FailureGlobalImage.memory mode l t v sentinel begin extra) := by
  have sourceImage : Listing8TransitionTable.Initial mode start table (withoutSource mode l t v sentinel begin extra) := by
    rw [Listing8TransitionTable.Initial,before_window mode l t v sentinel begin r body extra start _ after (by
      rw [Listing8TransitionTable.endpoint]
      exact nodeOutside)]
    exact initial
  rw [source_overlay]
  change Listing8TransitionTable.Initial mode start table
    (ByteMemory.putBytes (withoutSource mode l t v sentinel begin extra) l.sourceTransition
      (transitionBytes mode l.sourceTransition v.next v.newState v.rule v.fresh v.direction))
  rw [located,Listing8TransitionTable.fields_overlay mode start table index v selected _ sourceImage]
  exact sourceImage
end SmcTuring.Appendix.Listing8TableImage
