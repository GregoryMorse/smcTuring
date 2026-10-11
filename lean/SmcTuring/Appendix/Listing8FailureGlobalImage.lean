module
public import SmcTuring.Appendix.Listing8FailureFrames
public import SmcTuring.Appendix.Listing8FailureTrace

public section
namespace SmcTuring.Appendix.Listing8FailureGlobalImage
open Native Listing8CopyImage Listing8Prototypes Listing8FailureGeometry
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def callBytes (mode : Mode) (l : Layout) (sentinel begin : Nat) :=
  Native.encode mode (.callRelative (Listing8FailureLayout.original mode (region mode l sentinel begin)))
@[expose] def backing (mode : Mode) (l : Layout) (sentinel begin : Nat) (extra : ByteMemory.Memory) :=
  ByteMemory.putBytes
    (ByteMemory.putBytes extra (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) (callBytes mode l sentinel begin))
    (region mode l sentinel begin).start (Listing8FailureLayout.bytes mode (region mode l sentinel begin))
@[expose] def memory (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (extra : ByteMemory.Memory) :=
  Listing8StateImage.memory mode l t v (backing mode l sentinel begin extra)

theorem region_end (mode : Mode) (l : Layout) (sentinel begin : Nat) :
    (region mode l sentinel begin).start+(Listing8FailureLayout.bytes mode (region mode l sentinel begin)).length=
      Listing8FailureLayout.endPC mode (region mode l sentinel begin) := by
  rw [Listing8FailureLayout.bytes_length]
  exact (Listing8FailureLayout.positions mode (region mode l sentinel begin)).2.2.2.1.symm

theorem backing_region (mode : Mode) (l : Layout) (sentinel begin : Nat) (extra : ByteMemory.Memory) :
    Listing8FailureImage.Initial mode (region mode l sentinel begin) (backing mode l sentinel begin extra) :=
  ByteMemory.bytes_at_put _ _ _

theorem backing_call (mode : Mode) (l : Layout) (sentinel begin : Nat) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (backing mode l sentinel begin extra) (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) 5=
      callBytes mode l sentinel begin := by
  rw [backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [region_end]
    simp only [Listing8FailureLayout.callPC]
    omega))]
  exact ByteMemory.bytes_at_put _ _ _

/-- Earlier initializers and source overlays are outside every bounded future
window in the constructed failure/CALL region. -/
theorem image_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (observed count : Nat)
    (after : (region mode l sentinel begin).start ≤ observed)
    (upper : observed+count ≤ Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5) :
    ByteMemory.bytesAt (memory mode l t v sentinel begin extra) observed count=
      ByteMemory.bytesAt (backing mode l sentinel begin extra) observed count := by
  have coords:=positions mode l t sentinel begin bounds
  have beforeMain : l.start ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have nodeLen : (sourceNodeBytes mode l v).length=nodeSpan mode := node_length mode _ _ _ _
  have transitionLen : (sourceTransitionBytes mode l v).length=transitionSpan mode := transition_length mode _ _ _ _ _ _
  have nodeOutside : l.sourceNode+(sourceNodeBytes mode l v).length ≤ observed ∨ observed+count ≤ l.sourceNode := by
    rw [nodeLen]
    rcases bounds.nodeOutside with early | late
    · left;omega
    · right;omega
  have transitionOutside : l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ observed ∨ observed+count ≤ l.sourceTransition := by
    rw [transitionLen]
    rcases bounds.transitionOutside with early | late
    · left;omega
    · right;omega
  have stateEnd : (Listing8StateGeometry.region mode l).start+
      (Listing8StateLayout.bytes mode (Listing8StateGeometry.region mode l)).length=(region mode l sentinel begin).start := by
    rw [Listing8StateLayout.bytes_length]
    exact (Listing8StateLayout.positions mode (Listing8StateGeometry.region mode l)).2.2.2.symm
  have directionEnd : (Listing8DirectionGeometry.region mode l).start+
      (Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)).length=(Listing8StateGeometry.region mode l).start := by
    rw [Listing8DirectionLayout.bytes_length]
    exact (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.2.2.2.symm
  have inputEnd:=Listing8InputMask.bytes_length mode l.input 0 force force force force
  change l.input.start+(inputBytes mode l).length=Listing8LiteralInput.endPC mode l.input at inputEnd
  have input:=Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined
  have codeEnd:=code_length mode l
  have inputAfter:=r.inputAfter
  have pointerEnd:=Listing8PointerCopies.bytes_length mode l t
  rw [←bounds.state.head.input.joined] at pointerEnd
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  have directionBefore : (Listing8DirectionGeometry.region mode l).start+
      (Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)).length ≤ observed := by
    rw [directionEnd]
    exact Nat.le_trans (Listing8FailureFrames.state_before mode l sentinel begin) after
  rw [memory,Listing8StateImage.memory,Listing8DirectionImage.memory,image,
    byte_frame _ _ _ _ _ transitionOutside,byte_frame _ _ _ _ _ nodeOutside,
    byte_frame _ _ _ _ _ (Or.inl (by omega)),byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8PointerImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8DirectionImage.backing,byte_frame _ _ _ _ _ (Or.inl directionBefore),
    Listing8StateImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega))]

theorem initial_region (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) :
    Listing8FailureImage.Initial mode (region mode l sentinel begin) (memory mode l t v sentinel begin extra) := by
  rw [Listing8FailureImage.Initial,image_window mode l t v sentinel begin r bounds extra _ _ (Nat.le_refl _) (by
    rw [region_end]
    simp only [Listing8FailureLayout.callPC]
    omega)]
  exact backing_region mode l sentinel begin extra

theorem initial_call (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode l t v sentinel begin extra) (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) 5=
      callBytes mode l sentinel begin := by
  rw [image_window mode l t v sentinel begin r bounds extra _ _ (by
    have coords:=positions mode l t sentinel begin bounds
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega) (Nat.le_refl _)]
  exact backing_call mode l sentinel begin extra

theorem current_region (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8FailureImage.Initial mode (region mode l sentinel begin)
      (Listing8GlobalState.finish mode l t v (backing mode l sentinel begin extra) seed).principal.memory := by
  rw [Listing8FailureImage.Initial,Listing8FailureFrames.after_state mode l t v sentinel begin r owners copies bounds _ seed _ _ (Nat.le_refl _) (by
    rw [region_end]
    simp only [Listing8FailureLayout.callPC]
    omega)]
  exact initial_region mode l t v sentinel begin r bounds extra

theorem current_call (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v (backing mode l sentinel begin extra) seed).principal.memory
      (Listing8FailureLayout.callPC mode (region mode l sentinel begin)) 5=callBytes mode l sentinel begin := by
  rw [Listing8FailureFrames.after_state mode l t v sentinel begin r owners copies bounds _ seed _ _ (by
    have coords:=positions mode l t sentinel begin bounds
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega) (Nat.le_refl _)]
  exact initial_call mode l t v sentinel begin r bounds extra

end SmcTuring.Appendix.Listing8FailureGlobalImage
