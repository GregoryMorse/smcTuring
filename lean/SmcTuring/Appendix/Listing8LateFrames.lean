module
public import SmcTuring.Appendix.Listing8GlobalJump

public section
namespace SmcTuring.Appendix.Listing8LateFrames
open Native Listing8CopyImage Listing8Prototypes Listing8FailureGeometry
abbrev Targets:=Listing8PointerCopies.Targets
/-- Static source-tape separation replaces the earlier CALL-end bound. -/
theorem input_outside (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat) (bounds : Bounds mode l t sentinel begin)
    (observed count : Nat) (after : (region mode l sentinel begin).start ≤ observed)
    (tapeOutside : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    Listing8InputWindows.Outside mode l.input observed count := by
  have coords:=positions mode l t sentinel begin bounds
  have input:=Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),?_,?_⟩
  · rw [bounds.state.head.input.fields.headLabel];exact tapeOutside
  · intro writer member
    left
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts] at member
    rw [bounds.state.mask,bounds.state.head.mask] at member
    cases mode
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp [region,Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,
      Listing8StateLayout.newPC,Listing8StateLayout.halves,Listing8StateGeometry.region,
      Listing8DirectionLayout.endPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.directionPC,
      Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at after ⊢ <;> omega

theorem after_state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : (region mode l sentinel begin).start ≤ observed)
    (tapeOutside : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8StateImage.memory mode l t v extra) observed count := by
  have afterHead:=Nat.le_trans (Listing8FailureFrames.state_before mode l sentinel begin) after
  rw [Listing8GlobalState.finish,Listing8StateTrace.window mode (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t r bounds.state) _ (Listing8GlobalState.entry mode l t v r owners copies bounds.state extra seed)
    observed count
    (fun writer member => Or.inl (Nat.le_trans (state_helpers_before mode l sentinel begin writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (state_packets_before mode l t sentinel begin r bounds writer member) after))]
  change ByteMemory.bytesAt (Listing8GlobalHead.finish mode l t v (Listing8StateImage.backing mode l extra) seed).principal.memory observed count=_
  rw [Listing8StateFrames.after_head mode l t v r owners copies bounds.state (Listing8StateImage.backing mode l extra) seed observed count afterHead]
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v
    (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal.memory observed count=_
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.state.head.input _ seed observed count
    (input_outside mode l t sentinel begin bounds observed count after tapeOutside),Listing8GlobalInput.entryState]
  have inputBefore : Listing8LiteralInput.endPC mode l.input ≤ observed := by
    have coords:=positions mode l t sentinel begin bounds
    have input:=Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  rw [Listing8GlobalWindows.pointers mode l t v r owners copies _ seed observed count inputBefore
    (Or.inl (Listing8StateGeometry.direction_outside mode l t bounds.state observed afterHead))
    (fun writer member => Or.inl (pointer_outside mode l t sentinel begin bounds observed after writer member))]
  rfl

theorem initial_image (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (observed count : Nat)
    (after : (region mode l sentinel begin).start ≤ observed)
    (nodeOutside : l.sourceNode+nodeSpan mode ≤ observed ∨ observed+count ≤ l.sourceNode)
    (transitionOutside : l.sourceTransition+transitionSpan mode ≤ observed ∨ observed+count ≤ l.sourceTransition) :
    ByteMemory.bytesAt (Listing8FailureGlobalImage.memory mode l t v sentinel begin extra) observed count=
      ByteMemory.bytesAt (Listing8FailureGlobalImage.backing mode l sentinel begin extra) observed count := by
  have coords:=positions mode l t sentinel begin bounds
  have beforeMain : l.start ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have nodeSep : l.sourceNode+(sourceNodeBytes mode l v).length ≤ observed ∨ observed+count ≤ l.sourceNode := by
    have length : (sourceNodeBytes mode l v).length=nodeSpan mode := node_length mode _ _ _ _
    rw [length];exact nodeOutside
  have transitionSep : l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ observed ∨ observed+count ≤ l.sourceTransition := by
    have length : (sourceTransitionBytes mode l v).length=transitionSpan mode := transition_length mode _ _ _ _ _ _
    rw [length];exact transitionOutside
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
  rw [Listing8FailureGlobalImage.memory,Listing8StateImage.memory,Listing8DirectionImage.memory,image,
    byte_frame _ _ _ _ _ transitionSep,byte_frame _ _ _ _ _ nodeSep,
    byte_frame _ _ _ _ _ (Or.inl (by omega)),byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8PointerImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega)),
    Listing8DirectionImage.backing,byte_frame _ _ _ _ _ (Or.inl directionBefore),
    Listing8StateImage.backing,byte_frame _ _ _ _ _ (Or.inl (by omega))]

/-- Every later window separated from the actual source-node tape write
survives the complete body; no CALL-end upper bound is required. -/
theorem after_failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8FailureLayout.callPC mode (region mode l sentinel begin)+5 ≤ observed)
    (tapeOutside : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8FailureGlobalImage.memory mode l t v sentinel begin extra) observed count := by
  have coords:=Listing8FailureLayout.positions mode (region mode l sentinel begin)
  have lower : (region mode l sentinel begin).start ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have andBefore : Listing8FailureLayout.andPC mode (region mode l sentinel begin)+10 ≤ observed := by
    have maskBefore:=coords.2.2.1
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords maskBefore <;> omega
  have maskBefore : Listing8FailureLayout.mask mode (region mode l sentinel begin)+4 ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  rw [Listing8GlobalFailure.finish,Listing8FailureValues.window mode (region mode l sentinel begin)
    (local_bounds mode l t sentinel begin r bounds) _ (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed)
    observed count (Or.inl andBefore) (Or.inl maskBefore) (Or.inl after)]
  rw [Listing8GlobalFailure.entryState,after_state mode l t v sentinel begin r owners copies bounds _ seed observed count lower tapeOutside]
  rfl
end SmcTuring.Appendix.Listing8LateFrames
