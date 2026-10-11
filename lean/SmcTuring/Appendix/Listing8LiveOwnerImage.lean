module
public import SmcTuring.Appendix.Listing8LiveRetarget

public section
namespace SmcTuring.Appendix.Listing8LiveOwnerImage
open Native Listing8Prototypes Listing8CopyImage Listing8OwnerImage

theorem pointer_frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (q : Nat) (member : q∈pointerPositions mode l) :
    ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v state).principal.memory q (pointerSpan mode)=
      ByteMemory.bytesAt state.principal.memory q (pointerSpan mode) := by
  apply Listing8LiveRetarget.frame mode l v r reach state entry
  · exact pointer_patch_frame mode l q member
  · right
    have bound:=pointer_bounds mode l q member
    have inputAfter:=r.inputAfter
    have source:=source_field_bounds mode l
    omega

theorem original_frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l)) (q count : Nat)
    (outside : q+count≤l.start ∨ Listing8LiteralInput.endPC mode l.input≤q) :
    ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v state).principal.memory q count=
      ByteMemory.bytesAt state.principal.memory q count := by
  have before:=endpoint_lower mode l.start (nodeSpan mode)
  have next:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start≤secondStart mode l at before
  change secondStart mode l≤patchStart mode l at next
  have endBound:=code_to_input mode l r
  have startBound : l.start≤l.input.start := by have d:=destinations mode l; have afterInput:=r.inputAfter;omega
  apply Listing8LiveRetarget.frame mode l v r reach state entry
  · intro site member
    have bounds:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
    change patchStart mode l+40≤site.owner ∧ site.owner+10≤codeEnd mode l ∧ _ at bounds
    rcases outside with early | late <;> omega
  · have bounds:=source_field_bounds mode l
    rcases outside with early | late <;> omega

/-- All seven future owner fetches are derived from bytes current at the
retarget entry and the actual five preceding writes. -/
theorem current (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (block : Listing8LiveRetarget.Current mode l v state.principal.memory)
    (node : ByteMemory.bytesAt state.principal.memory l.sourceNode (sourceNodeBytes mode l v).length=sourceNodeBytes mode l v)
    (rule : ByteMemory.bytesAt state.principal.memory l.sourceTransition (sourceTransitionBytes mode l v).length=sourceTransitionBytes mode l v) :
    Listing8OwnerSequence.Intact mode (owners mode l v) (Listing8LiveRetarget.finish mode l v state).principal.memory := by
  have originalNode : ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v state).principal.memory l.sourceNode
      (sourceNodeBytes mode l v).length=sourceNodeBytes mode l v := by
    rw [original_frame mode l v r reach state entry _ _ (by simpa only [sourceNodeBytes,node_length] using r.nodeOutside)]
    exact node
  have originalTransition : ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v state).principal.memory l.sourceTransition
      (sourceTransitionBytes mode l v).length=sourceTransitionBytes mode l v := by
    rw [original_frame mode l v r reach state entry _ _ (by simpa only [sourceTransitionBytes,transition_length] using r.transitionOutside)]
    exact rule
  have sourceNode:=node_windows mode l.sourceNode l.sourceNode v.tape v.back v.forward _ originalNode
  have sourceTransition:=transition_windows mode l.sourceTransition l.sourceTransition v.next v.newState v.rule v.fresh v.direction _ originalTransition
  have copiedNode:=node_windows mode l.sourceNode (nodeParams mode l).destination v.tape v.back v.forward _
    (Listing8ModeOffsets.copied_node mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction
      v.back v.forward v.next v.newState _ block)
  have copiedTransition:=transition_windows mode l.sourceTransition (transitionParams mode l).destination v.next v.newState v.rule v.fresh v.direction _
    (Listing8ModeOffsets.copied_transition mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction
      v.back v.forward v.next v.newState _ block)
  have pointer (q source : Nat) (value : Word mode) (member : q∈pointerPositions mode l)
      (packet : ByteMemory.bytesAt state.principal.memory q (pointerBytes mode source value).length=pointerBytes mode source value) :
      ByteMemory.bytesAt (Listing8LiveRetarget.finish mode l v state).principal.memory q (pointerBytes mode source value).length=pointerBytes mode source value := by
    rw [pointer_length,pointer_frame mode l v r reach state entry q member]
    simpa only [pointer_length] using packet
  have scalar:=Listing8ModeOffsets.remaining_owners mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction
    v.back v.forward v.next v.newState (block_capacity mode l r) r.inputAfter reach (source_field_fits mode l r) _ entry block
  rw [←Listing8LiveRetarget.principal_effect] at scalar
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨sourceNode.1,pointer _ _ _ (by simp [pointerPositions]) copiedNode.1⟩
  · exact ⟨sourceNode.2,pointer _ _ _ (by simp [pointerPositions]) copiedNode.2⟩
  · exact ⟨sourceTransition.1,pointer _ _ _ (by simp [pointerPositions]) copiedTransition.1⟩
  · exact scalar.1
  · exact scalar.2.1
  · exact scalar.2.2
  · exact ⟨sourceTransition.2,pointer _ _ _ (by simp [pointerPositions]) copiedTransition.2⟩

end SmcTuring.Appendix.Listing8LiveOwnerImage
