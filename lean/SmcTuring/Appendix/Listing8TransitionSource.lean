module
public import SmcTuring.Appendix.Listing8FailReturn

public section
namespace SmcTuring.Appendix.Listing8TransitionSource
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
theorem packed_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (r : Resources mode l) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin) :
    Listing8FailLayout.Bounds mode origin l (Listing8FailLayout.endPC mode origin) := by
  have fits:=r.transition.sourceFits
  change l.sourceTransition+max (transitionSpan mode) mode.wordBytes<2^(8*mode.wordBytes) at fits
  have sourceCap : Listing8FailLayout.endPC mode origin<2^(8*mode.wordBytes) := by rw [located] at fits;omega
  have nodeSize : Listing4TargetLayout.size mode<nodeSpan mode := by cases mode <;> decide
  have callEq:=Listing8JumpImage.call_position mode origin l t sentinel boot body
  have node:=body.nodeOutside
  change l.sourceNode+nodeSpan mode ≤ l.start ∨ Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5 ≤ l.sourceNode at node
  rw [callEq] at node
  refine ⟨Nat.le_refl _,sourceCap,?_,Or.inr (Nat.le_of_eq located.symm)⟩
  rcases boot.node with early | late
  · exact Or.inl early
  · right
    rcases node with before | after
    · have large : 0<nodeSpan mode := by cases mode <;> decide
      omega
    · rcases r.sources with sourceBefore | sourceAfter
      · rw [located] at sourceBefore
        dsimp [Listing8FailLayout.endPC,Listing8JumpLayout.failPC] at sourceBefore
        omega
      · rw [located] at sourceAfter;omega
theorem initial_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (memory : ByteMemory.Memory) :
    ByteMemory.bytesAt (Listing8FailureGlobalImage.memory mode l t v sentinel begin memory) l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v := by
  have length : (sourceTransitionBytes mode l v).length=transitionSpan mode := transition_length mode _ _ _ _ _ _
  change ByteMemory.bytesAt (ByteMemory.putBytes _ l.sourceTransition (sourceTransitionBytes mode l v)) l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v
  rw [←length];exact ByteMemory.bytes_at_put _ _ _

/-- The original transition blueprint is also the printed ttape code when
its actual packed label follows the failure continuation. Body execution
preserves it, including all restored temporary graph/pointer exchanges. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))+5 ≤ l.sourceTransition) :
    ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v := by
  have large : 10 ≤ nodeSpan mode := by cases mode <;> decide
  have tapeOutside : l.sourceNode+10 ≤ l.sourceTransition ∨ l.sourceTransition+transitionSpan mode ≤ l.sourceNode+6 := by
    rcases r.sources with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [Listing8GlobalJump.bodyEnd,Listing8GlobalBoot.finish,
    Listing8LateFrames.after_failure mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _ _ _ after tapeOutside]
  exact initial_current mode l t v sentinel (Listing8BootImage.beginPC mode origin) _

theorem after_fail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin) :
    ByteMemory.bytesAt (Listing8FailReturn.finish mode origin l t v sentinel memory seed).principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v := by
  rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed]
  apply current mode origin l t v sentinel r owners copies body
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5 ≤ l.sourceTransition
  rw [Listing8JumpImage.call_position mode origin l t sentinel boot body,located]
  dsimp [Listing8FailLayout.endPC,Listing8JumpLayout.failPC];omega
end SmcTuring.Appendix.Listing8TransitionSource
