module
public import SmcTuring.Appendix.Listing8FailTransition
public import SmcTuring.Appendix.Listing8OriginalOwnerValues

public section
namespace SmcTuring.Appendix.Listing8FailTransitionValues
open Native Listing8CopyImage Listing8FailTransition
abbrev Targets:=Listing8PointerCopies.Targets
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode (origin+(if mode=.x86 then 903 else 1394)) := by
  rw [(result mode origin l t v sentinel r owners copies boot body located block memory seed).1,endpoint_offset mode origin l located]

theorem accumulator (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.accumulator=
      Execution.load mode (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed).principal.memory v.newState := by
  have entry : (Listing8FailReturn.finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode l.sourceTransition := by
    rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed,located]
  rw [finish,Listing8OriginalOwnerValues.transition_accumulator mode l.sourceTransition v block _ entry
    (Listing8TransitionSource.after_fail mode origin l t v sentinel r owners copies boot body memory seed located),
    Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed]

theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next := by
  rw [(result mode origin l t v sentinel r owners copies boot body located block memory seed).2.1]
  exact Listing8GlobalBootValues.transition mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction=if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward) else Arithmetic.encodeNat mode l.sourceNode := by
  rw [(result mode origin l t v sentinel r owners copies boot body located block memory seed).2.1]
  exact Listing8GlobalBootValues.head mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed takeBack encoded

theorem tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode origin l t v sentinel memory seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  rw [(result mode origin l t v sentinel r owners copies boot body located block memory seed).2.1]
  exact Listing8GlobalBootValues.tape mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed
end SmcTuring.Appendix.Listing8FailTransitionValues
