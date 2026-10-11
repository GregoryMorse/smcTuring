module
public import SmcTuring.Appendix.Listing8TransitionSource
public import SmcTuring.Appendix.Listing8TransitionBlock

public section
namespace SmcTuring.Appendix.Listing8FailTransition
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8TransitionBlock.finish mode l.sourceTransition v (Listing8FailReturn.finish mode origin l t v sentinel memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.program mode origin l t v sentinel memory seed++
    ((Listing8TransitionBlock.program mode l.sourceTransition v).map StringControl.Form.previous).map StringStack.Form.previous

/-- Actual failure target followed by the printed original DEFTRANSITION,
whose bytes are the preserved initialized blueprint in this same image. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (isFailed : Listing8FailReturn.failed mode origin l t v sentinel memory seed=true) :
    StringStack.Trace mode (Listing8FailReturn.initial mode origin l t v sentinel memory seed) (program mode origin l t v sentinel memory seed)
      (finish mode origin l t v sentinel memory seed) := by
  have first:=Listing8FailReturn.trace mode origin l t v sentinel (Listing8FailLayout.endPC mode origin) r owners copies boot body
    (Listing8TransitionSource.packed_bounds mode origin l t sentinel r boot body located) memory seed isFailed
  have entry : (Listing8FailReturn.finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode l.sourceTransition := by
    rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed,located]
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (Listing8TransitionBlock.trace mode l.sourceTransition v block _ entry
      (Listing8TransitionSource.after_fail mode origin l t v sentinel r owners copies boot body memory seed located)))
  exact StringStack.trace_append mode first last

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode (l.sourceTransition+Listing8Prototypes.transitionSpan mode) ∧
    (finish mode origin l t v sentinel memory seed).principal.memory=(Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed).principal.memory ∧
    (finish mode origin l t v sentinel memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel memory seed).backwards=false := by
  have entry : (Listing8FailReturn.finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode l.sourceTransition := by
    rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed,located]
  have result:=Listing8TransitionBlock.result mode l.sourceTransition v block _ entry
    (Listing8TransitionSource.after_fail mode origin l t v sentinel r owners copies boot body memory seed located)
  rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed] at result
  have prior:=Listing8GlobalBootValues.registers mode origin l t v sentinel r owners copies body
    (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed
  unfold finish
  rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact ⟨result.1,result.2.1,result.2.2.1.trans prior.1,result.2.2.2.1,
    result.2.2.2.2.1.trans prior.2.1,result.2.2.2.2.2.1.trans prior.2.2.1,result.2.2.2.2.2.2.trans prior.2.2.2.1⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel memory seed).length=(if mode=.x86 then 158 else 206) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8FailReturn.instruction_count,Listing8TransitionBlock.instruction_count]
  cases mode <;> rfl

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout)
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin) :
    l.sourceTransition+Listing8Prototypes.transitionSpan mode=origin+(if mode=.x86 then 903 else 1394) := by
  rw [located,Listing8FailLayout.end_offset]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> rfl
end SmcTuring.Appendix.Listing8FailTransition
