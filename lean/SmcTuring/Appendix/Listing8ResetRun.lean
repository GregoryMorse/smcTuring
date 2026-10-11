module
public import SmcTuring.Appendix.Listing8ResetValues

public section
namespace SmcTuring.Appendix.Listing8ResetRun
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

/-- Native validity is constructed from packed positions and static capacity.
The branch condition refers only to the initial declared transition/tape
values, rather than any future trace, packet, readiness or state value. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (capacity : Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel)<2^(8*mode.wordBytes))
    (nodeOutside : l.sourceNode+Listing8Prototypes.nodeSpan mode≤(Listing8ResetImage.region mode origin l sentinel).start ∨
      Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel)≤l.sourceNode)
    (halted : (if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GlobalReset.initial mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.program mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.finish mode origin l t v sentinel memory seed) := by
  have bounds : Listing8ResetImage.Bounds mode origin l sentinel :=
    ⟨Listing8ResetGeometry.reset_bounds mode origin l t sentinel boot body located capacity,nodeOutside⟩
  have failed : Listing8GlobalReset.failed mode origin l t v sentinel memory seed=true := by
    rw [Listing8ResetValues.failure_condition mode origin l t v sentinel r owners copies body memory seed]
    simp only [halted,decide_true]
  exact Listing8GlobalReset.trace mode origin l t v sentinel r owners copies boot body located block bounds memory seed failed

/-- Coupling the itape entry to the printed position after DOHALT derives
the reset window's source-node separation. The transition blueprint is the
inline original ttape declaration, never an independently placed duplicate. -/
theorem packed_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (capacity : Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel)<2^(8*mode.wordBytes))
    (inputLocated : l.sourceNode=Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel))
    (itape : sentinel=l.sourceNode)
    (halted : (if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GlobalReset.initial mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.program mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.finish mode origin l t v sentinel memory seed) := by
  exact trace mode origin l t v sentinel r owners copies boot body located block capacity
    (Or.inr (Nat.le_of_eq inputLocated.symm)) halted memory seed

theorem packed_result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (capacity : Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel)<2^(8*mode.wordBytes))
    (inputLocated : l.sourceNode=Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel))
    (itape : sentinel=l.sourceNode)
    (halted : (if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GlobalReset.initial mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.program mode origin l t v sentinel memory seed)
      (Listing8GlobalReset.finish mode origin l t v sentinel memory seed) ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.pc.toNat=origin+(if mode=.x86 then 967 else 1483) ∧
    MixedMemory.getWord mode (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode l.sourceNode ∧
    MixedMemory.getWord mode (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.memory
      (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode l.sourceTransition ∧
    ByteMemory.bytesAt (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.memory
      (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8BootControl.region mode origin l sentinel))) ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.stack=seed.principal.stack ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).principal.carry=false ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).sourceIndex=seed.sourceIndex ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).destinationIndex=seed.destinationIndex ∧
    (Listing8GlobalReset.finish mode origin l t v sentinel memory seed).backwards=false := by
  have bounds : Listing8ResetImage.Bounds mode origin l sentinel :=
    ⟨Listing8ResetGeometry.reset_bounds mode origin l t sentinel boot body located capacity,
      Or.inr (Nat.le_of_eq inputLocated.symm)⟩
  have input:=Listing8ResetValues.input_cursor mode origin l t v sentinel r owners copies boot body located block bounds memory seed
  exact ⟨packed_trace mode origin l t v sentinel r owners copies boot body located block capacity inputLocated itape halted memory seed,
    Listing8ResetValues.terminal_boundary mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    input.trans (congrArg (Arithmetic.encodeNat mode) itape),
    Listing8ResetValues.transition_cursor mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    Listing8ResetValues.call_packet mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    Listing8GlobalReset.registers mode origin l t v sentinel r owners copies boot body located block bounds memory seed⟩
end SmcTuring.Appendix.Listing8ResetRun
