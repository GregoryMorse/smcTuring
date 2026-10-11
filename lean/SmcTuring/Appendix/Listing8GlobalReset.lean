module
public import SmcTuring.Appendix.Listing8ResetGeometry

public section
namespace SmcTuring.Appendix.Listing8GlobalReset
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.initial mode origin l t v sentinel (Listing8ResetImage.backing mode origin l sentinel memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.failed mode origin l t v sentinel (Listing8ResetImage.backing mode origin l sentinel memory) seed
@[expose] def entryState (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailTransition.finish mode origin l t v sentinel (Listing8ResetImage.backing mode origin l sentinel memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8ResetEffects.finish mode (Listing8ResetImage.region mode origin l sentinel) (entryState mode origin l t v sentinel memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailTransition.program mode origin l t v sentinel (Listing8ResetImage.backing mode origin l sentinel memory) seed++
    ((Listing8ResetLayout.program mode (Listing8ResetImage.region mode origin l sentinel)).map StringControl.Form.previous).map StringStack.Form.previous

/-- One initialized image executes the actual bootstrap, body, computed
failure CALL/target, original ttape declaration, printed resets and DOHALT.
Every future packet and saved source value is positively derived. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (isFailed : failed mode origin l t v sentinel memory seed=true) :
    StringStack.Trace mode (initial mode origin l t v sentinel memory seed) (program mode origin l t v sentinel memory seed)
      (finish mode origin l t v sentinel memory seed) := by
  have first:=Listing8FailTransition.trace mode origin l t v sentinel r owners copies boot body located block _ seed isFailed
  have entry : (entryState mode origin l t v sentinel memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8ResetImage.region mode origin l sentinel).start :=
    (Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block _ seed).1
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (Listing8ResetTrace.trace mode (Listing8ResetImage.region mode origin l sentinel) bounds.reset _ entry
      (Listing8ResetImage.current mode origin l t v sentinel r owners copies boot body located block bounds memory seed)))
  exact StringStack.trace_append mode first last

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t v sentinel memory seed=
      {entryState mode origin l t v sentinel memory seed with principal:={(entryState mode origin l t v sentinel memory seed).principal with
        pc:=Arithmetic.encodeNat mode (Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel))
        accumulator:=StringInit.accumulator mode l.sourceTransition
          (Listing8ResetEffects.afterInput mode (Listing8ResetImage.region mode origin l sentinel) (entryState mode origin l t v sentinel memory seed))
        memory:=ByteMemory.putWord mode
          (ByteMemory.putWord mode
            (DwordCode.put (entryState mode origin l t v sentinel memory seed).principal.memory
              (Listing8JumpLayout.callPC mode origin+1) (Listing8ResetLayout.original (Listing8ResetImage.region mode origin l sentinel)))
            l.input.cursor (Arithmetic.encodeNat mode sentinel))
          (Listing8StateGeometry.region mode l).cursor (Arithmetic.encodeNat mode l.sourceTransition)}} := by
  have entry : (entryState mode origin l t v sentinel memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8ResetImage.region mode origin l sentinel).start :=
    (Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block _ seed).1
  have source : MixedMemory.getWord mode (entryState mode origin l t v sentinel memory seed).principal.memory
      (Listing8ResetImage.region mode origin l sentinel).inputSource=Arithmetic.encodeNat mode sentinel :=
    Listing8RetainedInputSource.after_ttape mode origin l t v sentinel r owners copies boot body located block _ seed
  rw [finish,Listing8ResetEffects.effect mode (Listing8ResetImage.region mode origin l sentinel) bounds.reset _ entry
    (Listing8ResetImage.current mode origin l t v sentinel r owners copies boot body located block bounds memory seed),source]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel memory seed).length=if mode=.x86 then 167 else 218 := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8FailTransition.instruction_count,
    Listing8ResetLayout.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.pc=Arithmetic.encodeNat mode (origin+(if mode=.x86 then 967 else 1483)) := by
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    Listing8ResetImage.endpoint_offset mode origin l sentinel located]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel memory seed).backwards=false := by
  have prior:=Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block
    (Listing8ResetImage.backing mode origin l sentinel memory) seed
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed]
  exact ⟨prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,prior.2.2.2.2.2.1,prior.2.2.2.2.2.2⟩
end SmcTuring.Appendix.Listing8GlobalReset
