module
public import SmcTuring.Appendix.Listing8TableResetImage

public section
namespace SmcTuring.Appendix.Listing8FullTableReset
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTable.initial mode origin l t v sentinel table (Listing8TableResetImage.backing mode origin l sentinel table memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTable.failed mode origin l t v sentinel table (Listing8TableResetImage.backing mode origin l sentinel table memory) seed
@[expose] def entryState (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTable.finish mode origin l t v sentinel table (Listing8TableResetImage.backing mode origin l sentinel table memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8ResetEffects.finish mode (Listing8TableResetImage.region mode origin l sentinel table)
    (entryState mode origin l t v sentinel table memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTable.program mode origin l t v sentinel table (Listing8TableResetImage.backing mode origin l sentinel table memory) seed++
    ((Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l sentinel table)).map StringControl.Form.previous).map StringStack.Form.previous

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (isFailed : failed mode origin l t v sentinel table memory seed=true) :
    StringStack.Trace mode (initial mode origin l t v sentinel table memory seed)
      (program mode origin l t v sentinel table memory seed) (finish mode origin l t v sentinel table memory seed) := by
  have first:=Listing8FullTable.trace mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed isFailed
  have entry : (entryState mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l sentinel table).start :=
    (Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed).1
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (Listing8ResetTrace.trace mode (Listing8TableResetImage.region mode origin l sentinel table) bounds.reset _ entry
      (Listing8TableResetImage.current mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed)))
  exact StringStack.trace_append mode first last

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t v sentinel table memory seed=
      {entryState mode origin l t v sentinel table memory seed with principal:={(entryState mode origin l t v sentinel table memory seed).principal with
        pc:=Arithmetic.encodeNat mode (Listing8ResetLayout.endPC mode (Listing8TableResetImage.region mode origin l sentinel table))
        accumulator:=StringInit.accumulator mode (Listing8FullTableImage.start mode origin)
          (Listing8ResetEffects.afterInput mode (Listing8TableResetImage.region mode origin l sentinel table)
            (entryState mode origin l t v sentinel table memory seed))
        memory:=ByteMemory.putWord mode
          (ByteMemory.putWord mode (DwordCode.put (entryState mode origin l t v sentinel table memory seed).principal.memory
            (Listing8JumpLayout.callPC mode origin+1) (Listing8ResetLayout.original (Listing8TableResetImage.region mode origin l sentinel table)))
            l.input.cursor (Arithmetic.encodeNat mode sentinel))
          (Listing8StateGeometry.region mode l).cursor (Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin))}} := by
  have entry : (entryState mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l sentinel table).start :=
    (Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed).1
  have source : MixedMemory.getWord mode (entryState mode origin l t v sentinel table memory seed).principal.memory
      (Listing8TableResetImage.region mode origin l sentinel table).inputSource=Arithmetic.encodeNat mode sentinel := by
    rw [entryState,(Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed).2.1]
    exact Listing8RetainedInputSource.body_value mode origin l t v sentinel r owners copies body _ seed
  rw [finish,Listing8ResetEffects.effect mode (Listing8TableResetImage.region mode origin l sentinel table) bounds.reset _ entry
    (Listing8TableResetImage.current mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed),source]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel table memory seed).length=(if mode=.x86 then 156 else 207)+11*table.length := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8FullTable.instruction_count,Listing8ResetLayout.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (origin+(if mode=.x86 then 901 else 1399)+table.length*Listing8Prototypes.transitionSpan mode) := by
  rw [effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    Listing8TableResetImage.endpoint_offset]
end SmcTuring.Appendix.Listing8FullTableReset
