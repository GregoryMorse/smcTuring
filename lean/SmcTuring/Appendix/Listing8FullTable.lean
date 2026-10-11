module
public import SmcTuring.Appendix.Listing8FullTableImage

public section
namespace SmcTuring.Appendix.Listing8FullTable
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.initial mode origin l t v sentinel (Listing8FullTableImage.backing mode origin table memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.failed mode origin l t v sentinel (Listing8FullTableImage.backing mode origin table memory) seed
@[expose] def entryState (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.finish mode origin l t v sentinel (Listing8FullTableImage.backing mode origin table memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8TableTrace.finish mode (Listing8FullTableImage.start mode origin) table (entryState mode origin l t v sentinel table memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.program mode origin l t v sentinel (Listing8FullTableImage.backing mode origin table memory) seed++
    ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) table).map StringControl.Form.previous).map StringStack.Form.previous

/-- Complete actual failure continuation followed by every declared original
transition. The body source can be any initial table index; fixed ttape entry
and selected source are distinct. No future table packet/trace is a premise. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8FullTableImage.Bounds mode origin l table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (isFailed : failed mode origin l t v sentinel table memory seed=true) :
    StringStack.Trace mode (initial mode origin l t v sentinel table memory seed)
      (program mode origin l t v sentinel table memory seed) (finish mode origin l t v sentinel table memory seed) := by
  have first:=Listing8FailReturn.trace mode origin l t v sentinel (Listing8FullTableImage.start mode origin)
    r owners copies boot body (Listing8FullTableImage.fail_bounds mode origin l table index v selected located bounds)
    (Listing8FullTableImage.backing mode origin table memory) seed isFailed
  have entry : (entryState mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
    rw [entryState,Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body]
    rfl
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (Listing8TableTrace.trace mode (Listing8FullTableImage.start mode origin) table bounds.valid _ entry
      (Listing8FullTableImage.after_fail mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed)))
  exact StringStack.trace_append mode first last

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8FullTableImage.Bounds mode origin l table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) table) ∧
    (finish mode origin l t v sentinel table memory seed).principal.memory=
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel
        (Listing8FailImage.backing mode origin (Listing8FullTableImage.backing mode origin table memory)) seed).principal.memory ∧
    (finish mode origin l t v sentinel table memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel table memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel table memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel table memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel table memory seed).backwards=false := by
  have entry : (entryState mode origin l t v sentinel table memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
    rw [entryState,Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body]
    rfl
  have actual:=Listing8TableTrace.result mode (Listing8FullTableImage.start mode origin) table bounds.valid _ entry
    (Listing8FullTableImage.after_fail mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed)
  change _=Arithmetic.encodeNat mode _ ∧ _=_ ∧ _=_ ∧ _=_ ∧ _=_ ∧ _=_ ∧ _=_ at actual
  have prior:=Listing8GlobalBootValues.registers mode origin l t v sentinel r owners copies body
    (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin (Listing8FullTableImage.backing mode origin table memory))) seed
  unfold entryState at actual
  unfold finish entryState
  rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body] at actual ⊢
  exact ⟨actual.1,actual.2.1,actual.2.2.1.trans prior.1,actual.2.2.2.1,
    actual.2.2.2.2.1.trans prior.2.1,actual.2.2.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.1⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel table memory seed).length=(if mode=.x86 then 147 else 195)+11*table.length := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8FailReturn.instruction_count,Listing8TableTrace.instruction_count]

theorem endpoint_offset (mode : Mode) (origin : Nat) (table : List (Values mode)) :
    Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) table=
      origin+(if mode=.x86 then 837 else 1310)+table.length*Listing8Prototypes.transitionSpan mode := by
  rw [Listing8TransitionTable.endPC,Listing8FullTableImage.start,Listing8FailLayout.end_offset]
end SmcTuring.Appendix.Listing8FullTable
