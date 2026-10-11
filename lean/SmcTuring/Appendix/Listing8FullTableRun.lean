module
public import SmcTuring.Appendix.Listing8FullTableResetValues

public section
namespace SmcTuring.Appendix.Listing8FullTableRun
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

/-- Actual full-table failure/reset/DOHALT run from declared initial fields.
The selected transition's five fields and the tape values are independent.
All native premises are static capacities, reaches and separation. -/
theorem run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (halted : (if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8FullTableReset.initial mode origin l t v sentinel table memory seed)
      (Listing8FullTableReset.program mode origin l t v sentinel table memory seed)
      (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed) ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.pc.toNat=
      origin+(if mode=.x86 then 901 else 1399)+table.length*Listing8Prototypes.transitionSpan mode ∧
    MixedMemory.getWord mode (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.memory
      l.input.cursor=Arithmetic.encodeNat mode sentinel ∧
    MixedMemory.getWord mode (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.memory
      (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.stack=seed.principal.stack ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.carry=false ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).sourceIndex=seed.sourceIndex ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).destinationIndex=seed.destinationIndex ∧
    (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).backwards=false := by
  have failed : Listing8FullTableReset.failed mode origin l t v sentinel table memory seed=true := by
    rw [Listing8FullTableResetValues.failure_condition mode origin l t v sentinel table r owners copies body memory seed]
    simp only [halted,decide_true]
  exact ⟨Listing8FullTableReset.trace mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed failed,
    Listing8FullTableResetValues.terminal_boundary mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    Listing8FullTableResetValues.input_cursor mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    Listing8FullTableResetValues.transition_cursor mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    Listing8FullTableResetValues.registers mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed⟩
end SmcTuring.Appendix.Listing8FullTableRun
