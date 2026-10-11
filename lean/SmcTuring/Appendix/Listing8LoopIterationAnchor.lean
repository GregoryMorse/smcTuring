module
public import SmcTuring.Appendix.Listing8LoopIteration
public import SmcTuring.Appendix.Listing8LoopBackedgeControlImage

public section
namespace SmcTuring.Appendix.Listing8LoopIterationAnchor
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Arbitrarily many logical nonhalting iterations are realized after the
actual first return from one original initialization, with the whole generic
main-entry invariant reconstructed at every iteration. No host reset occurs. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    {count : Nat} {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target count lastGraph lastNode lastRule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopControl.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code lastState ∧
      code.length=(if mode=.x86 then 147 else 195)+count*(if mode=.x86 then 139 else 182) ∧
      lastState.principal.stack=seed.principal.stack ∧ lastState.sourceIndex=seed.sourceIndex ∧ lastState.destinationIndex=seed.destinationIndex := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  have first:=Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt
  have prior:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  obtain ⟨lastL,lastOld,lastState,tail,lastCtx,lastImage,lastTrace,lastLength,stack,source,destination⟩:=
    Listing8LoopIteration.execute mode origin t logical (nextLayout mode origin l g node rule target)
      (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
      (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)
  refine ⟨lastL,lastOld,lastState,Listing8GraphBackedge.program mode origin l t g node rule memory seed++tail,
    lastCtx,lastImage,StringStack.trace_append mode first lastTrace,?_,stack.trans prior.2.1,
    source.trans prior.2.2.1,destination.trans prior.2.2.2.1⟩
  rw [List.length_append,Listing8GraphBackedge.instruction_count,lastLength]

end SmcTuring.Appendix.Listing8LoopIterationAnchor
