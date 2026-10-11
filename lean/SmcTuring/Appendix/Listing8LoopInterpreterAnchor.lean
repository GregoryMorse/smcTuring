module
public import SmcTuring.Appendix.Listing8LoopInterpreter

public section
namespace SmcTuring.Appendix.Listing8LoopInterpreterAnchor
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

/-- One original initialization reaches the actual first return, then any
finite logical continuation through declared halt, table/reset/DOHALT and all
updated input declarations. There is no intervening host initialization. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    {count : Nat} {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code finalState ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=(if mode=.x86 then 147 else 195)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro firstHalted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr firstHalted
    rw [selected] at none
    cases none
  have first:=Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt
  have registers:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  obtain ⟨finalState,tail,actual,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry⟩:=
    Listing8LoopInterpreter.execute mode origin t logical halted (nextLayout mode origin l g node rule target)
      (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
      (Listing8LoopHaltImage.after_backedge mode origin l t g node rule target ctx selected memory seed)
  have original:=rules
  rw [Listing8TransitionTable.Initial,Listing8MainGraphTable.updated_table_bytes] at original
  refine ⟨finalState,Listing8GraphBackedge.program mode origin l t g node rule memory seed++tail,
    StringStack.trace_append mode first actual,endpoint,?_,nodes,original,symbols,head,
    stack.trans registers.2.1,source.trans registers.2.2.1,destination.trans registers.2.2.2.1,forward,carry⟩
  rw [List.length_append,Listing8GraphBackedge.instruction_count,length]
  omega

end SmcTuring.Appendix.Listing8LoopInterpreterAnchor
