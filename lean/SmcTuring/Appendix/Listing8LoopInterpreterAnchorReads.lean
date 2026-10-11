module
public import SmcTuring.Appendix.Listing8LoopInterpreterReads
public import SmcTuring.Appendix.Listing8GraphReturnReads

public section
namespace SmcTuring.Appendix.Listing8LoopInterpreterAnchorReads
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

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
      StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) code
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
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
  have first:=Listing8GraphReturnWrites.trace mode origin l t g node rule ctx memory seed nonhalt
  have registers:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  obtain ⟨finalState,tail,actual,tailOwned,tailReads,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry⟩:=
    Listing8LoopInterpreterReads.execute mode origin t logical halted (nextLayout mode origin l g node rule target)
      (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
      (Listing8LoopHaltImage.after_backedge mode origin l t g node rule target ctx selected memory seed)
  rw [show (Listing8GraphStep.updated g node rule).transitions=g.transitions from rfl,
    show (Listing8GraphStep.updated g node rule).nodes=g.nodes from rfl] at tailOwned tailReads
  have original:=rules
  rw [Listing8TransitionTable.Initial,Listing8MainGraphTable.updated_table_bytes] at original
  refine ⟨finalState,Listing8GraphReturnWrites.program mode origin l t g node rule memory seed++tail,
    StringStack.trace_append mode first actual,?_,?_,endpoint,?_,nodes,original,symbols,head,
    stack.trans registers.2.1,source.trans registers.2.2.1,destination.trans registers.2.2.2.1,forward,carry⟩
  · with_reducible
      exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
        (Listing8GraphReturnWrites.program mode origin l t g node rule memory seed) tail
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
        (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) first
        (Listing8GraphReturnWrites.owned mode origin l t g node rule ctx memory seed nonhalt) tailOwned
  · exact StringReadRuns.append_trace mode _ _ _ _ _ first
      (Listing8GraphReturnReads.contained mode origin l t g node rule ctx memory seed nonhalt) tailReads
  · rw [List.length_append,Listing8GraphReturnWrites.instruction_count,length]
    omega

end SmcTuring.Appendix.Listing8LoopInterpreterAnchorReads
