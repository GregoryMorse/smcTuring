module
public import SmcTuring.Appendix.Listing8LoopOriginalInterpreterReads
public import SmcTuring.Appendix.Listing8LoopOriginalImage
public import SmcTuring.Native.StringWriteRegions

public import SmcTuring.Appendix.Listing8LoopOriginalInterpreterFetch

public section
namespace SmcTuring.Appendix.Listing8OriginalInterpreterFetchFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run StringFetchWindows.Run
abbrev Targets := Listing8PointerCopies.Targets

/-- Complete classifier/fetch containment, ownership and exterior frames hold on the very same constructed finite
interpreter trace, without a future frame or state premise. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code finalState ∧
      StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) code
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code
        (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=ByteMemory.bytesAt memory observed size) := by
  obtain ⟨finalState,code,actual,owned,reads,fetch,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry⟩ :=
    Listing8LoopOriginalInterpreterFetch.execute mode origin l t logical halted ctx memory seed
  refine ⟨finalState,code,actual,owned,reads,fetch,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry,?_⟩
  intro observed size after
  have frame := StringWriteRegions.trace_window mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    actual owned observed size (Or.inr after)
  rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed] at frame
  exact frame.trans (Listing8LoopOriginalTailFrames.initial_window mode origin l t g node rule ctx memory seed observed size after)

end SmcTuring.Appendix.Listing8OriginalInterpreterFetchFrames
