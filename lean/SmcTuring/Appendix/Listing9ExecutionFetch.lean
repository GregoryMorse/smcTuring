module
public import SmcTuring.Appendix.Listing9FinalImageReads
public import SmcTuring.Appendix.Listing9ExecutionImage
public import SmcTuring.Appendix.Listing9SurroundWrites

public import SmcTuring.Appendix.Listing9FinalImageFetch

public section
namespace SmcTuring.Appendix.Listing9ExecutionFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run StringFetchWindows.Run
abbrev Targets := Listing8PointerCopies.Targets
abbrev initial := Listing9ExecutionImage.initial

/-- The actual emitted Listing 9 entry/body/epilogue has every actual classifier/fetch and data-read window, complete code store
ownership, exact output and full seed accumulator restoration at the epilogue boundary. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) code finalState ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes) code
        (initial mode start l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ code
        (initial mode start l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ code
        (initial mode start l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=AccumulatorLayout.endPC mode (layout mode start g.transitions g.nodes) ∧
      code.length=4+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      finalState.principal.accumulator=seed.principal.accumulator ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode (Listing9PackedLayout.origin mode start) lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode (Listing9PackedLayout.origin mode start) (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode (Listing9PackedLayout.origin mode start)) (table mode (Listing9PackedLayout.origin mode start) g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode (Listing9PackedLayout.origin mode start) lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode (Listing9PackedLayout.origin mode start) lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, saveOwner mode start g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
            (layout mode start g.transitions g.nodes).save (Arithmetic.encodeNat mode (layout mode start g.transitions g.nodes).save)) observed size) := by
  have coords:=positions mode start g.transitions g.nodes
  have ordered:=bounds_order mode start g.transitions g.nodes
  have capacities:=owner_capacity mode start g.transitions g.nodes bounds
  have fields := Listing9SurroundWrites.fields mode start g.transitions g.nodes bounds
  exact Listing9FinalImageFetch.execute mode start (endPC mode start g.transitions g.nodes) (origin mode start) l t logical halted ctx
    (layout mode start g.transitions g.nodes) (admissible mode start g.transitions g.nodes bounds)
    (Nat.le_refl _) (by
      change epilogue mode start g.transitions g.nodes≤endPC mode start g.transitions g.nodes
      omega) fields.1 fields.2 coords.1 coords.2.1
    (by rw [coords.2.2.1];exact ordered.2.2.1)
    (by rw [coords.2.2.1];have a:=ordered.2.2.2.1;have b:=ordered.2.2.2.2.1;omega)
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
    (Listing9Image.epilogue_current mode start g.transitions g.nodes memory)
    (pointerOwner mode start g.transitions g.nodes) rfl capacities.2 (Listing9Image.pointer_current mode start g.transitions g.nodes memory)

end SmcTuring.Appendix.Listing9ExecutionFetch
