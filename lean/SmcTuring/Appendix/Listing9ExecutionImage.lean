module
public import SmcTuring.Appendix.Listing9Image
public import SmcTuring.Appendix.Listing9FinalImage

public section
namespace SmcTuring.Appendix.Listing9ExecutionImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def initial (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8AccumulatorEntry.initial mode (origin mode start) l t g node rule (layout mode start g.transitions g.nodes)
    (Listing9Image.memory mode start g.transitions g.nodes backing) seed

theorem prologue_current (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Context mode (origin mode start) l t g node rule) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (initial mode start l t g node rule backing seed).principal.memory start
      (Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))).length=
      Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes)) := by
  have before : start+(Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))).length≤origin mode start := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode (layout mode start g.transitions g.nodes)).1]
    exact Nat.le_refl _
  change ByteMemory.bytesAt (Listing8GraphBackedge.initial mode (origin mode start) l t g node rule (Listing9Image.memory mode start g.transitions g.nodes backing) seed).principal.memory _ _=_
  rw [Listing8LoopOriginalImage.initial_memory mode (origin mode start) l t g node rule ctx _ seed,
    Listing9EarlyImage.initial_window mode (origin mode start) l t g node rule ctx _ _ _ before]
  exact Listing9Image.prologue mode start g.transitions g.nodes backing

/-- Complete one-time emitted Listing 9 image plus the actual Listing 8 body.
All prologue/epilogue/pointer packet premises are derived from finite emitted
bytes and static placement. No initial/future packet observation is supplied. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) code finalState ∧
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
  exact Listing9FinalImage.execute mode (origin mode start) l t logical halted ctx
    (layout mode start g.transitions g.nodes) (admissible mode start g.transitions g.nodes bounds) coords.1 coords.2.1
    (by rw [coords.2.2.1];exact ordered.2.2.1)
    (by rw [coords.2.2.1];have a:=ordered.2.2.2.1;have b:=ordered.2.2.2.2.1;omega)
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (prologue_current mode start l t g node rule ctx memory seed)
    (Listing9Image.epilogue_current mode start g.transitions g.nodes memory)
    (pointerOwner mode start g.transitions g.nodes) rfl capacities.2 (Listing9Image.pointer_current mode start g.transitions g.nodes memory)

end SmcTuring.Appendix.Listing9ExecutionImage
