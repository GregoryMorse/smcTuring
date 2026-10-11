module
public import SmcTuring.Appendix.Listing9SurroundWrites

public section
namespace SmcTuring.Appendix.Listing9BodyExitWrites
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual one-initialization body reaches the epilogue with positively
proved prologue/epilogue complete code-word writes. No future native body
state, entry value or ownership is an input. Ownership of every Listing 8
body instruction remains a separate obligation. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (body : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing9ExecutionImage.initial mode start l t g node rule memory seed) code body ∧
      body.principal.pc=Arithmetic.encodeNat mode (epilogue mode start g.transitions g.nodes) ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes)
        [StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]
        (Listing9ExecutionImage.initial mode start l t g node rule memory seed) ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes)
        (Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)) body := by
  have coords:=positions mode start g.transitions g.nodes
  have ordered:=bounds_order mode start g.transitions g.nodes
  obtain ⟨body,code,trace,entry,_⟩:=AccumulatorFinalization.body mode (origin mode start) l t logical halted ctx
    (layout mode start g.transitions g.nodes) (admissible mode start g.transitions g.nodes bounds) coords.1 coords.2.1
    (by change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).save;omega)
    (by change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).pointer;omega)
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  exact ⟨body,code,trace,entry,
    Listing9SurroundWrites.prologue mode start g.transitions g.nodes bounds _ rfl,
    Listing9SurroundWrites.epilogue mode start g.transitions g.nodes bounds body entry⟩

end SmcTuring.Appendix.Listing9BodyExitWrites
