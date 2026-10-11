module
public import SmcTuring.Appendix.Listing9FullExecution
public import SmcTuring.Appendix.Listing9StorageWrites

public section
namespace SmcTuring.Appendix.Listing9FullStorageWrites
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The complete one-initialization trace reaches both declaration packets
with every reached write wholly in their emitted code. The ownership contract
is positively constructed from retained bytes/static bounds, not a hypothesis.
Whole Listing 8 body ownership remains a separate obligation. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (restored finalState : StringExecution.State mode) (prefixCode : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed) prefixCode restored ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) finalState ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      StringWrites.OwnedRun mode (saveOwner mode start g.transitions g.nodes) (endPC mode start g.transitions g.nodes)
        (Listing9Storage.program mode start g.transitions g.nodes) restored ∧
      finalState.principal.memory=restored.principal.memory := by
  obtain ⟨restored,finalState,prefixCode,first,ax,location,actual,endpoint,_,_,memorySame,_,_,_,_,_,_,_,_,_,frames⟩:=
    Listing9FullExecution.execute mode start l t logical halted ctx bounds memory seed
  have packets:=Listing9Storage.current_of_retained mode start g.transitions g.nodes memory finalState.principal.memory frames
  rw [memorySame] at packets
  have entry : restored.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start g.transitions g.nodes) := by
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) location
  exact ⟨restored,finalState,prefixCode,first,ax,actual,endpoint,
    Listing9StorageWrites.owned mode start g.transitions g.nodes bounds restored entry packets,memorySame⟩

end SmcTuring.Appendix.Listing9FullStorageWrites
