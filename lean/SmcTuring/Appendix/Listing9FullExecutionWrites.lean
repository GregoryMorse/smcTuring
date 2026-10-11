module
public import SmcTuring.Appendix.Listing9Storage
public import SmcTuring.Appendix.Listing9ExecutionWrites
public import SmcTuring.Appendix.Listing9StorageWrites

public section
namespace SmcTuring.Appendix.Listing9FullExecutionWrites
attribute [local irreducible] Native.StringWrites.OwnedRun
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets
abbrev initial:=Listing9ExecutionImage.initial

/-- One fully emitted original image executes the actual entry, interpreter,
epilogue and both trailing declarations. Full seed AX is restored at the
intermediate epilogue boundary; the precise full fallthrough effect is stated.
All later native states and packet contracts are derived, not hypotheses. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (restored finalState : StringExecution.State mode) (prefixCode : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) prefixCode restored ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes) prefixCode
        (initial mode start l t g node rule memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      restored.principal.pc.toNat=saveOwner mode start g.transitions g.nodes ∧
      StringStack.Trace mode (initial mode start l t g node rule memory seed)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) finalState ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      (prefixCode++Listing9Storage.program mode start g.transitions g.nodes).length=
        (if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
          (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      finalState.principal.accumulator=(if mode=.x86 then seed.principal.accumulator else Arithmetic.encodeNat mode (layout mode start g.transitions g.nodes).save) ∧
      finalState.principal.memory=restored.principal.memory ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode (origin mode start) lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode (origin mode start) (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode (origin mode start)) (table mode (origin mode start) g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode (origin mode start) lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode (origin mode start) lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, saveOwner mode start g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
            (layout mode start g.transitions g.nodes).save (Arithmetic.encodeNat mode (layout mode start g.transitions g.nodes).save)) observed size) ∧
      (∀ observed size, observed+size≤start ∨ endPC mode start g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (initial mode start l t g node rule memory seed).principal.memory observed size) := by
  obtain ⟨restored,prefixCode,trace,prefixOwned,location,length,ax,nodes,rules,symbols,head,sp,si,di,df,cf,frames⟩:=
    Listing9ExecutionWrites.execute mode start l t logical halted ctx bounds memory seed
  have coords:=positions mode start g.transitions g.nodes
  have ordered:=bounds_order mode start g.transitions g.nodes
  rw [coords.2.2.1] at location
  have entry : restored.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start g.transitions g.nodes) := by
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) location
  have packets:=Listing9Storage.current_of_retained mode start g.transitions g.nodes memory restored.principal.memory frames
  have tail:=Listing9Storage.trace mode start g.transitions g.nodes bounds restored entry packets
  have effect:=Listing9Storage.effect mode start g.transitions g.nodes bounds restored entry packets
  refine ⟨restored,Listing9Storage.finish mode start g.transitions g.nodes restored,prefixCode,
    trace,prefixOwned,ax,location,StringStack.trace_append mode trace tail,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply StackFieldWrites.owned_append mode start (endPC mode start g.transitions g.nodes)
      prefixCode (Listing9Storage.program mode start g.transitions g.nodes)
      (initial mode start l t g node rule memory seed) restored trace prefixOwned
    exact StringWriteRegions.owned_mono mode (saveOwner mode start g.transitions g.nodes)
      (endPC mode start g.transitions g.nodes) start (endPC mode start g.transitions g.nodes)
      (by have before : start≤origin mode start := by dsimp [origin];omega
          omega) (Nat.le_refl _) _ restored
      (Listing9StorageWrites.owned mode start g.transitions g.nodes bounds restored entry packets)
  · rw [effect,Arithmetic.encode_nat_toNat mode _ bounds.capacity]
  · rw [List.length_append,length,Listing9Storage.instruction_count]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  · rw [effect,ax]
  · rw [effect]
  · rw [effect];exact nodes
  · rw [effect];exact rules
  · rw [effect];exact symbols
  · rw [effect];exact head
  · rw [effect];exact sp
  · rw [effect];exact si
  · rw [effect];exact di
  · rw [effect];exact df
  · rw [effect];exact cf
  · rw [effect];exact frames
  · intro observed size outside
    apply StringWriteRegions.trace_window mode start (endPC mode start g.transitions g.nodes)
      (StringStack.trace_append mode trace tail) _ observed size outside
    apply StackFieldWrites.owned_append mode start (endPC mode start g.transitions g.nodes)
      prefixCode (Listing9Storage.program mode start g.transitions g.nodes)
      (initial mode start l t g node rule memory seed) restored trace prefixOwned
    exact StringWriteRegions.owned_mono mode (saveOwner mode start g.transitions g.nodes)
      (endPC mode start g.transitions g.nodes) start (endPC mode start g.transitions g.nodes)
      (by have before : start≤origin mode start := by dsimp [origin];omega
          omega) (Nat.le_refl _) _ restored
      (Listing9StorageWrites.owned mode start g.transitions g.nodes bounds restored entry packets)

end SmcTuring.Appendix.Listing9FullExecutionWrites
