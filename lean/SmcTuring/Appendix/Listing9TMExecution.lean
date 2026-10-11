module
public import SmcTuring.Appendix.Listing8TMRun
public import SmcTuring.Appendix.Listing9FullExecutionWrites

public section
namespace SmcTuring.Appendix.Listing9TMExecution
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun
attribute [local irreducible] StringWrites.OwnedRun
abbrev Targets:=Listing8PointerCopies.Targets

set_option maxHeartbeats 1000000 in
/-- Compile a completed source TM run and its missing transition to one actual
Listing 9 image. The interpreter trace, every complete architectural store,
whole finite terminal tape and head, final PC and accumulator effects are
conclusions. Only static native layout/capacity conditions remain explicit. -/
theorem execute {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count source=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat) (layout : Listing8CopyImage.Layout) (targets : Targets)
    (context : Listing8GraphInputContext.Context mode (Listing9PackedLayout.origin mode start) layout targets
      (initialGraph machine source count) (firstNode count) (entry source.state))
    (bounds : Listing9PackedLayout.Bounds mode start (states*(alphabet+1)) (width count))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (iterations : Nat) (lastNode : Fin (width count)) (restored finalState : StringExecution.State mode)
      (prefixCode : List (StringStack.Form mode)),
      iterations≤count*alphabet+alphabet ∧ position (lower source count) lastNode=finish.head ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start layout targets (initialGraph machine source count) (firstNode count) (entry source.state) memory seed)
        prefixCode restored ∧ restored.principal.accumulator=seed.principal.accumulator ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start layout targets (initialGraph machine source count) (firstNode count) (entry source.state) memory seed)
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count)) finalState ∧
      StringWrites.OwnedRun mode start (Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count))
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count))
        (Listing9ExecutionImage.initial mode start layout targets (initialGraph machine source count) (firstNode count) (entry source.state) memory seed) ∧
      finalState.principal.pc.toNat=Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count) ∧
      (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count)).length=
        (if mode=.x86 then 162 else 219)+iterations*(if mode=.x86 then 139 else 182)+11*(states*(alphabet+1))+9*width count ∧
      finalState.principal.accumulator=(if mode=.x86 then seed.principal.accumulator else
        Arithmetic.encodeNat mode (Listing9PackedLayout.layout mode start (states*(alphabet+1)) (width count)).save) ∧
      List.ofFn (fun query : Fin (width count) => DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower source count) (width count) (positive count) finish) query+6))=
        List.ofFn (fun query : Fin (width count) => encode (finish.tape (position (lower source count) query))) ∧
      DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower source count) (width count) (positive count) finish) lastNode+6)=encode (finish.tape finish.head) ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode (Listing9PackedLayout.origin mode start))
        (table mode (Listing9PackedLayout.origin mode start) (initialGraph machine source count)) finalState.principal.memory ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧
      finalState.destinationIndex=seed.destinationIndex ∧ finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, observed+size≤start ∨ Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count)≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (Listing9ExecutionImage.initial mode start layout targets (initialGraph machine source count)
            (firstNode count) (entry source.state) memory seed).principal.memory observed size) := by
  obtain ⟨iterations,lastNode,bounded,lastHead,logical,declaredHalt,unchanged⟩:=finite_halt machine capacity source finish count actual halted
  obtain ⟨restored,finalState,prefixCode,firstTrace,firstOwned,restoredAX,restoredPC,fullTrace,fullOwned,finalPC,length,finalAX,
    memoryEq,nodes,rules,symbols,head,sp,si,di,df,cf,frames,exterior⟩:=
    Listing9FullExecutionWrites.execute mode start layout targets logical declaredHalt context bounds memory seed
  have different:=terminal_symbol machine capacity finish.state
    (tape (width:=width count) (lower source count) finish lastNode)
  have nextNode:=Listing8TMGraph.mismatch_node machine (⟨0,positive count⟩ : Fin (width count)) back forward
    (tape (lower source count) finish) lastNode (index finish.state (endSlot alphabet)) different
  have finalSymbol (query : Fin (width count)) :
      ((Listing8GraphStep.updated (graph machine (lower source count) (width count) (positive count) finish)
        lastNode (index finish.state (endSlot alphabet))).tape query).symbol=
        encode (finish.tape (position (lower source count) query)) :=
    Listing8TMGraph.mismatch_symbol machine _ back forward _ lastNode _ different query
  refine ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,restoredAX,
    fullTrace,fullOwned,finalPC,?_,finalAX,?_,?_,rules,sp,si,di,df,cf,exterior⟩
  · rw [length]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  · simpa only [finalSymbol] using symbols
  · simpa only [nextNode,finalSymbol,lastHead] using head

end SmcTuring.Appendix.Listing9TMExecution
