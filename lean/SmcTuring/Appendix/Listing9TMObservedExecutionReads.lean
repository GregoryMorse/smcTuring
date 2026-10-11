module
public import SmcTuring.Appendix.Listing9TMStaticExecutionReads
public import SmcTuring.Appendix.Listing8TMOutputWindow

public section
namespace SmcTuring.Appendix.Listing9TMObservedExecutionReads
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun Listing9TMStaticExecution
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

set_option maxHeartbeats 1000000 in
/-- Additional input/output cells are part of the original emitted graph.
The source still performs count steps; static layout/resources are constructed
from numeric capacity and RIP bounds, and every terminal window cell follows
from actual native execution. -/
theorem execute {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count padding : Nat)
    (actual : TM.run machine count source=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      width (count+padding)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+width (count+padding)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (iterations : Nat) (lastNode : Fin (width (count+padding))) (restored finalState : StringExecution.State mode)
      (prefixCode : List (StringStack.Form mode)),
      iterations≤count*alphabet+alphabet ∧ position (lower source (count+padding)) lastNode=finish.head ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) memory seed)
        prefixCode restored ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+padding)))⟩
        prefixCode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) memory seed)
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+padding))) finalState ∧
      StringWrites.OwnedRun mode start (Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+padding)))
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+padding)))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) memory seed) ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+padding)))⟩
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+padding)))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) memory seed) ∧
      finalState.principal.pc.toNat=Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+padding)) ∧
      (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+padding))).length=
        (if mode=.x86 then 162 else 219)+iterations*(if mode=.x86 then 139 else 182)+11*(states*(alphabet+1))+9*width (count+padding) ∧
      finalState.principal.accumulator=(if mode=.x86 then seed.principal.accumulator else
        Arithmetic.encodeNat mode (Listing9PackedLayout.layout mode start (states*(alphabet+1)) (width (count+padding))).save) ∧
      List.ofFn (fun query : Fin (width (count+padding)) => DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish) query+6))=
        List.ofFn (fun query : Fin (width (count+padding)) => encode (finish.tape (position (lower source (count+padding)) query))) ∧
      DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish) lastNode+6)=encode (finish.tape finish.head) ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode (Listing9PackedLayout.origin mode start))
        (table mode (Listing9PackedLayout.origin mode start) (initialGraph machine source (count+padding))) finalState.principal.memory ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧
      finalState.destinationIndex=seed.destinationIndex ∧ finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, observed+size≤start ∨ Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+padding))≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) (initialGraph machine source (count+padding))
            (firstNode (count+padding)) (entry source.state) memory seed).principal.memory observed size) := by
  have bounds:=Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (width (count+padding)) capacityBytes reach
  have context:=Listing9PackedCapacity.context mode start (initialGraph machine source (count+padding)) (firstNode (count+padding)) (entry source.state) bounds

  obtain ⟨iterations,lastNode,bounded,lastHead,logical,declaredHalt,unchanged⟩:=Listing8TMObservedRun.finite_halt machine capacity source finish count padding actual halted
  obtain ⟨restored,finalState,prefixCode,firstTrace,firstOwned,firstReads,restoredAX,restoredPC,fullTrace,fullOwned,fullReads,finalPC,length,finalAX,
    memoryEq,nodes,rules,symbols,head,sp,si,di,df,cf,frames,exterior⟩:=
    Listing9FullExecutionReads.execute mode start (bodyLayout mode start machine source (count+padding)) (bodyTargets mode start) logical declaredHalt context bounds memory seed
  have different:=terminal_symbol machine capacity finish.state
    (tape (width:=width (count+padding)) (lower source (count+padding)) finish lastNode)
  have nextNode:=Listing8TMGraph.mismatch_node machine (⟨0,positive (count+padding)⟩ : Fin (width (count+padding))) back forward
    (tape (lower source (count+padding)) finish) lastNode (index finish.state (endSlot alphabet)) different
  have finalSymbol (query : Fin (width (count+padding))) :
      ((Listing8GraphStep.updated (graph machine (lower source (count+padding)) (width (count+padding)) (positive (count+padding)) finish)
        lastNode (index finish.state (endSlot alphabet))).tape query).symbol=
        encode (finish.tape (position (lower source (count+padding)) query)) :=
    Listing8TMGraph.mismatch_symbol machine _ back forward _ lastNode _ different query
  refine ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,firstReads,restoredAX,
    fullTrace,fullOwned,fullReads,finalPC,?_,finalAX,?_,?_,rules,sp,si,di,df,cf,exterior⟩
  · rw [length]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  · simpa only [finalSymbol] using symbols
  · simpa only [nextNode,finalSymbol,lastHead] using head


set_option maxHeartbeats 1000000 in
/-- One finite input is entirely included in the emitted graph. The final
observation equals the complete two-sided terminal TM tape, including proved
blank exterior cells, with all trace/ownership/register conclusions retained. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (iterations : Nat) (lastNode : Fin (width (count+input.length))) (restored finalState : StringExecution.State mode)
      (prefixCode : List (StringStack.Form mode)),
      iterations≤count*alphabet+alphabet ∧ position (lower (TM.initialConfiguration machine input) (count+input.length)) lastNode=finish.head ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed)
        prefixCode restored ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)))⟩
        prefixCode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed)
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+input.length))) finalState ∧
      StringWrites.OwnedRun mode start (Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)))
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+input.length)))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed) ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)))⟩
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+input.length)))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed) ∧
      finalState.principal.pc.toNat=Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)) ∧
      (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+input.length))).length=
        (if mode=.x86 then 162 else 219)+iterations*(if mode=.x86 then 139 else 182)+11*(states*(alphabet+1))+9*width (count+input.length) ∧
      finalState.principal.accumulator=(if mode=.x86 then seed.principal.accumulator else
        Arithmetic.encodeNat mode (Listing9PackedLayout.layout mode start (states*(alphabet+1)) (width (count+input.length))).save) ∧
      List.ofFn (fun query : Fin (width (count+input.length)) => DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower (TM.initialConfiguration machine input) (count+input.length)) (width (count+input.length)) (positive (count+input.length)) finish) query+6))=
        List.ofFn (fun query : Fin (width (count+input.length)) => encode (finish.tape (position (lower (TM.initialConfiguration machine input) (count+input.length)) query))) ∧
      DwordCode.get finalState.principal.memory
        (nodePC mode (Listing9PackedLayout.origin mode start)
          (graph machine (lower (TM.initialConfiguration machine input) (count+input.length)) (width (count+input.length)) (positive (count+input.length)) finish) lastNode+6)=encode (finish.tape finish.head) ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode (Listing9PackedLayout.origin mode start))
        (table mode (Listing9PackedLayout.origin mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length))) finalState.principal.memory ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧
      finalState.destinationIndex=seed.destinationIndex ∧ finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, observed+size≤start ∨ Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length))≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
            (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed).principal.memory observed size) ∧
      (∀ observed : Int, Listing8TMOutputWindow.observe mode (Listing9PackedLayout.origin mode start)
        (lower (TM.initialConfiguration machine input) (count+input.length)) machine.blank
        (graph machine (lower (TM.initialConfiguration machine input) (count+input.length)) (width (count+input.length)) (positive (count+input.length)) finish)
        finalState.principal.memory observed=encode (finish.tape observed)) := by
  obtain ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,firstReads,restoredAX,
    fullTrace,fullOwned,fullReads,finalPC,length,finalAX,symbols,head,rules,sp,si,di,df,cf,exterior⟩:=
    execute machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted mode start capacityBytes reach memory seed
  refine ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,firstReads,restoredAX,
    fullTrace,fullOwned,fullReads,finalPC,length,finalAX,symbols,head,rules,sp,si,di,df,cf,exterior,?_⟩
  have cells (query : Fin (width (count+input.length))) :
      DwordCode.get finalState.principal.memory (nodePC mode (Listing9PackedLayout.origin mode start)
        (graph machine (lower (TM.initialConfiguration machine input) (count+input.length))
          (width (count+input.length)) (positive (count+input.length)) finish) query+6)=
        encode (finish.tape (position (lower (TM.initialConfiguration machine input) (count+input.length)) query)) := by
    have observed:=congrArg (fun values : List (BitVec 32) => values[query.val]?) symbols
    simp only [List.getElem?_ofFn,query.isLt,dite_true] at observed
    exact Option.some.inj observed
  intro observed
  exact Listing8TMOutputWindow.reconstruct mode (Listing9PackedLayout.origin mode start)
    (lower (TM.initialConfiguration machine input) (count+input.length)) machine.blank _ finalState.principal.memory finish cells
    (fun query outside => Listing8TMOutputWindow.terminal_outside_blank machine input finish count actual query outside) observed

end SmcTuring.Appendix.Listing9TMObservedExecutionReads
