module
public import SmcTuring.Appendix.Listing9TMExecutionReads
public import SmcTuring.Appendix.Listing9TMStaticExecution
public import SmcTuring.Appendix.Listing9PackedCapacity

public section
namespace SmcTuring.Appendix.Listing9TMStaticExecutionReads
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun Listing9TMStaticExecution
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

set_option maxHeartbeats 1000000 in
/-- Numeric native capacity and RIP extent suffice: the original packed
layout, all helper targets and every resource/Context field are constructed.
Source execution derives the complete emitted trace, full store ownership,
terminal finite-window tape/head output and precise accumulator effects. -/
theorem execute {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (source finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count source=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      width count*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+width count*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (iterations : Nat) (lastNode : Fin (width count)) (restored finalState : StringExecution.State mode)
      (prefixCode : List (StringStack.Form mode)),
      iterations≤count*alphabet+alphabet ∧ position (lower source count) lastNode=finish.head ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count) (firstNode count) (entry source.state) memory seed)
        prefixCode restored ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count))⟩
        prefixCode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count) (firstNode count) (entry source.state) memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count) (firstNode count) (entry source.state) memory seed)
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count)) finalState ∧
      StringWrites.OwnedRun mode start (Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count))
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count) (firstNode count) (entry source.state) memory seed) ∧
      StringReadRuns.Run mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width count))⟩
        (prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width count))
        (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count) (firstNode count) (entry source.state) memory seed) ∧
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
          ByteMemory.bytesAt (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine source count) (bodyTargets mode start) (initialGraph machine source count)
            (firstNode count) (entry source.state) memory seed).principal.memory observed size) := by
  have bounds:=Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (width count) capacityBytes reach
  have context:=Listing9PackedCapacity.context mode start (initialGraph machine source count) (firstNode count) (entry source.state) bounds
  exact Listing9TMExecutionReads.execute machine capacity source finish count actual halted mode start
    (bodyLayout mode start machine source count) (bodyTargets mode start) context bounds memory seed

end SmcTuring.Appendix.Listing9TMStaticExecutionReads
