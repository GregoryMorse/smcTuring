module
public import SmcTuring.Appendix.Listing9TMFixedReadOutput
public import SmcTuring.Appendix.Listing9CanonicalMapping
public import SmcTuring.Native.StringReadPermissions
public import SmcTuring.Native.StringTraceChecks

public section
namespace SmcTuring.Appendix.Listing9TMCheckedReadAccess
open Native Listing8SourceGraph Listing8TMRules Listing8TMWindow Listing8TMRun Listing9TMStaticExecution
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

set_option maxHeartbeats 1000000 in
/-- Instantiate the actual finite-input interpreter using only original
source execution, numeric capacity/reach and a static effective mapping.
Every reached instruction fetches current memory and performs a nonempty
complete canonical, writable store in the original emitted interval. Every
computed complete data-read window is contained, canonical and readable.
The final PC is a valid observation boundary, without a physical halt claim. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (environment : MappedExecution.Environment)
    (canonical : mode=.x64 → Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length))<AddressSpace.half environment.paging ∨ AddressSpace.highStart environment.paging≤start)
    (readable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)) → environment.readable address=true)
    (writable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)) → environment.writable address=true)
    (executable : ∀ address, start≤address → address<Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)) → environment.executable address=true)
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
      (∀ observed : Int, Listing8TMFixedObservation.observe mode (Listing9PackedLayout.origin mode start)
        (lower (TM.initialConfiguration machine input) (count+input.length)) machine.blank
        (states*(alphabet+1)) (width (count+input.length))
        finalState.principal.memory observed=encode (finish.tape observed)) ∧
      AddressSpace.Valid mode environment.paging finalState.principal.pc.toNat ∧
      (∀ before form after, before++form::after=(prefixCode++Listing9Storage.program mode start (states*(alphabet+1)) (width (count+input.length))) →
        ∃ reached, StringStack.Trace mode (Listing9ExecutionImage.initial mode start (bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length)) (bodyTargets mode start) (initialGraph machine (TM.initialConfiguration machine input) (count+input.length)) (firstNode (count+input.length)) (entry (TM.initialConfiguration machine input).state) memory seed) before reached ∧
          StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
          StringWrites.CodeWrite mode start (Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length))) form reached ∧
          MappedExecution.Window mode environment .write (StringWrites.packet mode form reached).address
            (StringWrites.packet mode form reached).bytes.length ∧
          StringReadWindows.Within mode ⟨start,(Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (width (count+input.length)))⟩ form reached ∧
          StringReadPermissions.Allowed mode environment form reached ∧
          StringStack.Trace mode (StringStack.execute mode form reached) after finalState) := by
  obtain ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,firstReads,restoredAX,
    fullTrace,fullOwned,fullReads,finalPC,length,finalAX,symbols,head,rules,sp,si,di,df,cf,exterior,output⟩:=
    Listing9TMFixedReadOutput.complete_input machine capacity input finish count actual halted mode start capacityBytes reach memory seed
  have bounds:=Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (width (count+input.length)) capacityBytes reach
  have mapping:=Listing9CanonicalMapping.mapped mode environment start (states*(alphabet+1)) (width (count+input.length)) bounds
    (fun long => (canonical long).imp Nat.le_of_lt id) readable writable executable
  refine ⟨iterations,lastNode,restored,finalState,prefixCode,bounded,lastHead,firstTrace,firstReads,restoredAX,
    fullTrace,fullOwned,fullReads,finalPC,length,finalAX,symbols,head,rules,sp,si,di,df,cf,exterior,output,?_,?_⟩
  · rw [finalPC]
    exact Listing9CanonicalMapping.endpoint_valid mode environment.paging start (states*(alphabet+1)) (width (count+input.length)) bounds canonical
  · intro before form after cut
    exact StringReadPermissions.next_access mode environment start _ mapping fullTrace fullOwned fullReads before form after cut

end SmcTuring.Appendix.Listing9TMCheckedReadAccess
