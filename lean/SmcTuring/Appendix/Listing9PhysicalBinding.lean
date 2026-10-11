module
public import SmcTuring.Appendix.Listing9SameTraceBinding
public import SmcTuring.Native.PhysicalImageBinding
public import SmcTuring.CorrectedPaper

public section
namespace SmcTuring.Appendix.Listing9PhysicalBinding
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets
abbrev initial:=Listing9ExecutionImage.initial
set_option maxHeartbeats 2000000

@[expose] def sourceInitial {alphabet states : Nat} (mode : Mode) (start : Nat)
    (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (count : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  initial mode start
    (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing9TMStaticExecution.bodyTargets mode start)
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed

/-- PRESENT physical configuration and normalized COFF/loaded image evidence.
ISA,fetch coherence,flat segments,CET-off,mapping and ABI remain explicit.
No future trace,head boundary,template validity or interpreter simulation. -/
structure Conditions {alphabet states : Nat} (mode : Mode) (start : Nat)
    (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) (count : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) where
  environment : MappedExecution.Environment
  cpu : PhysicalImageBinding.CPU mode
  mapping : MappedExecution.Mapped mode environment
    ⟨start,endPC mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))⟩
  isa : PhysicalImageBinding.ISA mode environment cpu
  object : MemoryRegion.Image ⟨start,endPC mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))⟩
  physicalStart : cpu.State
  present : PhysicalImageBinding.Present mode
    ⟨start,endPC mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))⟩ object
    (cpu.project physicalStart) (sourceInitial mode start machine input count memory seed)
  endpointCanonical : AddressSpace.Valid mode environment.paging
    (endPC mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)))

/-- Final physical/native/head/COFF binding. Actual source input and numeric
bounds derive the complete modeled trace;present object comparison and LOCAL
ISA conditions then derive its physical realization and every SAME-prefix
catalog/head/tape observation. Finite endpoint does not imply hardware RET/stop. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (conditions : Conditions mode start machine input count memory seed) :
    let radius := count+input.length
    let lower := Listing8TMRun.lower (TM.initialConfiguration machine input) radius
    let g := Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) radius
    let node := Listing8TMRun.firstNode radius
    let rule := Listing8TMRules.entry (TM.initialConfiguration machine input).state
    let lastGraph := Listing8TMWindow.graph machine lower (Listing8TMRun.width radius) (Listing8TMRun.positive radius) finish
    let lastRule := Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)
    let l := Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) radius
    let t := Listing9TMStaticExecution.bodyTargets mode start
    ∃ (iterations : Nat) (lastNode : Fin (Listing8TMRun.width radius)),
      iterations≤count*alphabet+alphabet ∧ Listing8TMWindow.position lower lastNode=finish.head ∧
    ∃ (restored finalState : StringExecution.State mode) (prefixCode body : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) prefixCode restored ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes) prefixCode
        (initial mode start l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ prefixCode
        (initial mode start l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ prefixCode
        (initial mode start l t g node rule memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      restored.principal.pc.toNat=saveOwner mode start g.transitions g.nodes ∧
      StringStack.Trace mode (initial mode start l t g node rule memory seed)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) finalState ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      (prefixCode++Listing9Storage.program mode start g.transitions g.nodes).length=
        (if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+iterations*(if mode=.x86 then 139 else 182)+
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
          ByteMemory.bytesAt (initial mode start l t g node rule memory seed).principal.memory observed size) ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) (initial mode start l t g node rule memory seed) ∧
      (∀ before after,prefixCode++Listing9Storage.program mode start g.transitions g.nodes=before++after →
        Listing9JointFullExecution.Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body before
          (StringWrites.run mode before (initial mode start l t g node rule memory seed))) ∧
      ∃ (cursor : Nat) (boundary : StringExecution.State mode) (before after : List (StringStack.Form mode)),
        prefixCode++Listing9Storage.program mode start g.transitions g.nodes=before++after ∧
        StringStack.Trace mode (initial mode start l t g node rule memory seed) before boundary ∧
        StringStack.Trace mode boundary after finalState ∧
        Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor boundary.principal.memory=
          finish.head
 ∧
        (∀ observed : Int,Listing8TMFixedObservation.observe mode (origin mode start) lower machine.blank
          (states*(alphabet+1)) (Listing8TMRun.width radius) finalState.principal.memory observed=Listing8TMRules.encode (finish.tape observed)
) ∧
        ∃ physicalFinish,
          PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart
            (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) physicalFinish ∧
          conditions.cpu.project physicalFinish=finalState ∧
          (∃ physicalRestored,
            PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart prefixCode physicalRestored ∧
            PhysicalImageBinding.Trace mode conditions.cpu physicalRestored (Listing9Storage.program mode start g.transitions g.nodes) physicalFinish ∧
            conditions.cpu.project physicalRestored=restored ∧
            (conditions.cpu.project physicalRestored).principal.accumulator=seed.principal.accumulator) ∧
          (∀ leading trailing,prefixCode++Listing9Storage.program mode start g.transitions g.nodes=leading++trailing →
            ∃ reached,PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart leading reached ∧
              PhysicalImageBinding.Trace mode conditions.cpu reached trailing physicalFinish ∧
              conditions.cpu.project reached=StringWrites.run mode leading (conditions.cpu.project conditions.physicalStart) ∧
              Listing8GlobalControlTemplates.Decodes mode (origin mode start) (conditions.cpu.project reached).principal.memory ∧
              Listing9TailTemplates.Decodes mode start g.transitions g.nodes (conditions.cpu.project reached).principal.memory ∧
              Listing9JointFullExecution.Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body leading
                (conditions.cpu.project reached)) ∧
          (∀ leading form trailing,leading++form::trailing=prefixCode++Listing9Storage.program mode start g.transitions g.nodes →
            ∃ reached,PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart leading reached ∧
              StringStack.fetch mode (conditions.cpu.project reached).principal.memory (conditions.cpu.project reached).principal.pc.toNat=some form ∧
              StringFetchWindows.Within mode ⟨start,endPC mode start g.transitions g.nodes⟩ (conditions.cpu.project reached) ∧
              StringFetchPermissions.Allowed mode conditions.environment (conditions.cpu.project reached) ∧
              StringWrites.CodeWrite mode start (endPC mode start g.transitions g.nodes) form (conditions.cpu.project reached) ∧
              MappedExecution.Window mode conditions.environment .write (StringWrites.packet mode form (conditions.cpu.project reached)).address
                (StringWrites.packet mode form (conditions.cpu.project reached)).bytes.length ∧
              StringReadWindows.Within mode ⟨start,endPC mode start g.transitions g.nodes⟩ form (conditions.cpu.project reached) ∧
              StringReadPermissions.Allowed mode conditions.environment form (conditions.cpu.project reached)) ∧
          ∃ physicalHead,
            PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart before physicalHead ∧
            PhysicalImageBinding.Trace mode conditions.cpu physicalHead after physicalFinish ∧
            conditions.cpu.project physicalHead=boundary ∧
            Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor
              (conditions.cpu.project physicalHead).principal.memory=finish.head ∧
            ∀ observed : Int,Listing8TMFixedObservation.observe mode (origin mode start) lower machine.blank
              (states*(alphabet+1)) (Listing8TMRun.width radius)
              (conditions.cpu.project physicalFinish).principal.memory observed=Listing8TMRules.encode (finish.tape observed)
 := by
  dsimp only
  obtain ⟨iterations,lastNode,bounded,lastHead,restored,finalState,prefixCode,body,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames,globalCatalogs,jointPrefixes,
    cursor,boundary,before,after,cut,reached,following,observed,tape⟩ :=
    Listing9SameTraceBinding.complete_input machine capacity input finish count actual halted mode start capacityBytes reach memory seed
  have present := PhysicalImageBinding.present_eq mode _ conditions.object _ _ conditions.present
  have finalCanonical : AddressSpace.Valid mode conditions.environment.paging finalState.principal.pc.toNat := by
    rw [endpoint];exact conditions.endpointCanonical
  obtain ⟨physicalFinish,physical,projection⟩ := PhysicalImageBinding.realize mode conditions.environment _ conditions.mapping conditions.cpu conditions.isa
    whole fetches reads owned finalCanonical conditions.physicalStart present
  refine ⟨iterations,lastNode,bounded,lastHead,restored,finalState,prefixCode,body,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames,globalCatalogs,jointPrefixes,
    cursor,boundary,before,after,cut,reached,following,observed,tape,physicalFinish,physical,projection,?_,?_,?_,?_⟩
  · obtain ⟨physicalRestored,first,last,atState⟩ := PhysicalImageBinding.at_prefix mode conditions.cpu physical prefixCode
      (Listing9Storage.program mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))) rfl
    have restoredProjection : conditions.cpu.project physicalRestored=restored := by
      rw [atState,present]
      exact StringWrites.trace_run_eq mode firstTrace
    exact ⟨physicalRestored,first,last,restoredProjection,by rw [restoredProjection];exact ax⟩
  · intro leading trailing split
    obtain ⟨reached,first,last,atState⟩ := PhysicalImageBinding.at_prefix mode conditions.cpu physical leading trailing split
    refine ⟨reached,first,last,atState,?_,?_,?_⟩
    · rw [atState,present]
      exact (StringTemplateStates.at_prefix mode _ leading trailing _ (split ▸ globalCatalogs)).1
    · rw [atState,present]
      exact (StringTemplateStates.at_prefix mode _ leading trailing _ (split ▸ globalCatalogs)).2
    · rw [atState,present]
      exact jointPrefixes leading trailing split
  · intro leading form trailing split
    obtain ⟨physicalCurrent,first,last,atState⟩ := PhysicalImageBinding.at_prefix mode conditions.cpu physical leading (form::trailing) split.symm
    obtain ⟨nativeCurrent,actualPrefix,fetched,contained,allowed,write,writeAllowed,read,readAllowed,remaining⟩ :=
      StringFetchPermissions.next_access mode conditions.environment _ _ conditions.mapping whole fetches owned reads leading form trailing split
    have sameCurrent : conditions.cpu.project physicalCurrent=nativeCurrent := by
      rw [atState,present]
      exact StringWrites.trace_run_eq mode actualPrefix
    refine ⟨physicalCurrent,first,?_,?_,?_,?_,?_,?_,?_⟩ <;> rw [sameCurrent]
    · exact fetched
    · exact contained
    · exact allowed
    · exact write
    · exact writeAllowed
    · exact read
    · exact readAllowed
  · obtain ⟨physicalHead,first,last,atState⟩ := PhysicalImageBinding.at_prefix mode conditions.cpu physical before after cut
    have headProjection : conditions.cpu.project physicalHead=boundary := by
      rw [atState,present]
      exact StringWrites.trace_run_eq mode reached
    refine ⟨physicalHead,first,last,headProjection,?_,?_⟩
    · rw [headProjection];exact observed
    · rw [projection];exact tape

/-- Final corrected-paper realization clause. Its configuration/COFF input
is present and finite;all source and physical execution conclusions are outputs. -/
@[expose] def Realization : Prop := ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (_capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (_actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (_halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (_capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (_reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (conditions : Conditions mode start machine input count memory seed),
    let radius := count+input.length
    let lower := Listing8TMRun.lower (TM.initialConfiguration machine input) radius
    let g := Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) radius
    let node := Listing8TMRun.firstNode radius
    let rule := Listing8TMRules.entry (TM.initialConfiguration machine input).state
    let lastGraph := Listing8TMWindow.graph machine lower (Listing8TMRun.width radius) (Listing8TMRun.positive radius) finish
    let lastRule := Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)
    let l := Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) radius
    let t := Listing9TMStaticExecution.bodyTargets mode start
    ∃ (iterations : Nat) (lastNode : Fin (Listing8TMRun.width radius)),
      iterations≤count*alphabet+alphabet ∧ Listing8TMWindow.position lower lastNode=finish.head ∧
    ∃ (restored finalState : StringExecution.State mode) (prefixCode body : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) prefixCode restored ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes) prefixCode
        (initial mode start l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ prefixCode
        (initial mode start l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩ prefixCode
        (initial mode start l t g node rule memory seed) ∧
      restored.principal.accumulator=seed.principal.accumulator ∧
      restored.principal.pc.toNat=saveOwner mode start g.transitions g.nodes ∧
      StringStack.Trace mode (initial mode start l t g node rule memory seed)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) finalState ∧
      StringWrites.OwnedRun mode start (endPC mode start g.transitions g.nodes)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      StringReadRuns.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      StringFetchWindows.Run mode ⟨start,endPC mode start g.transitions g.nodes⟩
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes)
        (initial mode start l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      (prefixCode++Listing9Storage.program mode start g.transitions g.nodes).length=
        (if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+iterations*(if mode=.x86 then 139 else 182)+
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
          ByteMemory.bytesAt (initial mode start l t g node rule memory seed).principal.memory observed size) ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory)
        (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) (initial mode start l t g node rule memory seed) ∧
      (∀ before after,prefixCode++Listing9Storage.program mode start g.transitions g.nodes=before++after →
        Listing9JointFullExecution.Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body before
          (StringWrites.run mode before (initial mode start l t g node rule memory seed))) ∧
      ∃ (cursor : Nat) (boundary : StringExecution.State mode) (before after : List (StringStack.Form mode)),
        prefixCode++Listing9Storage.program mode start g.transitions g.nodes=before++after ∧
        StringStack.Trace mode (initial mode start l t g node rule memory seed) before boundary ∧
        StringStack.Trace mode boundary after finalState ∧
        Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor boundary.principal.memory=
          finish.head
 ∧
        (∀ observed : Int,Listing8TMFixedObservation.observe mode (origin mode start) lower machine.blank
          (states*(alphabet+1)) (Listing8TMRun.width radius) finalState.principal.memory observed=Listing8TMRules.encode (finish.tape observed)
) ∧
        ∃ physicalFinish,
          PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart
            (prefixCode++Listing9Storage.program mode start g.transitions g.nodes) physicalFinish ∧
          conditions.cpu.project physicalFinish=finalState ∧
          (∃ physicalRestored,
            PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart prefixCode physicalRestored ∧
            PhysicalImageBinding.Trace mode conditions.cpu physicalRestored (Listing9Storage.program mode start g.transitions g.nodes) physicalFinish ∧
            conditions.cpu.project physicalRestored=restored ∧
            (conditions.cpu.project physicalRestored).principal.accumulator=seed.principal.accumulator) ∧
          (∀ leading trailing,prefixCode++Listing9Storage.program mode start g.transitions g.nodes=leading++trailing →
            ∃ reached,PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart leading reached ∧
              PhysicalImageBinding.Trace mode conditions.cpu reached trailing physicalFinish ∧
              conditions.cpu.project reached=StringWrites.run mode leading (conditions.cpu.project conditions.physicalStart) ∧
              Listing8GlobalControlTemplates.Decodes mode (origin mode start) (conditions.cpu.project reached).principal.memory ∧
              Listing9TailTemplates.Decodes mode start g.transitions g.nodes (conditions.cpu.project reached).principal.memory ∧
              Listing9JointFullExecution.Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body leading
                (conditions.cpu.project reached)) ∧
          (∀ leading form trailing,leading++form::trailing=prefixCode++Listing9Storage.program mode start g.transitions g.nodes →
            ∃ reached,PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart leading reached ∧
              StringStack.fetch mode (conditions.cpu.project reached).principal.memory (conditions.cpu.project reached).principal.pc.toNat=some form ∧
              StringFetchWindows.Within mode ⟨start,endPC mode start g.transitions g.nodes⟩ (conditions.cpu.project reached) ∧
              StringFetchPermissions.Allowed mode conditions.environment (conditions.cpu.project reached) ∧
              StringWrites.CodeWrite mode start (endPC mode start g.transitions g.nodes) form (conditions.cpu.project reached) ∧
              MappedExecution.Window mode conditions.environment .write (StringWrites.packet mode form (conditions.cpu.project reached)).address
                (StringWrites.packet mode form (conditions.cpu.project reached)).bytes.length ∧
              StringReadWindows.Within mode ⟨start,endPC mode start g.transitions g.nodes⟩ form (conditions.cpu.project reached) ∧
              StringReadPermissions.Allowed mode conditions.environment form (conditions.cpu.project reached)) ∧
          ∃ physicalHead,
            PhysicalImageBinding.Trace mode conditions.cpu conditions.physicalStart before physicalHead ∧
            PhysicalImageBinding.Trace mode conditions.cpu physicalHead after physicalFinish ∧
            conditions.cpu.project physicalHead=boundary ∧
            Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor
              (conditions.cpu.project physicalHead).principal.memory=finish.head ∧
            ∀ observed : Int,Listing8TMFixedObservation.observe mode (origin mode start) lower machine.blank
              (states*(alphabet+1)) (Listing8TMRun.width radius)
              (conditions.cpu.project physicalFinish).principal.memory observed=Listing8TMRules.encode (finish.tape observed)


/-- Final mathematical/binding umbrella. Cold replay and actual Windows/native
CI acceptance remain validation gates;physical endpoint does not assert RET. -/
theorem full_paper : CorrectedPaper.Statement ∧ Realization := by
  refine ⟨CorrectedPaper.full_paper,?_⟩
  intro alphabet states machine capacity input finish count actual halted mode start capacityBytes reach memory seed conditions
  exact complete_input machine capacity input finish count actual halted mode start capacityBytes reach memory seed conditions

end SmcTuring.Appendix.Listing9PhysicalBinding
