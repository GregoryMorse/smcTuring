module
public import SmcTuring.Appendix.Listing9JointFullExecution
public import SmcTuring.Appendix.Listing9FullExecutionFetch
public import SmcTuring.Appendix.Listing9NativeHeadObservation
public import SmcTuring.Native.StringFetchPermissions

public section
namespace SmcTuring.Appendix.Listing9SameTraceBinding
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets
abbrev initial:=Listing9ExecutionImage.initial
set_option maxHeartbeats 2000000

/-- Reuse the proved pre-cleanup decoder at a positively constructed head
cut. Its containing body has the exact source-graph instruction count. -/
theorem head_cut (mode : Mode) (start : Nat) (lower : Int) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (cursor : Nat) (boundary bodyEnd : StringExecution.State mode) (before after : List (StringStack.Form mode)),
      StringStack.Trace mode (initial mode start l t g node rule memory seed) before boundary ∧
      StringStack.Trace mode boundary after bodyEnd ∧
      Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor boundary.principal.memory=
        lower+((Listing8GraphStep.nextNode lastGraph lastNode lastRule).val : Int) ∧
      (before++after).length=1+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
        (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
  let a := layout mode start g.transitions g.nodes
  let saved := ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory) a.save seed.principal.accumulator
  have coords := positions mode start g.transitions g.nodes
  have ordered := bounds_order mode start g.transitions g.nodes
  have prologue := Listing8AccumulatorEntry.trace mode (origin mode start) l t g node rule a
    (admissible mode start g.transitions g.nodes bounds) _ seed (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  rw [Listing8AccumulatorEntry.saved_eq mode (origin mode start) l t g node rule ctx a
    (admissible mode start g.transitions g.nodes bounds) coords.1
    (by change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).save;omega) _ seed] at prologue
  have image := Listing8OriginalResetBinding.current mode (origin mode start) l t g node rule ctx saved seed
  have boot : StringStack.Trace mode (Listing8GraphBackedge.initial mode (origin mode start) l t g node rule saved seed)
      (Listing4EntryLayout.forms mode (origin mode start)) (Listing8GraphCopyWrites.afterBoot mode (origin mode start) l t g node rule saved seed) :=
    Listing4Entry.trace mode (origin mode start) (Listing8GraphCopyWrites.bootSeed mode (origin mode start) l t g node rule saved seed)
      (Listing8GlobalBoot.entry_capacity mode (origin mode start) l t _ ctx.boot ctx.body)
  obtain ⟨lastL,lastOld,lastState,passes,lastCtx,lastImage,passTrace,passLength,_,_,_⟩ :=
    Listing8LoopHaltIteration.execute mode (origin mode start) t logical l Listing8OriginalControlImage.old _ ctx image
  obtain ⟨later,cut,first,tail,head⟩ := Listing8NativeHeadBoundary.terminal mode (origin mode start) lower lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  let leading := ([StringStack.native mode (AccumulatorLayout.saveForm mode a)]++Listing4EntryLayout.forms mode (origin mode start))++passes
  have reached := StringStack.trace_append mode (StringStack.trace_append mode (StringStack.trace_append mode prologue boot) passTrace) first
  refine ⟨lastL.input.cursor,_,_,_,later,reached,tail,head,?_⟩
  change ((leading++_ )++later).length=_
  rw [List.append_assoc,←cut]
  simp only [leading,List.length_append,List.length_cons,List.length_nil,Listing4EntryLayout.instruction_count,passLength,Listing8LoopTerminal.instruction_count]
  omega

/-- Final modeled native binding:all fetch/read/store/output/register frames,
full joint purity and the pre-cleanup head cut refer to ONE actual full trace.
No future boundary,whole run or independent existential catalog is an input. -/
theorem execute (mode : Mode) (start : Nat) (lower : Int) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
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
          lower+((Listing8GraphStep.nextNode lastGraph lastNode lastRule).val : Int)
 := by
  obtain ⟨restored,finalState,prefixCode,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames⟩ :=
    Listing9FullExecutionFetch.execute mode start l t logical halted ctx bounds memory seed
  obtain ⟨jointEnd,body,jointTrace,jointPC,jointLength,globalCatalogs,jointPrefixes⟩ :=
    Listing9JointFullExecution.execute mode start l t logical halted ctx bounds memory seed
  have same := StringStackTraceDeterminism.equal_length mode _ _ _ jointEnd finalState (jointLength.trans length.symm) jointTrace whole
  obtain ⟨cursor,boundary,bodyEnd,before,after,reached,tail,observed,bodyLength⟩ := head_cut mode start lower l t logical halted ctx bounds memory seed
  have smaller : before.length≤(prefixCode++Listing9Storage.program mode start g.transitions g.nodes).length := by
    rw [List.length_append] at bodyLength
    rw [length]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at bodyLength ⊢ <;> omega
  obtain ⟨remaining,cut,following⟩ := StringStackTraceDeterminism.initial_segment mode before _ _ boundary finalState smaller reached whole
  refine ⟨restored,finalState,prefixCode,body,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames,?_,?_,cursor,boundary,before,remaining,cut,reached,following,observed⟩
  · exact same.1 ▸ globalCatalogs
  · intro before after cut
    exact jointPrefixes before after (same.1.trans cut)

/-- Final source-input binding retains all actual native and SAME-prefix
conclusions,full two-sided tape output,and a pre-cleanup native head observation
at a structural prefix of THAT very same complete emitted trace. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
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
        ∀ observed : Int,Listing8TMFixedObservation.observe mode (origin mode start) lower machine.blank
          (states*(alphabet+1)) (Listing8TMRun.width radius) finalState.principal.memory observed=Listing8TMRules.encode (finish.tape observed)
 := by
  dsimp only
  obtain ⟨iterations,lastNode,bounded,lastHead,logical,declaredHalt,unchanged⟩ :=
    Listing8TMObservedRun.finite_halt machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted
  have bounds := Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) capacityBytes reach
  have ctx := Listing9PackedCapacity.context mode start
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) bounds
  obtain ⟨restored,finalState,prefixCode,body,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames,globalCatalogs,jointPrefixes,
    cursor,boundary,before,after,cut,reached,following,observed⟩ :=
    execute mode start (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) _ _ logical declaredHalt ctx bounds memory seed
  have different := Listing8TMRules.terminal_symbol machine capacity finish.state
    (Listing8TMWindow.tape (width:=Listing8TMRun.width (count+input.length))
      (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) finish lastNode)
  have stayed := Listing8TMGraph.mismatch_node machine (⟨0,Listing8TMRun.positive (count+input.length)⟩ : Fin (Listing8TMRun.width (count+input.length)))
    Listing8TMWindow.back Listing8TMWindow.forward
    (Listing8TMWindow.tape (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) finish)
    lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) different
  rw [stayed] at observed
  refine ⟨iterations,lastNode,bounded,lastHead,restored,finalState,prefixCode,body,firstTrace,prefixOwned,prefixReads,prefixFetch,ax,location,whole,owned,reads,fetches,endpoint,length,
    finalAX,restoredMemory,nodes,rules,symbols,head,stack,source,destination,forward,carry,savedFrames,exteriorFrames,globalCatalogs,jointPrefixes,
    cursor,boundary,before,after,cut,reached,following,observed.trans lastHead,?_⟩
  have cells (query : Fin (Listing8TMRun.width (count+input.length))) :
      DwordCode.get finalState.principal.memory (nodePC mode (origin mode start)
        (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish) query+6)=
        Listing8TMRules.encode (finish.tape (Listing8TMWindow.position (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) query)) := by
    have allSymbols := symbols
    have value := congrArg (fun values : List (BitVec 32) => values[query.val]?) allSymbols
    simp only [List.getElem?_ofFn,query.isLt,dite_true] at value
    exact (Option.some.inj value).trans (Listing8TMGraph.mismatch_symbol machine _ Listing8TMWindow.back Listing8TMWindow.forward _ lastNode _ different query)
  intro observed
  exact Listing8TMFixedObservation.reconstruct mode (origin mode start)
    (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) machine.blank
    (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
      (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish) finalState.principal.memory finish cells
    (fun query outside => Listing8TMOutputWindow.terminal_outside_blank machine input finish count actual query outside) observed

end SmcTuring.Appendix.Listing9SameTraceBinding
