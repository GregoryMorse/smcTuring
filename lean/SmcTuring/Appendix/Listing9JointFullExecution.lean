module
public import SmcTuring.Appendix.Listing8JointInterpreter
public import SmcTuring.Appendix.Listing9GlobalControlExecution
public import SmcTuring.Appendix.Listing9FullExecution

public section
namespace SmcTuring.Appendix.Listing9JointFullExecution
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000

/-- A transport helper identifies the fully restored terminal catalog at the
endpoint of an independently constructed body trace. Core execution below
constructs that trace;no future image is assumed. -/
theorem final_catalog (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed finalState : StringExecution.State mode) (body : List (StringStack.Form mode))
    (actual : StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) body finalState)
    (length : body.length=(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
      (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes) :
    ∃ (lastL : Layout),Context mode origin lastL t lastGraph lastNode lastRule ∧
      Listing8JointAccumulatorCatalog.Property mode origin lastL (values mode origin lastGraph lastNode lastRule)
        lastGraph finalState.principal.memory := by
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx memory seed
  obtain ⟨lastL,lastOld,lastState,passes,lastCtx,lastImage,all,prefixTrace,prefixLength⟩ :=
    Listing8JointIteration.execute mode origin t logical l Listing8OriginalControlImage.old _ ctx image
  have boot : StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) :=
    Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have ending := Listing8LoopTerminal.trace mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have total := StringStack.trace_append mode boot (StringStack.trace_append mode prefixTrace ending)
  have same := StringStackTraceDeterminism.equal_length mode _ body _ _ finalState (by
    rw [List.length_append,List.length_append,Listing4EntryLayout.instruction_count,prefixLength,
      Listing8LoopTerminal.instruction_count,length];omega) total actual
  refine ⟨lastL,lastCtx,?_⟩
  rw [←same.2]
  exact Listing8JointAccumulatorCatalog.terminal_seed mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted

/-- Initial epilogue packets are transported through positive body exterior
frames and the exact disjoint accumulator save. -/
theorem epilogue_packets (mode : Mode) (a : AccumulatorLayout.Layout)
    (saveAfter : AccumulatorLayout.endPC mode a≤a.save)
    (memory : ByteMemory.Memory) (saved : Word mode) (reached : ByteMemory.Memory)
    (frames : ∀ observed size,a.epilogue≤observed → ByteMemory.bytesAt reached observed size=
      ByteMemory.bytesAt (ByteMemory.putWord mode memory a.save saved) observed size)
    (initial : Listing8AccumulatorExit.Current mode a memory) : Listing8AccumulatorExit.Current mode a reached := by
  constructor
  · rw [frames a.epilogue _ (by rfl),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
      rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.1]
      unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC at saveAfter;omega))]
    exact initial.first
  · rw [frames (AccumulatorLayout.secondPC mode a) _ (by unfold AccumulatorLayout.secondPC;omega),
      StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1]
        unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC at saveAfter;omega))]
    exact initial.second
  · rw [frames (AccumulatorLayout.thirdPC mode a) _ (by unfold AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega),
      StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.2];exact saveAfter))]
    exact initial.third

@[expose] def Prefix (mode : Mode) (start : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (lastGraph : Graph) (lastNode : Fin lastGraph.nodes) (lastRule : Fin lastGraph.transitions)
    (body before : List (StringStack.Form mode)) (reached : StringExecution.State mode) :=
  (∃ rest,[StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]=before++rest ∧
    Listing8JointAccumulatorCatalog.BeforeProperty mode (origin mode start) l g reached.principal.memory) ∨
  (∃ part rest,body=part++rest ∧
    before=[StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++part ∧
    ∃ bodyForms,body=Listing4EntryLayout.forms mode (origin mode start)++bodyForms ∧
      Listing8JointInterpreter.OriginalPrefix mode (origin mode start) l t g node rule
        (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes backing)
          (layout mode start g.transitions g.nodes).save seed.principal.accumulator) seed
        lastGraph lastNode lastRule bodyForms part reached) ∨
  (∃ (lastL : Layout) (part rest : List (StringStack.Form mode)),
    Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes=part++rest ∧
    before=([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++part ∧
    Listing8JointAccumulatorCatalog.Property mode (origin mode start) lastL (values mode (origin mode start) lastGraph lastNode lastRule)
      lastGraph reached.principal.memory)

/-- ONE fetched full Listing9 trace carries both the already proved global/
late descriptors and the full lifetime-aware original/main/terminal/late joint
catalogs at EVERY SAME passes. All later states,packets and catalogs are outputs. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (body : List (StringStack.Form mode)),
      let code := ([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++
        (Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes)
      StringStack.Trace mode (Listing9ExecutionImage.initial mode start l t g node rule memory seed) code finalState ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      code.length=(if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
        (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory) code
        (Listing9ExecutionImage.initial mode start l t g node rule memory seed) ∧
      ∀ before after,code=before++after → Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body before
        (StringWrites.run mode before (Listing9ExecutionImage.initial mode start l t g node rule memory seed)) := by
  let a := layout mode start g.transitions g.nodes
  let original := Listing9Image.memory mode start g.transitions g.nodes memory
  let saved := ByteMemory.putWord mode original a.save seed.principal.accumulator
  let saving := [StringStack.native mode (AccumulatorLayout.saveForm mode a)]
  have valid := admissible mode start g.transitions g.nodes bounds
  have coords := positions mode start g.transitions g.nodes
  have ordered := bounds_order mode start g.transitions g.nodes
  have counts := Listing8LoopInterpreterTail.counts logical
  have located : a.epilogue=Listing8JointAccumulatorCatalog.graphEnd mode (origin mode start) lastGraph := by
    rw [Listing8JointAccumulatorCatalog.graphEnd,counts.1,counts.2];rfl
  have saveAfter : AccumulatorLayout.endPC mode a≤a.save := by rw [coords.2.2.1];exact ordered.2.2.1
  have pointerAfter : AccumulatorLayout.endPC mode a≤a.pointer := by
    rw [coords.2.2.1];change saveOwner mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).pointer;omega
  have graphSave : Listing8JointAccumulatorCatalog.graphEnd mode (origin mode start) lastGraph≤a.save := by
    rw [←located];change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).save;omega
  have graphPointer : Listing8JointAccumulatorCatalog.graphEnd mode (origin mode start) lastGraph≤a.pointer := by
    rw [←located];change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).pointer;omega
  obtain ⟨bodyEnd,bodyForms,bodyTrace,bodyPC,bodyLength,bodyPrefixes⟩ :=
    Listing8JointInterpreter.original mode (origin mode start) l t logical halted ctx a valid located graphSave graphPointer saved seed
  let body := Listing4EntryLayout.forms mode (origin mode start)++bodyForms
  have length : body.length=(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
      (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
    rw [List.length_append,Listing4EntryLayout.instruction_count,bodyLength]
    omega
  obtain ⟨lastL,lastCtx,terminalCatalog⟩ := final_catalog mode (origin mode start) l t logical halted ctx saved seed bodyEnd body bodyTrace length
  obtain ⟨framed,frameCode,frameTrace,_,_,frameLength,_,_,_,_,_,_,_,_,_,frames⟩ :=
    Listing8OriginalInterpreterWriteFrames.execute mode (origin mode start) l t logical halted ctx saved seed
  have sameBody := StringStackTraceDeterminism.equal_length mode body frameCode _ bodyEnd framed (length.trans frameLength.symm) bodyTrace frameTrace
  have packets := epilogue_packets mode a saveAfter original seed.principal.accumulator bodyEnd.principal.memory
    (by intro observed size after;rw [sameBody.2];exact frames observed size after) (Listing9Image.epilogue_current mode start g.transitions g.nodes memory)
  have entry : bodyEnd.principal.pc=Arithmetic.encodeNat mode a.epilogue := by
    have pc : bodyEnd.principal.pc.toNat=a.epilogue := by exact bodyPC.trans located.symm
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) pc
  have ending := Listing8AccumulatorExit.trace mode a valid pointerAfter bodyEnd entry packets
  have epiRun := Listing8JointAccumulatorCatalog.epilogue mode (origin mode start) lastL t lastGraph lastNode lastRule lastCtx a valid bodyEnd entry terminalCatalog graphSave graphPointer
  have prologue := Listing8AccumulatorEntry.trace mode (origin mode start) l t g node rule a valid original seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  rw [Listing8AccumulatorEntry.saved_eq mode (origin mode start) l t g node rule ctx a valid coords.1
    (by change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).save;omega) original seed] at prologue
  have prefixTrace := StringStack.trace_append mode (StringStack.trace_append mode prologue bodyTrace) ending
  obtain ⟨restored,oldCode,oldTrace,oldPC,oldLength,_,_,_,_,_,_,_,_,_,_,retained⟩ :=
    Listing9ExecutionImage.execute mode start l t logical halted ctx bounds memory seed
  have sameRestored := StringStackTraceDeterminism.equal_length mode _ oldCode _ _ restored (by
    rw [List.length_append,List.length_append,List.length_cons,List.length_nil,length,
      Listing8AccumulatorExit.program,List.length_map,AccumulatorLayout.program]
    simp only [List.length_cons,List.length_nil];omega) prefixTrace oldTrace
  have storageCurrent := Listing9Storage.current_of_retained mode start g.transitions g.nodes memory restored.principal.memory retained
  have storageEntry : restored.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start g.transitions g.nodes) := by
    rw [coords.2.2.1] at oldPC
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) oldPC
  have storageTrace := Listing9Storage.trace mode start g.transitions g.nodes bounds restored storageEntry storageCurrent
  have epiEnd := StringTemplateStates.at_prefix mode _ (Listing8AccumulatorExit.program mode a) [] bodyEnd
    (by simpa only [List.append_nil] using epiRun)
  rw [StringWrites.trace_run_eq mode ending,sameRestored.2] at epiEnd
  have storageRegions := BoundedStoreRegions.interval mode
    (fun address _ => Listing8JointAccumulatorCatalog.graphEnd mode (origin mode start) lastGraph≤address)
    (saveOwner mode start g.transitions g.nodes) (endPC mode start g.transitions g.nodes) _ restored
    (fun address _ lower _ => (by rw [←located];change epilogue mode start g.transitions g.nodes≤_;omega))
    (Listing9StorageWrites.owned mode start g.transitions g.nodes bounds restored storageEntry storageCurrent)
  have storageRun := StringStoreTemplateRuns.preserve mode _ _ _ restored epiEnd
    (Listing8JointAccumulatorCatalog.store mode (origin mode start) lastL t lastGraph lastNode lastRule lastCtx) storageRegions
  have lateRun : StringTemplateStates.Run mode
      (fun reached => Listing8JointAccumulatorCatalog.Property mode (origin mode start) lastL
        (values mode (origin mode start) lastGraph lastNode lastRule) lastGraph reached.principal.memory)
      (Listing8AccumulatorExit.program mode a++Listing9Storage.program mode start g.transitions g.nodes) bodyEnd := by
    rw [StringTemplateStates.append,StringWrites.trace_run_eq mode ending,sameRestored.2]
    exact ⟨epiRun,storageRun⟩
  have whole := StringStack.trace_append mode (sameRestored.2 ▸ prefixTrace) storageTrace
  have wholeLength : ((saving++body)++(Listing8AccumulatorExit.program mode a++Listing9Storage.program mode start g.transitions g.nodes)).length=
      (if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
        (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
    simp only [saving,body,List.length_append,List.length_cons,List.length_nil,
      Listing4EntryLayout.instruction_count,bodyLength,Listing8AccumulatorExit.program,List.length_map,
      AccumulatorLayout.program,Listing9Storage.instruction_count]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  rw [List.append_assoc] at whole
  obtain ⟨globalEnd,globalCode,globalTrace,globalCatalogs,globalPC,globalLength⟩ :=
    Listing9GlobalControlExecution.execute mode start l t logical halted ctx bounds memory seed
  have sameWhole := StringStackTraceDeterminism.equal_length mode _ globalCode _ _ globalEnd (wholeLength.trans globalLength.symm) whole globalTrace
  have prologueRun := Listing8JointAccumulatorCatalog.prologue mode (origin mode start) l t g node rule ctx a valid
    (by change epilogue mode start g.transitions g.nodes≤(layout mode start g.transitions g.nodes).save;omega) original seed
  have savedRun := StringWrites.trace_run_eq mode prologue
  change StringWrites.run mode saving (Listing9ExecutionImage.initial mode start l t g node rule memory seed)=
    Listing8GraphBackedge.initial mode (origin mode start) l t g node rule saved seed at savedRun
  change StringTemplateStates.Run mode (fun reached => Listing8JointAccumulatorCatalog.BeforeProperty mode (origin mode start) l g reached.principal.memory) saving
    (Listing9ExecutionImage.initial mode start l t g node rule memory seed) at prologueRun
  have bodyRun := StringWrites.trace_run_eq mode bodyTrace
  change StringWrites.run mode body (Listing8GraphBackedge.initial mode (origin mode start) l t g node rule saved seed)=bodyEnd at bodyRun
  refine ⟨_,body,whole,?_,wholeLength,?_,?_⟩
  · rw [sameWhole.2];exact globalPC
  · rw [sameWhole.1];exact globalCatalogs
  · intro before after cut
    rcases Listing8BoundarySummary.cut_append (saving++body) _ before after cut with
      ⟨rest,split⟩ | ⟨part,rest,split,location⟩
    · rcases Listing8BoundarySummary.cut_append saving body before rest split with
        ⟨last,short⟩ | ⟨part,last,short,location⟩
      · exact Or.inl ⟨last,short,StringTemplateStates.at_prefix mode _ before last _ (short ▸ prologueRun)⟩
      · refine Or.inr (Or.inl ⟨part,last,short,location,bodyForms,rfl,?_⟩)
        rw [location,StringWrites.run_append,savedRun]
        exact bodyPrefixes part last short
    · refine Or.inr (Or.inr ⟨lastL,part,rest,split,location,?_⟩)
      rw [location,StringWrites.run_append,StringWrites.run_append,savedRun,bodyRun]
      exact StringTemplateStates.at_prefix mode _ part rest bodyEnd (split ▸ lateRun)

/-- The complete bounded native certificate;all phase witnesses describe
one actual fetch/execute trace and its SAME reached prefixes. -/
@[expose] def Certificate (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (lastGraph : Graph) (lastNode : Fin lastGraph.nodes) (lastRule : Fin lastGraph.transitions)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) : Prop :=
    ∃ (finalState : StringExecution.State mode) (body : List (StringStack.Form mode)),
      let code := ([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++
        (Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes)
      StringStack.Trace mode (Listing9ExecutionImage.initial mode start l t g node rule memory seed) code finalState ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory) code
        (Listing9ExecutionImage.initial mode start l t g node rule memory seed) ∧
      ∀ before after,code=before++after → Prefix mode start l t g node rule memory seed lastGraph lastNode lastRule body before
        (StringWrites.run mode before (Listing9ExecutionImage.initial mode start l t g node rule memory seed))

/-- Original finite input and actual source halting construct the full joint
Listing9 certificate. Numeric hardware capacity/reach remain explicit;the
unbounded mathematical universality theorem is stated separately. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ lastNode : Fin (Listing8TMRun.width (count+input.length)),
      Listing8TMWindow.position (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) lastNode=finish.head ∧
      Certificate mode start
        (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing9TMStaticExecution.bodyTargets mode start)
        (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state)
        (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish)
        lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) memory seed := by
  obtain ⟨iterations,lastNode,bounded,head,logical,declaredHalt,unchanged⟩ :=
    Listing8TMObservedRun.finite_halt machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted
  have bounds := Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) capacityBytes reach
  have ctx := Listing9PackedCapacity.context mode start
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) bounds
  obtain ⟨finalState,body,trace,endpoint,length,catalogs,prefixes⟩ := execute mode start _ _ logical declaredHalt ctx bounds memory seed
  exact ⟨lastNode,head,finalState,body,trace,endpoint,catalogs,prefixes⟩

end SmcTuring.Appendix.Listing9JointFullExecution
