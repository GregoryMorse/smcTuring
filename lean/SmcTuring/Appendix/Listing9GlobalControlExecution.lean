module
public import SmcTuring.Appendix.Listing9TailTemplateEpilogue
public import SmcTuring.Appendix.Listing9GlobalControlRegions
public import SmcTuring.Appendix.Listing8GlobalOriginalInterpreterTemplates

public section
namespace SmcTuring.Appendix.Listing9GlobalControlExecution
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- One actual full Listing 9 trace carries the global thirteen/eighteen
control descriptors and all six/twelve late executable templates at the same
reached prefixes. All future states and packets are positively constructed. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Listing8GraphInputContext.Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed) code finalState ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory)
        code (Listing9FullExecution.initial mode start l t g node rule memory seed) ∧
      finalState.principal.pc.toNat=endPC mode start g.transitions g.nodes ∧
      code.length=(if mode=.x86 then 6 else 12)+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
        (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
  have valid:=admissible mode start g.transitions g.nodes bounds
  have coords:=positions mode start g.transitions g.nodes
  have ordered:=bounds_order mode start g.transitions g.nodes
  obtain ⟨reached,body,bodyTrace,owned,endpoint,length,_,_,_,_,_,_,_,_,_,frames⟩:=
    Listing8OriginalInterpreterWriteFrames.execute mode (origin mode start) l t logical halted ctx
      (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
        (layout mode start g.transitions g.nodes).save seed.principal.accumulator) seed
  obtain ⟨globalEnd,globalBody,globalTrace,globalTemplates,globalProperty,_,globalLength⟩:=
    Listing8GlobalOriginalInterpreterTemplates.execute mode (origin mode start) l t logical halted ctx
      (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
        (layout mode start g.transitions g.nodes).save seed.principal.accumulator) seed
  have same:=StringStackTraceDeterminism.equal_length mode globalBody body _ globalEnd reached
    (globalLength.trans length.symm) globalTrace bodyTrace
  have bodyTemplates:=same.1 ▸ globalTemplates
  have bodyProperty:=same.2 ▸ globalProperty
  have savedEq:=Listing8AccumulatorEntry.saved_eq mode (origin mode start) l t g node rule ctx
    (layout mode start g.transitions g.nodes) valid coords.1 (by change epilogue mode start g.transitions g.nodes≤_;omega)
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
  rw [←savedEq] at bodyTrace owned bodyTemplates
  have leading:=Listing8AccumulatorEntry.trace mode (origin mode start) l t g node rule (layout mode start g.transitions g.nodes) valid
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  change StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed) _ _ at leading
  have leadingRegions:=Listing9TailTemplateRegions.prologue mode start g.transitions g.nodes bounds
    (Listing9FullExecution.initial mode start l t g node rule memory seed) rfl
  have leadingGlobalRegions:=Listing9GlobalControlRegions.prologue mode start g.transitions g.nodes bounds
    (Listing9FullExecution.initial mode start l t g node rule memory seed) rfl
  have initialGlobal:=Listing8GlobalControlTemplates.initial mode (origin mode start) _
    (Listing8GlobalInitialControl.current mode (origin mode start) l t g node rule ctx
      (Listing9Image.memory mode start g.transitions g.nodes memory) seed)
  have leadingTemplates:=Listing8GlobalControlTemplates.all_decodes mode (origin mode start) _
    (Listing9FullExecution.initial mode start l t g node rule memory seed) initialGlobal leadingGlobalRegions
  have bodyRegions:=Listing9TailTemplateRegions.body mode start g.transitions g.nodes body _ owned
  have prefixTrace:=StringStack.trace_append mode leading bodyTrace
  have prefixTemplates : StringTemplateStates.Run mode
      (fun state => Listing8GlobalControlTemplates.Decodes mode (origin mode start) state.principal.memory)
      ([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)
      (Listing9FullExecution.initial mode start l t g node rule memory seed) := by
    rw [StringTemplateStates.append,StringWrites.trace_run_eq mode leading]
    exact ⟨leadingTemplates,bodyTemplates⟩
  have prefixRegions : StringStoreRegions.Run mode (Listing9TailTemplateFields.Allowed mode start g.transitions g.nodes)
      ([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)
      (Listing9FullExecution.initial mode start l t g node rule memory seed) := by
    rw [StringStoreRegions.append,StringWrites.trace_run_eq mode leading]
    exact ⟨leadingRegions,bodyRegions⟩
  have initial:=Listing9TailTemplateInitial.original mode start l t g node rule ctx memory seed
  have prefixStates:=Listing9TailTemplates.all_states mode start g.transitions g.nodes _ _ initial prefixRegions
  have reachedProperty:=StringTemplateStates.at_prefix mode
    (fun state => Listing9TailTemplates.Property mode start g.transitions g.nodes state.principal.memory)
    ([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body) [] _
    (by simpa only [List.append_nil] using prefixStates)
  rw [StringWrites.trace_run_eq mode prefixTrace] at reachedProperty
  have counts:=Listing8LoopInterpreterTail.counts logical
  rw [counts.1,counts.2] at endpoint
  change reached.principal.pc.toNat=epilogue mode start g.transitions g.nodes at endpoint
  have entry : reached.principal.pc=Arithmetic.encodeNat mode (epilogue mode start g.transitions g.nodes) := by
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) endpoint
  have pointerFits : (layout mode start g.transitions g.nodes).pointer<2^(8*mode.wordBytes) := by
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    have cap:=valid.pointerFits
    omega
  have pointerBytes:=frames (layout mode start g.transitions g.nodes).pointer mode.wordBytes (by
    change epilogue mode start g.transitions g.nodes≤_;omega)
  have pointerWord:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) pointerBytes
  change MixedMemory.getWord mode reached.principal.memory (layout mode start g.transitions g.nodes).pointer=
    MixedMemory.getWord mode (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
      (layout mode start g.transitions g.nodes).save seed.principal.accumulator) (layout mode start g.transitions g.nodes).pointer at pointerWord
  rw [MixedFrames.word_after_word mode _ _ _ _ valid.separate] at pointerWord
  have declaredPointer:=(Listing9Image.initial_values mode start g.transitions g.nodes bounds memory).2
  rw [MixedMemory.load_nat mode _ _ pointerFits] at declaredPointer
  have pointer : Execution.load mode reached.principal.memory (Arithmetic.encodeNat mode (layout mode start g.transitions g.nodes).pointer)=
      Arithmetic.encodeNat mode (layout mode start g.transitions g.nodes).save := by
    rw [MixedMemory.load_nat mode _ _ pointerFits]
    exact pointerWord.trans declaredPointer
  have exitTrace:=Listing8AccumulatorExit.trace mode _ valid (by rw [coords.2.2.1];omega) reached entry
    (Listing9TailTemplateEpilogue.packets mode start g.transitions g.nodes _ reachedProperty)
  have exitRegions:=Listing9TailTemplateRegions.epilogue mode start g.transitions g.nodes bounds reached entry
  have exitGlobalRegions:=Listing9GlobalControlRegions.epilogue mode start g.transitions g.nodes bounds reached entry
  have exitTemplates:=Listing8GlobalControlTemplates.all_decodes mode (origin mode start) _ reached bodyProperty exitGlobalRegions
  have exitProperty:=Listing8GlobalControlProperties.after_trace mode (origin mode start) _ _ _ bodyProperty exitGlobalRegions exitTrace
  have tailCurrent:=Listing9TailTemplateEpilogue.storage_current mode start g.transitions g.nodes bounds reached entry reachedProperty pointer
  have tailEntry : (Listing8AccumulatorExit.finish mode (layout mode start g.transitions g.nodes) reached).principal.pc=
      Arithmetic.encodeNat mode (saveOwner mode start g.transitions g.nodes) := by
    change (AccumulatorEffects.finish mode _ reached.principal).pc=_
    rw [AccumulatorEffects.effect mode _ valid reached.principal entry,coords.2.2.1]
  have tailTrace:=Listing9Storage.trace mode start g.transitions g.nodes bounds _ tailEntry tailCurrent
  have tailRegions:=Listing9TailTemplateRegions.storage mode start g.transitions g.nodes bounds _ tailEntry tailCurrent
  have tailGlobalRegions:=Listing9GlobalControlRegions.storage mode start g.transitions g.nodes bounds _ tailEntry tailCurrent
  have tailTemplates:=Listing8GlobalControlTemplates.all_decodes mode (origin mode start) _ _ exitProperty tailGlobalRegions
  have wholeTrace:=StringStack.trace_append mode (StringStack.trace_append mode prefixTrace exitTrace) tailTrace
  have wholeRegions : StringStoreRegions.Run mode (Listing9TailTemplateFields.Allowed mode start g.transitions g.nodes)
      (([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++
        Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes)
      (Listing9FullExecution.initial mode start l t g node rule memory seed) := by
    rw [StringStoreRegions.append,StringStoreRegions.append,StringWrites.trace_run_eq mode prefixTrace,
      StringWrites.trace_run_eq mode (StringStack.trace_append mode prefixTrace exitTrace)]
    exact ⟨⟨prefixRegions,exitRegions⟩,tailRegions⟩
  have wholeTemplates : StringTemplateStates.Run mode
      (fun state => Listing8GlobalControlTemplates.Decodes mode (origin mode start) state.principal.memory)
      (([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++
        Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes)
      (Listing9FullExecution.initial mode start l t g node rule memory seed) := by
    rw [StringTemplateStates.append,StringTemplateStates.append,StringWrites.trace_run_eq mode prefixTrace,
      StringWrites.trace_run_eq mode (StringStack.trace_append mode prefixTrace exitTrace)]
    exact ⟨⟨prefixTemplates,exitTemplates⟩,tailTemplates⟩
  refine ⟨_,_,wholeTrace,JointTemplateStates.join mode _ _ _ _ wholeTemplates (Listing9TailTemplates.all_decodes mode start g.transitions g.nodes _ _ initial wholeRegions),?_,?_⟩
  · rw [Listing9Storage.effect mode start g.transitions g.nodes bounds _ tailEntry tailCurrent,
      Arithmetic.encode_nat_toNat mode _ bounds.capacity]
  · rw [List.length_append,List.length_append,List.length_append,List.length_cons,List.length_nil,length,
      Listing8AccumulatorExit.program,List.length_map,AccumulatorLayout.program,Listing9Storage.instruction_count]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,List.length_cons,List.length_nil] <;> omega

end SmcTuring.Appendix.Listing9GlobalControlExecution
