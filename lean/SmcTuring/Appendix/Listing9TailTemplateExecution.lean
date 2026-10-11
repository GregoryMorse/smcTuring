module
public import SmcTuring.Appendix.Listing9TailTemplateEpilogue

public section
namespace SmcTuring.Appendix.Listing9TailTemplateExecution
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The full original emitted execution carries all six/twelve Listing 9
instruction/declaration templates jointly at every reached prefix. The body
store policy, native states, epilogue packets and both later declarations are
constructed from logical steps and the original image, never supplied. -/
theorem execute (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Listing8GraphInputContext.Context mode (origin mode start) l t g node rule)
    (bounds : Bounds mode start g.transitions g.nodes) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed) code finalState ∧
      StringTemplateStates.Run mode (fun reached => Listing9TailTemplates.Decodes mode start g.transitions g.nodes reached.principal.memory)
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
  have savedEq:=Listing8AccumulatorEntry.saved_eq mode (origin mode start) l t g node rule ctx
    (layout mode start g.transitions g.nodes) valid coords.1 (by change epilogue mode start g.transitions g.nodes≤_;omega)
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
  rw [←savedEq] at bodyTrace owned
  have leading:=Listing8AccumulatorEntry.trace mode (origin mode start) l t g node rule (layout mode start g.transitions g.nodes) valid
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  change StringStack.Trace mode (Listing9FullExecution.initial mode start l t g node rule memory seed) _ _ at leading
  have leadingRegions:=Listing9TailTemplateRegions.prologue mode start g.transitions g.nodes bounds
    (Listing9FullExecution.initial mode start l t g node rule memory seed) rfl
  have bodyRegions:=Listing9TailTemplateRegions.body mode start g.transitions g.nodes body _ owned
  have prefixTrace:=StringStack.trace_append mode leading bodyTrace
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
  have tailCurrent:=Listing9TailTemplateEpilogue.storage_current mode start g.transitions g.nodes bounds reached entry reachedProperty pointer
  have tailEntry : (Listing8AccumulatorExit.finish mode (layout mode start g.transitions g.nodes) reached).principal.pc=
      Arithmetic.encodeNat mode (saveOwner mode start g.transitions g.nodes) := by
    change (AccumulatorEffects.finish mode _ reached.principal).pc=_
    rw [AccumulatorEffects.effect mode _ valid reached.principal entry,coords.2.2.1]
  have tailTrace:=Listing9Storage.trace mode start g.transitions g.nodes bounds _ tailEntry tailCurrent
  have tailRegions:=Listing9TailTemplateRegions.storage mode start g.transitions g.nodes bounds _ tailEntry tailCurrent
  have wholeTrace:=StringStack.trace_append mode (StringStack.trace_append mode prefixTrace exitTrace) tailTrace
  have wholeRegions : StringStoreRegions.Run mode (Listing9TailTemplateFields.Allowed mode start g.transitions g.nodes)
      (([StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start g.transitions g.nodes))]++body)++
        Listing8AccumulatorExit.program mode (layout mode start g.transitions g.nodes)++Listing9Storage.program mode start g.transitions g.nodes)
      (Listing9FullExecution.initial mode start l t g node rule memory seed) := by
    rw [StringStoreRegions.append,StringStoreRegions.append,StringWrites.trace_run_eq mode prefixTrace,
      StringWrites.trace_run_eq mode (StringStack.trace_append mode prefixTrace exitTrace)]
    exact ⟨⟨prefixRegions,exitRegions⟩,tailRegions⟩
  refine ⟨_,_,wholeTrace,Listing9TailTemplates.all_decodes mode start g.transitions g.nodes _ _ initial wholeRegions,?_,?_⟩
  · rw [Listing9Storage.effect mode start g.transitions g.nodes bounds _ tailEntry tailCurrent,
      Arithmetic.encode_nat_toNat mode _ bounds.capacity]
  · rw [List.length_append,List.length_append,List.length_append,List.length_cons,List.length_nil,length,
      Listing8AccumulatorExit.program,List.length_map,AccumulatorLayout.program,Listing9Storage.instruction_count]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,List.length_cons,List.length_nil] <;> omega

end SmcTuring.Appendix.Listing9TailTemplateExecution
