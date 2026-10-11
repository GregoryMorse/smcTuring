module
public import SmcTuring.Appendix.Listing8AccumulatorEntry
public import SmcTuring.Appendix.Listing8OriginalInterpreterReadFrames
public import SmcTuring.Native.AccumulatorReadClasses
public import SmcTuring.Native.StackFieldWrites

public import SmcTuring.Appendix.Listing8OriginalInterpreterFetchFrames
public import SmcTuring.Native.StringFetchWiden
public import SmcTuring.Native.AccumulatorPC

public section
namespace SmcTuring.Native.AccumulatorBodyFetch
set_option maxHeartbeats 1000000
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run StringFetchWindows.Run
open Appendix.Listing8CopyImage Appendix.Listing8SourceGraph Appendix.Listing8GraphInputContext
abbrev BodyTargets:=Appendix.Listing8PointerCopies.Targets

/-- The actual Listing 9 entry store and the complete Listing 8 interpreter
body are composed from one present entry image. Logical-only steps produce
all future traces and classifier/fetch windows; later save/pointer values are derived from byte frames.
This closes the concrete body/save preservation obligations. Epilogue packet
construction, whole-program ownership and the physical exit remain separate. -/
theorem body (mode : Mode) (codeStart codeEnd origin : Nat) (l : Layout) (t : BodyTargets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Appendix.Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Appendix.Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (prologueInside : codeStart≤a.prologue)
    (bodyInside : Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤codeEnd)
    (saveInside : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode a.save))
    (located : AccumulatorLayout.savedPC mode a=origin)
    (epilogue : a.epilogue=Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (saveAfter : Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤a.save)
    (pointerAfter : Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (prologue : ByteMemory.bytesAt (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a)) :
    ∃ (reached : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) code reached ∧
      StringWrites.OwnedRun mode codeStart codeEnd code
        (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) ∧
      StringReadRuns.Run mode ⟨codeStart,codeEnd⟩ code
        (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) ∧
      StringFetchWindows.Run mode ⟨codeStart,codeEnd⟩ code
        (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) ∧
      reached.principal.pc=Arithmetic.encodeNat mode a.epilogue ∧
      code.length=1+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      Appendix.Listing8NodeTable.Initial mode (Appendix.Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Appendix.Listing8GraphNodeImage.declarations mode origin (Appendix.Listing8GraphStep.updated lastGraph lastNode lastRule)) reached.principal.memory ∧
      Appendix.Listing8TransitionTable.Initial mode (Appendix.Listing8FullTableImage.start mode origin) (table mode origin g) reached.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get reached.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Appendix.Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get reached.principal.memory (nodePC mode origin lastGraph (Appendix.Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Appendix.Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Appendix.Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      Execution.load mode reached.principal.memory (Arithmetic.encodeNat mode a.save)=seed.principal.accumulator ∧
      Execution.load mode reached.principal.memory (Arithmetic.encodeNat mode a.pointer)=Execution.load mode memory (Arithmetic.encodeNat mode a.pointer) ∧
      reached.principal.stack=seed.principal.stack ∧ reached.sourceIndex=seed.sourceIndex ∧ reached.destinationIndex=seed.destinationIndex ∧
      reached.backwards=false ∧ reached.principal.carry=false ∧
      (∀ observed size, Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed →
        ByteMemory.bytesAt reached.principal.memory observed size=ByteMemory.bytesAt (ByteMemory.putWord mode memory a.save seed.principal.accumulator) observed size) := by
  obtain ⟨reached,tail,actual,tailOwned,tailReads,tailFetch,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry,frames⟩:=
    Appendix.Listing8OriginalInterpreterFetchFrames.execute mode origin l t logical halted ctx
      (ByteMemory.putWord mode memory a.save seed.principal.accumulator) seed
  rw [←Appendix.Listing8AccumulatorEntry.saved_eq mode origin l t g node rule ctx a valid located saveAfter memory seed] at actual tailOwned tailReads tailFetch
  have leading:=Appendix.Listing8AccumulatorEntry.trace mode origin l t g node rule a valid memory seed prologue
  have counts:=Appendix.Listing8LoopInterpreterTail.counts logical
  have location : reached.principal.pc=Arithmetic.encodeNat mode a.epilogue := by
    rw [counts.1,counts.2,←epilogue] at endpoint
    simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) endpoint
  have saveFits : a.save<2^(8*mode.wordBytes) := by
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    have cap:=valid.saveFits;omega
  have pointerFits : a.pointer<2^(8*mode.wordBytes) := by
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    have cap:=valid.pointerFits;omega
  have saveBytes:=frames a.save mode.wordBytes saveAfter
  have saveWord:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) saveBytes
  change MixedMemory.getWord mode reached.principal.memory a.save=MixedMemory.getWord mode (ByteMemory.putWord mode memory a.save seed.principal.accumulator) a.save at saveWord
  rw [MixedMemory.get_put] at saveWord
  have pointerBytes:=frames a.pointer mode.wordBytes pointerAfter
  have pointerWord:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) pointerBytes
  change MixedMemory.getWord mode reached.principal.memory a.pointer=MixedMemory.getWord mode (ByteMemory.putWord mode memory a.save seed.principal.accumulator) a.pointer at pointerWord
  rw [MixedFrames.word_after_word mode memory a.save a.pointer seed.principal.accumulator valid.separate] at pointerWord
  refine ⟨reached,[StringStack.native mode (AccumulatorLayout.saveForm mode a)]++tail,
    StringStack.trace_append mode leading actual,?_,?_,?_,location,?_,nodes,rules,symbols,head,?_,?_,stack,source,destination,forward,carry,frames⟩
  · have lower : codeStart≤origin := by
      unfold AccumulatorLayout.savedPC at located
      omega
    have address := AccumulatorImage.save_address mode a valid
      (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed).principal rfl
    apply StackFieldWrites.owned_append mode codeStart codeEnd
      [StringStack.native mode (AccumulatorLayout.saveForm mode a)] tail
      (Appendix.Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed)
      (Appendix.Listing8AccumulatorEntry.saved mode origin l t g node rule a memory seed) leading
    · simp only [StringWrites.OwnedRun]
      constructor
      · apply StringWrites.native_code_write mode codeStart codeEnd (AccumulatorLayout.saveForm mode a)
        rw [address]
        exact saveInside
      · trivial
    · exact StringWriteRegions.owned_mono mode origin
        (Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes) codeStart codeEnd lower bodyInside tail _ tailOwned
  · have lower : codeStart≤origin := by
      unfold AccumulatorLayout.savedPC at located
      omega
    exact StringReadRuns.append_trace mode _ _ _ _ _ leading
      (AccumulatorReadClasses.prologue mode _ a _)
      (StringReadRuns.mono mode ⟨origin,Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
        ⟨codeStart,codeEnd⟩ lower bodyInside tail _ tailReads)
  · have lower : codeStart≤origin := by
      unfold AccumulatorLayout.savedPC at located
      omega
    have originEnd : origin≤Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes :=
      Nat.le_trans (Appendix.Listing9EarlyImage.input_after_origin mode origin g.transitions)
        (Appendix.Listing8LoopTailGeometry.input_before_end mode origin g)
    have prologueUpper : AccumulatorLayout.savedPC mode a≤codeEnd := by
      rw [located]
      exact Nat.le_trans originEnd bodyInside
    apply StringFetchWindows.append_trace mode _ _ _ _ _ leading
    · exact StringFetchWiden.run mode ⟨a.prologue,AccumulatorLayout.savedPC mode a⟩ ⟨codeStart,codeEnd⟩ _ _ prologueInside prologueUpper
        (StringFetchWindows.of_pc_run mode _ leading (AccumulatorPC.prologue_windows mode a valid _ rfl))
    · exact StringFetchWiden.run mode ⟨origin,Appendix.Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
        ⟨codeStart,codeEnd⟩ tail _ lower bodyInside tailFetch
  · rw [List.length_append,length,List.length_cons,List.length_nil];omega
  · rw [MixedMemory.load_nat mode _ _ saveFits];exact saveWord
  · rw [MixedMemory.load_nat mode _ _ pointerFits,MixedMemory.load_nat mode _ _ pointerFits];exact pointerWord

end SmcTuring.Native.AccumulatorBodyFetch
