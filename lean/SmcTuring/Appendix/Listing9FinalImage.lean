module
public import SmcTuring.Appendix.Listing9PatchWindows

public section
namespace SmcTuring.Appendix.Listing9FinalImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- Actual Listing 9 prologue, complete initialized Listing 8 interpreter and
all three epilogue instructions in the same decoder/state. Only present entry
packet observations and static bounds are inputs; future epilogue bytes and
save/pointer values follow from execution. The endpoint is the epilogue code
boundary, before trailing storage declarations. Full emitted image construction,
whole-code ownership and physical exit remain separate obligations. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin)
    (epilogue : a.epilogue=Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (saveAfter : AccumulatorLayout.endPC mode a≤a.save)
    (pointerAfter : AccumulatorLayout.endPC mode a≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (prologue : ByteMemory.bytesAt (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a))
    (current : Listing8AccumulatorExit.Current mode a memory)
    (owner : Nat) (pointerField : a.pointer=StringInit.field mode owner)
    (ownerFits : owner+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (pointerDeclaration : ByteMemory.bytesAt memory owner (StringCodec.initialSize mode)=StringInit.bytes mode owner a.save) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) code finalState ∧
      finalState.principal.pc.toNat=AccumulatorLayout.endPC mode a ∧
      code.length=4+(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      finalState.principal.accumulator=seed.principal.accumulator ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, AccumulatorLayout.endPC mode a≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=
          ByteMemory.bytesAt (ByteMemory.putWord mode memory a.save (Arithmetic.encodeNat mode a.save)) observed size) := by
  have epiBefore : a.epilogue≤AccumulatorLayout.endPC mode a := by
    unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega
  have bodySave : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤a.save := by rw [←epilogue];omega
  have bodyPointer : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤a.pointer := by rw [←epilogue];omega
  obtain ⟨reached,body,bodyTrace,entry,bodyLength,nodes,rules,symbols,head,saved,pointer,stack,source,destination,forward,carry,frames⟩:=
    AccumulatorFinalization.body mode origin l t logical halted ctx a valid located epilogue bodySave bodyPointer memory seed prologue
  have pointerValue:=StringInit.initialized_pointer mode owner a.save memory ownerFits pointerDeclaration
  rw [←pointerField] at pointerValue
  have declared : Execution.load mode reached.principal.memory (Arithmetic.encodeNat mode a.pointer)=Arithmetic.encodeNat mode a.save := pointer.trans pointerValue
  have reachedCurrent : Listing8AccumulatorExit.Current mode a reached.principal.memory := by
    constructor
    · rw [frames a.epilogue (Native.encode mode (AccumulatorLayout.first mode a)).length (by rw [←epilogue]),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.1]
        unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC at saveAfter;omega))]
      exact current.first
    · rw [frames (AccumulatorLayout.secondPC mode a) (Native.encode mode (AccumulatorLayout.second mode a)).length (by rw [←epilogue];unfold AccumulatorLayout.secondPC;omega),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1]
        unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC at saveAfter;omega))]
      exact current.second
    · rw [frames (AccumulatorLayout.thirdPC mode a) (Native.encode mode (AccumulatorLayout.third mode a)).length (by rw [←epilogue];unfold AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega),StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.2];exact saveAfter))]
      exact current.third
  have exitTrace:=Listing8AccumulatorExit.trace mode a valid pointerAfter reached entry reachedCurrent
  have effect:=Listing8AccumulatorExit.effect mode a valid reached entry seed.principal.accumulator saved declared
  have counts:=Listing8LoopInterpreterTail.counts logical
  have outputFrame (observed size : Nat) (before : observed+size≤a.save) :
      ByteMemory.bytesAt (Listing8AccumulatorExit.finish mode a reached).principal.memory observed size=ByteMemory.bytesAt reached.principal.memory observed size := by
    rw [effect,StackWindows.word_window _ _ _ _ _ _ (Or.inr before)]
  have inputEnd : Listing8GraphLayout.input mode origin lastGraph.transitions+
      (Listing8NodeTable.bytes mode (Listing8GraphLayout.input mode origin lastGraph.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule))).length≤a.save := by
    rw [Listing8NodeTable.endpoint,Listing8NodeTable.endPC,Listing8GraphNodeImage.length]
    change Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes≤a.save
    rw [counts.1,counts.2];exact bodySave
  have tableEnd : Listing8FullTableImage.start mode origin+(Listing8TransitionTable.bytes mode (Listing8FullTableImage.start mode origin) (table mode origin g)).length≤a.save := by
    rw [Listing8TransitionTable.endpoint,Listing8TransitionTable.endPC,table_length]
    exact Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions)
      (Nat.le_trans (Listing8LoopTailGeometry.input_before_end mode origin g) bodySave)
  have nodesFinal:=nodes
  rw [Listing8NodeTable.Initial,←outputFrame _ _ inputEnd] at nodesFinal
  have rulesFinal:=rules
  rw [Listing8TransitionTable.Initial,←outputFrame _ _ tableEnd] at rulesFinal
  have symbolFrame (index : Fin lastGraph.nodes) : DwordCode.get (Listing8AccumulatorExit.finish mode a reached).principal.memory (nodePC mode origin lastGraph index+6)=DwordCode.get reached.principal.memory (nodePC mode origin lastGraph index+6) := by
    apply congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes))
      (outputFrame (nodePC mode origin lastGraph index+6) 4 (by
        have upper:=Listing8GraphLayout.node_upper mode origin lastGraph.transitions lastGraph.nodes index.val index.isLt
        have big : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
        change nodePC mode origin lastGraph index+Listing8Prototypes.nodeSpan mode≤_ at upper
        have ending:=bodySave;rw [←counts.1,←counts.2] at ending;omega))
  refine ⟨Listing8AccumulatorExit.finish mode a reached,body++Listing8AccumulatorExit.program mode a,
    StringStack.trace_append mode bodyTrace exitTrace,?_,?_,?_,nodesFinal,rulesFinal,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [effect,Arithmetic.encode_nat_toNat mode _ valid.epilogueFits]
  · rw [List.length_append,bodyLength,Listing8AccumulatorExit.program,AccumulatorLayout.program,List.length_map];simp only [List.length_cons,List.length_nil];omega
  · rw [effect]
  · exact (congrArg List.ofFn (funext symbolFrame)).trans symbols
  · exact (symbolFrame (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).trans head
  · rw [effect];exact stack
  · rw [effect];exact source
  · rw [effect];exact destination
  · rw [effect];exact forward
  · rw [effect];exact carry
  · intro observed size after
    rw [effect]
    have initial:=frames observed size (by rw [←epilogue];omega)
    have patched:=Listing9PatchWindows.patch_window reached.principal.memory (ByteMemory.putWord mode memory a.save seed.principal.accumulator)
      a.save (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode a.save)) observed size initial
    change ByteMemory.bytesAt (ByteMemory.putWord mode reached.principal.memory a.save (Arithmetic.encodeNat mode a.save)) observed size=
      ByteMemory.bytesAt (ByteMemory.putWord mode memory a.save (Arithmetic.encodeNat mode a.save)) observed size
    change ByteMemory.bytesAt (ByteMemory.putWord mode reached.principal.memory a.save (Arithmetic.encodeNat mode a.save)) observed size=
      ByteMemory.bytesAt (ByteMemory.putWord mode (ByteMemory.putWord mode memory a.save seed.principal.accumulator) a.save (Arithmetic.encodeNat mode a.save)) observed size at patched
    rw [Listing9PatchWindows.word_overwrite] at patched
    exact patched

end SmcTuring.Appendix.Listing9FinalImage
